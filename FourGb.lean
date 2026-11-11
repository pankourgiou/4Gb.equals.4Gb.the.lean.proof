/-!
A 4 Gb file is a 4 Gb file. Core Lean 4 only, decorated with attributes.
Sizes are in bits so that Gb (gigabit) and GB (gigabyte) can be told apart.
-/

namespace FileSize

/-- A file size, counted in bits. -/
@[ext] structure Size where
  bits : Nat
deriving DecidableEq, Repr

/-- Bits per byte. -/
@[reducible, inline] def byteBits : Nat := 8

/-- One gigabit (SI): 10^9 bits. -/
@[reducible, inline] def Gb (n : Nat) : Size := ⟨n * 1000000000⟩

/-- One gigabyte (SI): 10^9 bytes. -/
@[reducible, inline] def GB (n : Nat) : Size := ⟨n * 1000000000 * byteBits⟩

/-- One gibibyte: 2^30 bytes. -/
@[reducible, inline] def GiB (n : Nat) : Size := ⟨n * 1073741824 * byteBits⟩

/-- A file is just a name plus a size. -/
structure File where
  name : String
  size : Size
deriving DecidableEq, Repr

/-- "f is an n Gb file". -/
@[reducible] def IsGbFile (f : File) (n : Nat) : Prop := f.size = Gb n

/-- Our test subject. -/
def movie : File := ⟨"movie.mkv", Gb 4⟩

/-! ## The main theorem -/

/-- A 4 Gb file is indeed a 4 Gb file. -/
@[simp] theorem movie_is_4Gb : IsGbFile movie 4 := rfl

/-- Same fact, with the arithmetic spelled out: 4 Gb = 4,000,000,000 bits. -/
theorem movie_bits : movie.size.bits = 4000000000 := by decide

/-- ...which is exactly 500,000,000 bytes. -/
theorem movie_bytes : movie.size.bits / byteBits = 500000000 := by decide

/-- Every n Gb file is an n Gb file (the general statement). -/
@[simp] theorem gb_refl (n : Nat) : IsGbFile ⟨"any", Gb n⟩ n := rfl

/-! ## Sanity checks: the units really are different -/

/-- 4 Gb is NOT 4 GB (gigabit vs gigabyte, factor 8). -/
theorem Gb_ne_GB : Gb 4 ≠ GB 4 := by decide

/-- 4 GB is NOT 4 GiB. -/
theorem GB_ne_GiB : GB 4 ≠ GiB 4 := by decide

/-- 4 GB is exactly 8 times 4 Gb. -/
theorem GB_eq_8_Gb : (GB 4).bits = 8 * (Gb 4).bits := by decide

/-- Uniqueness: a 4 Gb file cannot also be an m Gb file for m ≠ 4. -/
theorem unique_size (f : File) (m : Nat) (h4 : IsGbFile f 4) (hm : IsGbFile f m) :
    m = 4 := by
  unfold IsGbFile Gb at h4 hm
  have := congrArg Size.bits (hm.symm.trans h4)
  simp at this
  omega

end FileSize
