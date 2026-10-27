module

public import CFSG.Monster.Code.Weights
public import CFSG.Monster.CodeLattice

public section

namespace CFSG.Monster.Code

open CFSG.Monster

theorem allOnes_eq_Ω : allOnes = Ω := rfl

theorem allOnes_mem_C : allOnes ∈ C := Ω_mem_C

theorem bitLift_eq_val (t : ZMod 2) : bitLift t = t.val := rfl

theorem weight_eq_hammingNorm (d : Fin 24 → ZMod 2) : weight d = hammingNorm d := by
  rw [weight, hammingNorm_eq_sum_val]
  push_cast
  rfl

theorem weight_mod_four {d : Fin 24 → ZMod 2} (hd : d ∈ C) : weight d % 4 = 0 := by
  rw [weight_eq_hammingNorm]
  obtain ⟨k, hk⟩ := four_dvd_wt hd
  rw [hk]
  push_cast
  omega

@[expose] def mogLattice : AddSubgroup (Fin 24 → ℤ) := codeLatticeSubgroup allOnes_mem_C

theorem mem_mogLattice {u : Fin 24 → ℤ} : u ∈ mogLattice ↔ u ∈ codeLattice C := Iff.rfl

@[expose] def normSq (u : Fin 24 → ℤ) : ℤ := ∑ i, u i * u i

theorem codeForm_self (u : Fin 24 → ℤ) :
    codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = (normSq u : ℚ) / 8 := by
  unfold codeForm normSq
  push_cast
  rfl

theorem codeForm_self_eq_four_iff (u : Fin 24 → ℤ) :
    codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 4 ↔ normSq u = 32 := by
  rw [codeForm_self]
  constructor
  · intro h
    have : (normSq u : ℚ) = 32 := by linarith
    exact_mod_cast this
  · intro h
    rw [h]
    norm_num

@[expose] def eℤ (i : Fin 24) : Fin 24 → ℤ := Pi.single i 1

@[expose] def liftℤ (d : Fin 24 → ZMod 2) : Fin 24 → ℤ := fun i => bitLift (d i)

theorem sum_liftℤ (d : Fin 24 → ZMod 2) : ∑ i, liftℤ d i = hammingNorm d := by
  rw [← weight_eq_hammingNorm]
  rfl

theorem sum_bitLift (d : Fin 24 → ZMod 2) : ∑ i, bitLift (d i) = hammingNorm d := sum_liftℤ d

theorem bitLift_cast (t : ZMod 2) : ((bitLift t : ℤ) : ZMod 2) = t := by
  rw [bitLift, Int.cast_natCast, ZMod.natCast_zmod_val]

end CFSG.Monster.Code
