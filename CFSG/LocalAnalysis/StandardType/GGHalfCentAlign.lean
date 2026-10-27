module

public import CFSG.LocalAnalysis.StandardType.GGHalfCentFrame

public section

namespace CFSG.StandardType.GGHalf

open CFSG.StandardType CFSG.StandardType.CoordSL Matrix

private def centAlignEta3 (a : ZMod 3) : (ZMod 3)ˣ := if a = 2 then -1 else 1

private lemma centAlignEta3_mul_val (a : ZMod 3) :
    (((centAlignEta3 a : ZMod 3) * a).val = 0 ∨ ((centAlignEta3 a : ZMod 3) * a).val = 1) := by
  fin_cases a <;> decide

private lemma centAlignEta3_mul_val_eq_zero (a : ZMod 3) :
    ((centAlignEta3 a : ZMod 3) * a).val = 0 ↔ a = 0 := by
  rw [ZMod.val_eq_zero, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (centAlignEta3 a).ne_zero
    · exact h
  · exact Or.inr

theorem exists_conj_nsSL_binary {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ) :
    ∃ (M : SpecialLinearGroup (Fin (n + 1)) F2) (k' : Fin s → ℕ),
      M⁻¹ * SLNS.nsSL ε det_rootMat_phi3 k * M = SLNS.nsSL ε det_rootMat_phi3 k' ∧
      ∀ i, (k' i = 0 ∨ k' i = 1) ∧ (k' i = 0 ↔ k i % 3 = 0) := by
  classical
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  let t : Fin s → ZMod 3 := fun i => (k i : ZMod 3)
  let η : Fin s → (ZMod 3)ˣ := fun i => centAlignEta3 (t i)
  have hη : ∀ i, η i ∈ galExp phi3 root_phi3_pow_three := fun i => galExp_phi3 (η i)
  obtain ⟨M, hM⟩ := exists_conj_frameHom phi3
    (MonoidHom.id (SpecialLinearGroup (Fin (n + 1)) F2)) 1 ε det_rootMat_phi3
    rootMat_phi3_pow_three root_phi3_pow_three (Equiv.refl _) η hη
  have h := hM t
  simp only [CoordSL.frameHom_apply, SLRep.ggFrame_apply, Equiv.refl_apply, MonoidHom.id_apply,
    one_mul, inv_one, mul_one] at h
  have hL : SLNS.nsSL ε det_rootMat_phi3 (fun i => (t i).val) =
      SLNS.nsSL ε det_rootMat_phi3 k :=
    SLNS.nsSL_congr ε det_rootMat_phi3 rootMat_phi3_pow_three (fun i => by
      show (t i).val % 3 = k i % 3
      rw [show t i = (k i : ZMod 3) from rfl, ZMod.val_natCast]
      exact Nat.mod_mod _ _)
  rw [hL] at h
  refine ⟨M, fun i => ((η i : ZMod 3) * t i).val, h, fun i => ⟨?_, ?_⟩⟩
  · exact centAlignEta3_mul_val (t i)
  · rw [centAlignEta3_mul_val_eq_zero]
    show t i = 0 ↔ k i % 3 = 0
    rw [show t i = (k i : ZMod 3) from rfl, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

end CFSG.StandardType.GGHalf

end
