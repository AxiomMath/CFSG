module

public import CFSG.RankThree.GF2n.Parrott.SpinKernelChecks
public import CFSG.RankThree.GF2n.Parrott.SpinActionA

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups
open scoped Matrix


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "P45" => Equiv.Perm (Fin 45)

private theorem eq_top_of_gens (K : Subgroup A45) (hx : (⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) ∈ K)
    (hy : (⟨y45, Q45_le_A45 y45_mem_Q⟩ : A45) ∈ K) (hf : (⟨f45, f45_mem_A⟩ : A45) ∈ K) :
    K = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hle : Subgroup.closure ({x45, y45, f45} : Set P45) ≤
      K.map (QA45.originalSubgroup).subtype := by
    rw [Subgroup.closure_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨_, hx, rfl⟩
    · exact ⟨_, hy, rfl⟩
    · exact ⟨_, hf, rfl⟩
  have hg : (g : P45) ∈ Subgroup.closure ({x45, y45, f45} : Set P45) := by
    rw [← QA45_closure]
    exact g.2
  obtain ⟨k, hk, hkg⟩ := hle hg
  have hkg' : k = g := Subtype.ext hkg
  rwa [hkg'] at hk

private theorem exists_rhoA_mulVec (w : List Bool) (v : V) :
    ∃ a : A45, ((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v =
      evalSpinWordV (toSpinWord w) v := by
  refine ⟨evalW (⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) ⟨y45, Q45_le_A45 y45_mem_Q⟩ w, ?_⟩
  rw [map_evalW, rhoA_x, rhoA_y, coe_evalW_genUnit, evalSpinWordV_eq_matWord_mulVec]

theorem spinQuad_invariant :
    ∀ (a : A45) (v : V), q (((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = q v := by
  let K : Subgroup A45 :=
    { carrier := {a | ∀ v : V,
        q (((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = q v}
      mul_mem' := by
        intro a b ha hb v
        rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
      one_mem' := by
        intro v
        simp
      inv_mem' := by
        intro a ha v
        have h := ha (((rhoA a⁻¹ : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
          Units.val_one, Matrix.one_mulVec] at h
        exact h.symm }
  have hK : K = ⊤ := by
    refine eq_top_of_gens K ?_ ?_ ?_
    · intro v
      rw [rhoA_x]
      exact q_mulVec_Mx v
    · intro v
      rw [rhoA_y]
      exact q_mulVec_My v
    · intro v
      rw [rhoA_f]
      exact q_mulVec_Mf v
  intro a v
  have ha : a ∈ K := by
    rw [hK]
    exact Subgroup.mem_top a
  exact ha v

theorem spinSingular_transitive :
    ∀ v w : V, v ≠ 0 → w ≠ 0 → q v = 0 → q w = 0 →
      ∃ a : A45, ((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = w := by
  intro v w hv hw hqv hqw
  obtain ⟨wv, hwv⟩ := exists_word_sing v hv hqv
  obtain ⟨ww, hww⟩ := exists_word_sing w hw hqw
  obtain ⟨a, ha⟩ := exists_rhoA_mulVec wv spinSingBase
  obtain ⟨b, hb⟩ := exists_rhoA_mulVec ww spinSingBase
  rw [hwv] at ha
  rw [hww] at hb
  refine ⟨b * a⁻¹, ?_⟩
  have hav : ((rhoA a⁻¹ : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = spinSingBase := by
    rw [← ha, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec]
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hav, hb]

theorem spinInvariantQuadratic_unique :
    ∀ Q : V → ZMod 2,
      (∀ u u' w : V,
        Q (u + u' + w) + Q (u + u') + Q (u + w) + Q (u' + w) + Q u + Q u' + Q w = 0) →
      (∀ (a : A45) (v : V),
        Q (((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = Q v) →
      Q = 0 ∨ Q = q := by
  intro Q hpol hinv
  have hQ0 : Q 0 = 0 := by
    have h := hpol 0 0 0
    simp only [add_zero] at h
    revert h
    generalize Q 0 = x
    revert x
    decide
  have hsing : ∀ v : V, v ≠ 0 → q v = 0 → Q v = Q spinSingBase := by
    intro v hv hq
    obtain ⟨w, hw⟩ := exists_word_sing v hv hq
    obtain ⟨a, ha⟩ := exists_rhoA_mulVec w spinSingBase
    rw [← hw, ← ha]
    exact hinv a spinSingBase
  have hnon : ∀ v : V, q v = 1 → Q v = Q spinNonBase := by
    intro v hq
    obtain ⟨w, hw⟩ := exists_word_non v hq
    obtain ⟨a, ha⟩ := exists_rhoA_mulVec w spinNonBase
    rw [← hw, ← ha]
    exact hinv a spinNonBase
  have hone : ∀ x : ZMod 2, ¬ x = 0 → x = 1 := by decide
  have hform : Q = spinOrbitForm (Q spinSingBase) (Q spinNonBase) := by
    funext v
    unfold spinOrbitForm
    split_ifs with h0 h1
    · rw [h0]
      exact hQ0
    · exact hsing v h0 h1
    · exact hnon v (hone _ h1)
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases (Q spinSingBase) with ha | ha
  · rcases hcases (Q spinNonBase) with hc | hc
    · left
      refine hform.trans ?_
      rw [ha, hc]
      funext v
      simp [spinOrbitForm]
    · right
      refine hform.trans ?_
      rw [ha, hc]
      funext v
      exact spinOrbitForm_zero_one v
  · exfalso
    exact spinOrbitForm_second_difference (Q spinNonBase) Q (hform.trans (by rw [ha]))
      (hpol (basis 7) (basis 6) (basis 5))

end CFSG.RankThree.GF2n.Parrott
