module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.SpQv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.SpExt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.PSLAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.PSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Open Matrix
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ gsp conjAut fieldAut
  multiplierUnit multiplierUnit_spec)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
  (unipSp spForm spN isSp_spN spN_mul_self isSp_neg neg_mul_self_neg unipSp_inv
    conjAut_fieldAut_unipSp multiplier_sq_eq exists_spN_inv_skew exists_spN_inv_split)

variable {r : ℕ} {K : Type} [Field K]

theorem exists_inv_of_unipSp_three (A : gsp r K)
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs : Nᵀ * formJ r K + formJ r K * N = 0) (hN : N * N = 0)
    (h : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N *
      (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = -N)
    (hgood : orderOf (proj r K (unipSp N hs hN)) = 3 ∧ IsExtraGood (proj r K (unipSp N hs hN))) :
    ∃ x : StatedProj (StatedSp r K), orderOf x = 3 ∧
      (conjAut r K A * fieldAut r K 1) x = x⁻¹ ∧ IsExtraGood x := by
  have hmap1 : N.map (1 : K ≃+* K) = N := by
    ext i j
    rfl
  refine ⟨proj r K (unipSp N hs hN), hgood.1, ?_, hgood.2⟩
  rw [conjAut_fieldAut_unipSp A 1 hs hN (isSp_neg hs) (neg_mul_self_neg hN)
    (by rw [hmap1]; exact h), ← map_inv, unipSp_inv]

theorem involGood_projectiveSp_three [Finite K] (hK : Nat.card K = 3) (hr : 3 ≤ r) :
    InvolGood (StatedProj (StatedSp r K)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 3 := charP_of_card_eq_prime hK'
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hdvd : (3 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 3 2).mp (by exact_mod_cast h)
    omega
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    omega
  intro α hα
  have hαα : α * α = 1 := by
    rw [← pow_two, ← hα, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    omega
  obtain ⟨A, σ, rfl, -, ⟨d, hd⟩, hσ1, -⟩ :=
    (odd_symplectic_automorphism_semilinear_representation hodd (by omega)).2.2 α hαα hα1
  obtain rfl : σ = 1 := ringEquiv_eq_one_of_card_three hK σ
  left
  have hdM : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (d : K) • 1 := by
    have h := congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hd
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h
    rw [smul_one_eq_diagonal]
    exact h
  have hμ := multiplierUnit_spec A
  have hsq := multiplier_sq_eq (by omega) (A : GL (Fin r ⊕ Fin r) K) hμ hdM
  have hpm : (multiplierUnit A : K) = d ∨ (multiplierUnit A : K) = -d := by
    have h0 : ((multiplierUnit A : K) - d) * ((multiplierUnit A : K) + d) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hpm with hμd | hμd
  · rw [hμd] at hμ
    by_cases hdsq : IsSquare (d : K)
    · obtain ⟨c, hc⟩ := hdsq
      have hc2 : (d : K) = c ^ 2 := by rw [hc, pow_two]
      rw [hc2] at hμ hdM
      have hAs : ∀ a : K,
          ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ≠ a • 1 := by
        intro a ha
        have ha0 : a ≠ 0 := by
          rintro rfl
          have hunit := Matrix.isUnits_det_units (A : GL (Fin r ⊕ Fin r) K)
          have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
          rw [ha, zero_smul, Matrix.det_zero] at hunit
          exact not_isUnit_zero hunit
        apply hσ1 rfl (Units.mk0 a ha0)
        apply Units.ext
        rw [ha, GeneralLinearGroup.coe_scalar, Units.val_mk0, smul_one_eq_diagonal]
        rfl
      obtain ⟨v, u, hv, hu, hvu, hinv⟩ :=
        exists_spN_inv_split h2 (A : GL (Fin r ⊕ Fin r) K) hμ hdM hAs
      exact exists_inv_of_unipSp_three A (isSp_spN v u) (spN_mul_self hvu) hinv
        (good_unipSp_spN_three hK hr hv hu hvu)
    · obtain ⟨e, f, hef, hinv⟩ :=
        exists_frame_inv_ext hr h2 (A : GL (Fin r ⊕ Fin r) K) hμ hdM hdsq
      exact exists_inv_of_unipSp_three A (isSp_frameN e f) (frameN_mul_self hef) hinv
        (good_unipSp_frameN_three hK (by omega) hef)
  · rw [hμd] at hμ
    obtain ⟨v, u, hv, hu, hvu, hinv⟩ :=
      exists_spN_inv_skew (by omega) (A : GL (Fin r ⊕ Fin r) K) hμ hdM
    exact exists_inv_of_unipSp_three A (isSp_spN v u) (spN_mul_self hvu) hinv
      (good_unipSp_spN_three hK hr hv hu hvu)

theorem involAt_PSp : InvolAt .PSp := by
  intro S _ _ n _ hn hS
  obtain ⟨⟨-, -, hn2, -⟩, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  let : Field K := hKf
  have : Finite K := hKfin
  have hK : Nat.card K = 3 := by rw [hKcard, pow_one]
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · exact absurd ⟨rfl, by omega⟩ hn
    · exact h
  exact InvolGood.of_mulEquiv φ.symm (involGood_projectiveSp_three hK hn3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
