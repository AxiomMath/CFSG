module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpSkew
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpExt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Families
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ gsp conjAut fieldAut
  multiplierUnit multiplierUnit_spec mul_transpose_formJ_mul smul_formJ_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)

variable {r : ℕ} {K : Type} [Field K]

theorem multiplier_sq_eq (hr : 1 ≤ r) (A : GL (Fin r ⊕ Fin r) K) {μ d : K}
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A = μ • formJ r K)
    (hd : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * A = d • 1) : μ ^ 2 = d ^ 2 := by
  have h1 := mul_transpose_formJ_mul hA (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  rw [hA, hd] at h1
  simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_smul] at h1
  have : NeZero r := ⟨by omega⟩
  rw [sq, sq, smul_formJ_injective r h1]

theorem involInvertsGood_projectiveSp [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [CharP K p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hr : 2 ≤ r) :
    InvolInvertsGood p (StatedProj (StatedSp r K)) := by
  classical
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := hp.two_le
    omega
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  intro α hα
  have hαα : α * α = 1 := by
    rw [← pow_two, ← hα, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    omega
  obtain ⟨A, σ, rfl, hσ2, ⟨d, hd⟩, hσ1, -⟩ :=
    (odd_symplectic_automorphism_semilinear_representation hodd hr).2.2 α hαα hα1
  have hdM : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ =
      (d : K) • 1 := by
    have h := congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hd
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h
    rw [smul_one_eq_diagonal]
    exact h
  have hμ := multiplierUnit_spec A
  by_cases hσ : σ = 1
  · subst hσ
    have hmap1 : ∀ M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K,
        M.map (1 : K ≃+* K) = M := fun M => by
      ext i j
      rfl
    rw [hmap1] at hdM
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
        rw [← hmap1 (spN v u)] at hinv
        exact exists_inv_of_unipSp A 1 (isSp_spN v u) (spN_mul_self hvu) hinv
          (good_unipSp_spN hp hp2 hK h3 hr hv hu hvu)
      · rcases Nat.lt_or_ge r 3 with hr3 | hr3
        · obtain rfl : r = 2 := by omega
          exact exists_inv_sp_four hp hp2 hK h3 A hμ hdM hdsq
        · obtain ⟨N₁, N₂, hs₁, hs₂, h₁, h₂, h₁₂₁, h₂₁₂, h₁₂, hPQ, hinv⟩ :=
            exists_heis_inv_ext hr3 h2 (A : GL (Fin r ⊕ Fin r) K) hμ hdM hdsq
          rw [← hmap1 N₁] at hinv
          exact exists_inv_of_unipSp A 1 hs₁ h₁ hinv
            (good_unipSp hp hp2 hK h3 (by omega) hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ h₁₂ hPQ)
    · rw [hμd] at hμ
      obtain ⟨v, u, hv, hu, hvu, hinv⟩ :=
        exists_spN_inv_skew hr (A : GL (Fin r ⊕ Fin r) K) hμ hdM
      rw [← hmap1 (spN v u)] at hinv
      exact exists_inv_of_unipSp A 1 (isSp_spN v u) (spN_mul_self hvu) hinv
        (good_unipSp_spN hp hp2 hK h3 hr hv hu hvu)
  · obtain ⟨v, u, hv, hu, hvu, hinv⟩ :=
      exists_spN_inv_field (by omega) (A : GL (Fin r ⊕ Fin r) K) hμ σ hσ hσ2 hdM
    exact exists_inv_of_unipSp A σ (isSp_spN v u) (spN_mul_self hvu) hinv
      (good_unipSp_spN hp hp2 hK h3 hr hv hu hvu)

theorem involQAt_PSp : InvolQAt .PSp := by
  intro S _ _ n p e hp2 h3 _ hS
  obtain ⟨⟨hp, -, hn2, -⟩, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  let : Field K := hKf
  have : Finite K := hKfin
  let : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (f := e) (by rw [← Nat.card_eq_fintype_card, hKcard])
  let : CharP K p := hchar
  exact InvolInvertsGood.of_mulEquiv φ.symm (involInvertsGood_projectiveSp hp hp2 hKcard h3 hn2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
