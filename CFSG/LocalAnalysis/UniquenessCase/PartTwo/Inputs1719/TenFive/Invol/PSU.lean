module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuHeis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuPaired
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuBarScalar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuBarOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuBarNeg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Families

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Open
open CFSG.Blueprint (LieModel)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem inner_involution_lift (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hr : 1 ≤ r)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε)
    (hA2 : orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h r ε) = 2) :
    ∃ l : K, l ≠ 0 ∧ (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1 ∧
      (h.norm l = 1 ∨ h.norm l = -1) ∧
      ∀ c : K, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) ≠ c • 1 := by
  have hsq : (QuotientGroup.mk (⟨A, hA⟩ * ⟨A, hA⟩) : hypUnitaryMod h r ε) = 1 := by
    rw [QuotientGroup.mk_mul, ← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hA2])
  obtain ⟨d, hd, -, hAA⟩ := mem_normOneScalars.mp ((QuotientGroup.eq_one_iff _).mp hsq)
  obtain ⟨l, hl0, hld⟩ := exists_sq_eq_of_norm_eq_one h hp2 hd
  have hAA' : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1 := by
    have h1 := congrArg (fun g : GL (HypIndex r ε) K =>
      (g : Matrix (HypIndex r ε) (HypIndex r ε) K)) hAA
    simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
    rw [h1, hld, scalar_apply, smul_one_eq_diagonal]
  have hN : h.norm l = 1 ∨ h.norm l = -1 := by
    have h1 : h.norm l * h.norm l = 1 := by
      rw [← norm_mul_eq h, ← pow_two, hld, hd]
    exact mul_self_eq_one_iff.mp h1
  refine ⟨l, hl0, hAA', hN, fun c hc => ?_⟩
  have hU := mem_hypUnitary.mp hA
  rw [hc, smul_one_eq_diagonal, ← scalar_apply, scalar_gram h c] at hU
  have hcN : h.norm c = 1 := by
    have h2 := congrFun (congrFun hU (.inl ⟨0, hr⟩)) (hypPartner (.inl ⟨0, hr⟩))
    simpa [hypGram_apply] using h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp [UnitaryFieldData.norm] at hcN
  have h1 : (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h r ε) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    refine ⟨Units.mk0 c hc0, hcN, pow_zero _, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply, ← smul_one_eq_diagonal]
    exact hc
  rw [h1, orderOf_one] at hA2
  exact absurd hA2 (by norm_num)

theorem involInvertsGood_hypPSU (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h3 : 3 < p ^ f)
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) : InvolInvertsGood p (hypPSU h r ε) := by
  intro α hα
  obtain ⟨A, σ, hx, hA, rfl, hσ, hrefl, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation h hp2 hr hε hn).2.2.2 α hα
  obtain ⟨v, w, γ, hd, hAE⟩ : ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * (hypEichler h v w γ).map σ =
        hypEichler h v (-w) (h.bar γ) * A := by
    rcases hσ with rfl | hσ
    · obtain ⟨l, hl0, hAA, hN, hAs⟩ := inner_involution_lift h hp2 hr hA (hrefl rfl)
      obtain ⟨v, w, γ, hd, hE⟩ : ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * hypEichler h v w γ =
            hypEichler h v (-w) (h.bar γ) * A := by
        rcases hN with hN | hN
        · exact exists_eichler_inv_split h hp2 hn hA hl0 hAA hN hAs
        · exact exists_eichler_inv_paired h hp2 hA hAA hN hAs
      exact ⟨v, w, γ, hd, hE⟩
    · obtain ⟨c, -, hc⟩ := hbar hσ
      have hmap (M : Matrix (HypIndex r ε) (HypIndex r ε) K) : M.map σ = M.map h.bar :=
        Matrix.ext fun _ _ => hσ _
      obtain ⟨v, w, γ, hd, hE⟩ : ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * (hypEichler h v w γ).map h.bar =
            hypEichler h v (-w) (h.bar γ) * A := by
        rcases bar_scalar_eq_one_or_neg_one h hr hA hc with rfl | rfl
        · exact exists_eichler_inv_barOne h hp2 hn hA (by rw [hc, one_smul])
        · exact exists_eichler_inv_barNeg h hp2 hn hA (by rw [hc, neg_one_smul])
      exact ⟨v, w, γ, hd, by rw [hmap]; exact hE⟩
  obtain ⟨hord, hgood⟩ := good_eichlerSU h hp2 h3 hn hd
  exact ⟨_, hord, semilinearAutHom_eichler_inv h hr hε hx hd.isotropic hd.orthogonal
    hd.trace_eq hAE, Or.inl hgood⟩

theorem involQAt_PSU : InvolQAt .PSU := by
  intro S _ _ n p e hp2 h3 _ hS
  obtain ⟨⟨hp, he1, hn3, -⟩, K, hKf, -, hKcard, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  let : Field K := hKf
  have h : UnitaryFieldData p e K := ⟨hp, he1, by rw [hKcard, ← pow_mul, mul_comm]⟩
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε : ℕ, ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  exact InvolInvertsGood.of_mulEquiv ((hypPSUEquivStatedProj h hR (by omega)).trans φ.symm)
    (involInvertsGood_hypPSU h hp2 h3 (by omega) hε hn3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
