module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenData
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Assembly.GL83LieDefs

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Open QuadraticMap

abbrev OmegaSevenIdx : Type := Fin 3 ⊕ Fin 3 ⊕ Unit

theorem LiftsConjugate.map {S T : Type} [Group S] [Group T] (e : S ≃* T) {x : S}
    (h : LiftsConjugate x) : LiftsConjugate (e x) := by
  unfold LiftsConjugate
  intro L _ π hπ hcen hperf hcard x' hx' z hz
  have hker : (e.symm.toMonoidHom.comp π).ker = π.ker :=
    MonoidHom.ker_comp_of_injective π e.symm.toMonoidHom e.symm.injective
  refine h L (e.symm.toMonoidHom.comp π) (fun y => ?_) ?_ hperf ?_ x' ?_ z ?_
  · obtain ⟨a, ha⟩ := hπ (e y)
    exact ⟨a, by rw [MonoidHom.comp_apply, ha]; exact MulEquiv.symm_apply_apply e y⟩
  · rw [hker]; exact hcen
  · rw [hker]; exact hcard
  · rw [MonoidHom.comp_apply, hx']; exact MulEquiv.symm_apply_apply e x
  · rwa [hker]

section Eichler

variable {K : Type} [Field K]

@[expose] def OmegaSevenShortPair (u w : OmegaSevenIdx → K) : Prop :=
  quadOdd 3 K u = 0 ∧ u ≠ 0 ∧ polar (quadOdd 3 K) u w = 0 ∧ quadOdd 3 K w = 1

noncomputable def eichlerOmega (h2 : (2 : K) ≠ 0) (u w : OmegaSevenIdx → K) :
    StatedOmega (StatedQuadOdd 3 K) :=
  ⟨(toLinEquiv OmegaSevenIdx K).symm (eichler (quadOdd 3 K) u w), by
    rw [statedOmega_quadOdd_eq_map h2 le_rfl]
    exact Subgroup.mem_map_of_mem _ (eichler_mem_elementaryGroup _ _ _)⟩

noncomputable def eichlerProj (h2 : (2 : K) ≠ 0) (u w : OmegaSevenIdx → K) :
    StatedProj (StatedOmega (StatedQuadOdd 3 K)) :=
  QuotientGroup.mk (eichlerOmega h2 u w)

theorem eichlerProj_mul (h2 : (2 : K) ≠ 0) {u v w : OmegaSevenIdx → K}
    (hu : quadOdd 3 K u = 0) (hv : polar (quadOdd 3 K) u v = 0)
    (hw : polar (quadOdd 3 K) u w = 0) :
    eichlerProj h2 u v * eichlerProj h2 u w = eichlerProj h2 u (v + w) := by
  have hmul : eichlerOmega h2 u v * eichlerOmega h2 u w = eichlerOmega h2 u (v + w) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, eichlerOmega]
    rw [← map_mul, eichler_mul hv hw]
  simp only [eichlerProj]
  rw [← QuotientGroup.mk_mul, hmul]

theorem eichlerProj_zero_right (h2 : (2 : K) ≠ 0) (u : OmegaSevenIdx → K) :
    eichlerProj h2 u 0 = 1 := by
  have h1 : eichlerOmega h2 u 0 = 1 := by
    apply Subtype.ext
    simp [eichlerOmega, eichler_zero_right]
  simp only [eichlerProj]
  rw [h1, QuotientGroup.mk_one]

theorem eichlerProj_inv (h2 : (2 : K) ≠ 0) {u w : OmegaSevenIdx → K}
    (hu : quadOdd 3 K u = 0) (hw : polar (quadOdd 3 K) u w = 0) :
    (eichlerProj h2 u w)⁻¹ = eichlerProj h2 u (-w) := by
  rw [inv_eq_iff_mul_eq_one,
    eichlerProj_mul h2 hu hw (by rw [polar_neg_right, hw, neg_zero]), add_neg_cancel,
    eichlerProj_zero_right]

theorem eichlerProj_neg_left (h2 : (2 : K) ≠ 0) (u w : OmegaSevenIdx → K) :
    eichlerProj h2 (-u) w = eichlerProj h2 u (-w) := by
  have h1 : eichlerOmega h2 (-u) w = eichlerOmega h2 u (-w) := by
    apply Subtype.ext
    simp only [eichlerOmega]
    rw [show (-u : OmegaSevenIdx → K) = (-1 : K) • u from by simp,
      show (-w : OmegaSevenIdx → K) = (-1 : K) • w from by simp, eichler_smul_left]
  simp only [eichlerProj]
  rw [h1]

theorem orderOf_eichlerProj (hK : Nat.card K = 3) (h2 : (2 : K) ≠ 0) [Finite K]
    {u w : OmegaSevenIdx → K} (hu : quadOdd 3 K u = 0) (hu0 : u ≠ 0)
    (hw : polar (quadOdd 3 K) u w = 0) (hQw : quadOdd 3 K w ≠ 0) :
    orderOf (eichlerProj h2 u w) = 3 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have h3w : w + w + w = 0 := by
    have h : w + w + w = (Fintype.card K : K) • w := by
      rw [hcard, Nat.cast_smul_eq_nsmul, add_assoc, ← three_nsmul]
    rw [h, FiniteField.cast_card_eq_zero K, zero_smul]
  have h2w : polar (quadOdd 3 K) u (w + w) = 0 := by
    rw [polar_add_right, hw, add_zero]
  have hpow : (eichlerProj h2 u w) ^ 3 = 1 := by
    change (eichlerProj h2 u w) ^ (2 + 1) = 1
    rw [pow_succ, pow_two]
    rw [eichlerProj_mul h2 hu hw hw, eichlerProj_mul h2 hu h2w hw, h3w,
      eichlerProj_zero_right]
  have hne : eichlerProj h2 u w ≠ 1 := by
    intro h1
    have hmem : eichlerOmega h2 u w ∈
        (StatedScalars OmegaSevenIdx K).subgroupOf (StatedOmega (StatedQuadOdd 3 K)) :=
      (QuotientGroup.eq_one_iff (eichlerOmega h2 u w)).mp h1
    rw [Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hmem
    have hx : toLinEquiv OmegaSevenIdx K
        (eichlerOmega h2 u w : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
        eichler (quadOdd 3 K) u w := by
      simp [eichlerOmega]
    rw [hx] at hmem
    obtain ⟨c, hc⟩ := mem_scalars.mp hmem
    have hcu : c = 1 := by
      have h1' : u = c • u := by rw [← hc u, eichler_apply_self]
      have h2' : (c - 1) • u = 0 := by rw [sub_smul, one_smul, ← h1', sub_self]
      rcases smul_eq_zero.mp h2' with h3' | h3'
      · exact sub_eq_zero.mp h3'
      · exact absurd h3' hu0
    have hex : ∃ x, polar (quadOdd 3 K) x u ≠ 0 := by
      by_contra hc0
      rw [not_exists] at hc0
      exact hu0 ((nondegenerate_polarBilin_quadOdd 3 K h2).2 u fun x => by
        rw [polarBilin_apply_apply]
        exact not_ne_iff.mp (hc0 x))
    obtain ⟨x, hx1⟩ := hex
    set x' := (polar (quadOdd 3 K) x u)⁻¹ • x with hx'def
    have hx1' : polar (quadOdd 3 K) x' u = 1 := by
      rw [hx'def, polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hx1]
    have hx' : eichler (quadOdd 3 K) u w x' = x' := by rw [hc x', hcu, one_smul]
    rw [eichler_apply hu hw x', hx1'] at hx'
    simp only [one_smul, mul_one] at hx'
    have hw0 : quadOdd 3 K w = 0 := by
      have hw_eq : w = (polar (quadOdd 3 K) x' w + quadOdd 3 K w) • u :=
        add_left_cancel (sub_eq_iff_eq_add.mp hx')
      rw [hw_eq, QuadraticMap.map_smul, hu, smul_zero]
    exact hQw hw0
  exact orderOf_eq_prime hpow hne

theorem map_eichlerProj_of_isometry (h2 : (2 : K) ≠ 0)
    {A : Matrix.GeneralLinearGroup OmegaSevenIdx K}
    (hA : ∀ v, quadOdd 3 K (A.val.mulVec v) = quadOdd 3 K v)
    {β : MulAut (StatedProj (StatedOmega (StatedQuadOdd 3 K)))}
    (hβ : ∀ x : StatedOmega (StatedQuadOdd 3 K), ∃ y : StatedOmega (StatedQuadOdd 3 K),
      (y : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
          A * (x : Matrix.GeneralLinearGroup _ K) * A⁻¹ ∧
        β (QuotientGroup.mk x) = QuotientGroup.mk y)
    (u w : OmegaSevenIdx → K) :
    β (eichlerProj h2 u w) = eichlerProj h2 (A.val.mulVec u) (A.val.mulVec w) := by
  obtain ⟨y, hy, hβy⟩ := hβ (eichlerOmega h2 u w)
  have horth : toLinEquiv OmegaSevenIdx K A ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [toLinEquiv_apply]
      exact hA v
  have hx : toLinEquiv OmegaSevenIdx K
      (eichlerOmega h2 u w : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
      eichler (quadOdd 3 K) u w := by
    simp [eichlerOmega]
  have hy' : toLinEquiv OmegaSevenIdx K (y : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
      eichler (quadOdd 3 K) (A.val.mulVec u) (A.val.mulVec w) := by
    rw [hy]
    simp only [map_mul, MulEquiv.map_inv, hx, eichler_conj horth u w, toLinEquiv_apply]
  have hyeq : y = eichlerOmega h2 (A.val.mulVec u) (A.val.mulVec w) := by
    apply Subtype.ext
    exact (toLinEquiv OmegaSevenIdx K).injective (by rw [hy']; simp [eichlerOmega])
  simp only [eichlerProj]
  rw [hβy, hyeq]

end Eichler

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
