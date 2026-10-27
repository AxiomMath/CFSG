module

public import CFSG.Quasithin.Vol2.Ch11SecOE9B
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftSL2
public import CFSG.RankThree.PartOne.SEITZ4.SpPlane

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.SEITZ4
open CFSG.LocalAnalysis.ComponentInitial (sl2Upper sl2Lower sl2_closure_upper_lower)
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem spForm_e₀_f {x : ↥(StatedSp 2 K)} (hc : spForm 2 K e₀ (mat x *ᵥ e₀) ≠ 0) :
    spForm 2 K e₀ ((spForm 2 K e₀ (mat x *ᵥ e₀))⁻¹ • (mat x *ᵥ e₀)) = 1 := by
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]

theorem planeHom_upper_eq {f : Fin 2 ⊕ Fin 2 → K} (hf : spForm 2 K e₀ f = 1) (t : K) :
    planeHom hf (sl2Upper K t) = xHom (Multiplicative.ofAdd t) :=
  Subtype.ext (planeHom_upper hf _ t rfl)

theorem range_planeHom_le {R : Subgroup ↥(StatedSp 2 K)} (hXR : rootX ≤ R)
    {x : ↥(StatedSp 2 K)} (hx : x ∈ R) (hc : spForm 2 K e₀ (mat x *ᵥ e₀) ≠ 0) :
    (planeHom (spForm_e₀_f hc)).range ≤ R := by
  set c := spForm 2 K e₀ (mat x *ᵥ e₀) with hcdef
  rw [MonoidHom.range_eq_map, ← sl2_closure_upper_lower, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨M, ⟨t, rfl⟩ | ⟨t, rfl⟩, rfl⟩
  · rw [SetLike.mem_coe, planeHom_upper_eq]
    exact hXR ⟨_, rfl⟩
  · have h1 : planeHom (spForm_e₀_f hc) (sl2Lower K t) =
        x * xHom (Multiplicative.ofAdd (c⁻¹ ^ 2 * t)) * x⁻¹ := by
      apply Subtype.ext
      rw [planeHom_lower (spForm_e₀_f hc) _ t rfl, spTrans_smul, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv]
      exact (conj_spTrans x.2 e₀ _).symm
    rw [SetLike.mem_coe, h1]
    exact R.mul_mem (R.mul_mem hx (hXR ⟨_, rfl⟩)) (R.inv_mem hx)

omit [CharP K 2] in
theorem sl2Upper_mul_sl2Lower_ne :
    sl2Upper K 1 * sl2Lower K 1 ≠ sl2Lower K 1 * sl2Upper K 1 := by
  intro h
  have h1 := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [sl2Upper, sl2Lower, Matrix.mul_apply, Fin.sum_univ_two] at h1

theorem not_isSolvable_SL2 (h4 : 4 ≤ Nat.card K) : ¬ Group.IsSolvable SL(2, K) := by
  have := E1.RootLift.isSimpleGroup_SL2 h4
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  exact fun hc => sl2Upper_mul_sl2Lower_ne (hc _ _)

theorem planeHom_injective (h4 : 4 ≤ Nat.card K) {f : Fin 2 ⊕ Fin 2 → K}
    (hf : spForm 2 K e₀ f = 1) : Function.Injective (planeHom hf) := by
  have := E1.RootLift.isSimpleGroup_SL2 h4
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (planeHom hf).ker with h | h
  · exact h
  · exfalso
    have h1 : sl2Upper K 1 ∈ (planeHom hf).ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, planeHom_upper_eq] at h1
    have h2 := xHom_injective (h1.trans (map_one xHom).symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd h2)

theorem rootX_dichotomy (h4 : 4 ≤ Nat.card K) {R : Subgroup ↥(StatedSp 2 K)} (hXR : rootX ≤ R) :
    (∃ N : Subgroup ↥(StatedSp 2 K), N ≤ R ∧ (N.subgroupOf R).Normal ∧ IsPGroup 2 N ∧
      rootX ≤ N) ∨
    (¬ Group.IsSolvable ↥R ∧ ∀ N : Subgroup ↥(StatedSp 2 K), N ≤ R → (N.subgroupOf R).Normal →
      Group.IsSolvable ↥N → rootX ⊓ N = ⊥) := by
  by_cases h : ∀ x ∈ R, spForm 2 K (mat x *ᵥ e₀) e₀ = 0
  · exact Or.inl (exists_normal_expTwo hXR h)
  push Not at h
  obtain ⟨x, hx, hc'⟩ := h
  have hc : spForm 2 K e₀ (mat x *ᵥ e₀) ≠ 0 := by rwa [spForm_comm']
  set H := (planeHom (spForm_e₀_f hc)).range with hHdef
  have hHR : H ≤ R := range_planeHom_le hXR hx hc
  set eH : SL(2, K) ≃* ↥H := MonoidHom.ofInjective (planeHom_injective h4 (spForm_e₀_f hc))
  have := E1.RootLift.isSimpleGroup_SL2 h4
  have hsimp : IsSimpleGroup ↥H := eH.symm.isSimpleGroup
  have hHns : ¬ Group.IsSolvable ↥H := fun hs =>
    not_isSolvable_SL2 h4 (Group.isSolvable_of_isSolvable_injective eH.injective)
  have hXH : rootX ≤ H := by
    rintro _ ⟨t, rfl⟩
    exact ⟨sl2Upper K (Multiplicative.toAdd t), planeHom_upper_eq _ _⟩
  refine Or.inr ⟨fun hs => hHns (Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hHR)), fun N hNR hNn hNs => ?_⟩
  have hRN := (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).mp hNn
  have hn : ((N ⊓ H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      ((le_inf (hHR.trans hRN) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ H).subgroupOf H) with h0 | h0
  · refine eq_bot_iff.mpr fun y hy => ?_
    have hy' : (⟨y, hXH hy.1⟩ : ↥H) ∈ (N ⊓ H).subgroupOf H := ⟨hy.2, hXH hy.1⟩
    rw [h0, Subgroup.mem_bot] at hy'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hy')
  · exfalso
    have hHN : H ≤ N := fun y hy => by
      have hy' : (⟨y, hy⟩ : ↥H) ∈ (N ⊓ H).subgroupOf H := h0 ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hy').1
    exact hHns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHN))

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
