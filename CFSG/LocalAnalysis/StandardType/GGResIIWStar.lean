module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIDual

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggResII_isRefl (hp2 : p ≠ 2) {t : V ≃ₗ[ZMod p] V} {H : V} {A : Module.Dual (ZMod p) V}
    (ht : ∀ w, t w = w - A w • H) (h2 : A H = 2) : ZS.IsRefl p t := by
  have hH : H ≠ 0 := by
    rintro rfl
    rw [map_zero] at h2
    exact zmod_two_ne_zero hp2 h2.symm
  refine ⟨LinearEquiv.ext fun w => ?_, ?_⟩
  · show t (t w) = w
    rw [ht, ht, map_sub, map_smul, h2, smul_eq_mul]
    module
  · have hrange : LinearMap.range ((t : V →ₗ[ZMod p] V) - LinearMap.id) =
        Submodule.span (ZMod p) {H} := by
      apply le_antisymm
      · rintro v ⟨w, rfl⟩
        rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, ht, sub_sub_cancel_left,
          ← neg_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self H)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        refine ⟨-(2 : ZMod p)⁻¹ • H, ?_⟩
        rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, ht, sub_sub_cancel_left,
          map_smul, h2, smul_eq_mul, ← neg_smul]
        rw [show -(-(2 : ZMod p)⁻¹ * 2) = 1 by
          rw [neg_mul, neg_neg, inv_mul_cancel₀ (zmod_two_ne_zero hp2)], one_smul]
    rw [hrange]
    exact finrank_span_singleton hH

theorem ggResII_linWeyl_dual (hp2 : p ≠ 2) [Module.Finite (ZMod p) V] {I : Type} [Fintype I]
    [DecidableEq I] {M : CoxeterMatrix I} {C : Matrix I I ℤ} (hFT : TauCeti.IsFiniteType C)
    (hC : GGIntCartan M C) (hW : GGIsWeylMatrix M) (t : I → (V ≃ₗ[ZMod p] V)) (H : I → V)
    (A : I → Module.Dual (ZMod p) V) (ht : ∀ i w, t i w = w - A i w • H i)
    (hP : ∀ i j, A j (H i) = (C i j : ZMod p)) (hsep : ∀ w : V, (∀ i, A i w = 0) → w = 0)
    (hdim : Module.finrank (ZMod p) V = Fintype.card I) :
    ZS.LinWeyl p (Subgroup.closure (Set.range t)) := by
  classical
  have h2 : ∀ i, A i (H i) = 2 := fun i => by rw [hP, hC.1 i]; norm_num
  let Φ : V →ₗ[ZMod p] (I → ZMod p) := LinearMap.pi fun i => A i
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hsep w fun i => congrFun hw i
  have hΦsurj : Function.Surjective Φ := by
    have hfr : Module.finrank (ZMod p) V = Module.finrank (ZMod p) (I → ZMod p) := by
      rw [hdim, Module.finrank_fintype_fun_eq_card]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hΦinj
  have hind : LinearIndependent (ZMod p) A := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    obtain ⟨w, hw⟩ := hΦsurj (Pi.single k 1)
    have h1 := congrArg (fun f : Module.Dual (ZMod p) V => f w) hc
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at h1
    have hA : ∀ i, A i w = (Pi.single k 1 : I → ZMod p) i := fun i => congrFun hw i
    simp only [hA, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    exact h1
  let ev : I → Module.Dual (ZMod p) (Module.Dual (ZMod p) V) :=
    fun i => Module.Dual.eval (ZMod p) V (H i)
  have hα : ∀ i, ev i (A i) = 2 := h2
  have hP' : ∀ i j, ev i (A j) = (C i j : ZMod p) := hP
  have hL := isLiftable_reflection_of_intCartan hC A ev hα hP'
  set ρ := M.toCoxeterSystem.lift ⟨fun i => Module.reflection (hα i), hL⟩ with hρ
  have hρinj : Function.Injective ρ :=
    ggCartanFaithful_of_isFiniteType hα hP' hp2 hFT hC hind
  have hcontra : ∀ i, ggContra (t i) = Module.reflection (hα i) := by
    intro i
    have hinv : (t i).symm = t i := by
      refine LinearEquiv.ext fun w => ?_
      rw [LinearEquiv.symm_apply_eq, ht, ht, map_sub, map_smul, h2, smul_eq_mul]
      module
    ext f w
    rw [ggContra_apply, hinv, ht, map_sub, map_smul, smul_eq_mul, Module.reflection_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, ev,
      Module.Dual.eval_apply]
    ring
  have hrange : ρ.range = (Subgroup.closure (Set.range t)).map ggContra := by
    rw [MonoidHom.map_closure, MonoidHom.range_eq_map,
      ← M.toCoxeterSystem.subgroup_closure_range_simple, MonoidHom.map_closure]
    congr 1
    ext e
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨t i, ⟨i, rfl⟩, by rw [hcontra, hρ, CoxeterSystem.lift_apply_simple]⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨M.toCoxeterSystem.simple i, ⟨i, rfl⟩, by
        rw [hcontra, hρ, CoxeterSystem.lift_apply_simple]⟩
  let e₁ : M.Group ≃* ρ.range := MonoidHom.ofInjective hρinj
  let e₂ : ↥(Subgroup.closure (Set.range t)) ≃* ↥((Subgroup.closure (Set.range t)).map ggContra) :=
    (Subgroup.closure (Set.range t)).equivMapOfInjective ggContra ggContra_injective
  let f : M.Group ≃* ↥(Subgroup.closure (Set.range t)) :=
    (e₁.trans (MulEquiv.subgroupCongr hrange)).trans e₂.symm
  refine ⟨I, M, hW, f, fun i => ?_⟩
  have hfi : f (M.simple i) = ⟨t i, Subgroup.subset_closure (Set.mem_range_self i)⟩ := by
    show e₂.symm ((e₁.trans (MulEquiv.subgroupCongr hrange)) (M.simple i)) = _
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    change ρ (M.simple i) = ggContra (t i)
    rw [hcontra, hρ]
    exact CoxeterSystem.lift_apply_simple _ _ i
  rw [hfi]
  exact ggResII_isRefl hp2 (ht i) (h2 i)

end CFSG.StandardType
