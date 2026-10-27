module

public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bTorus
public import CFSG.HardMathSupport.C14IdxDet
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdxRee
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcRee

public noncomputable section

namespace CFSG.StandardType.TwE6E4bFlag

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TwE6E4bTorus CFSG.StandardType.TwE6FixedA2SL3
  CFSG.StandardType.TwE6FixedA2Type CFSG.StandardType.TwE6HyperplaneTypes

local instance : NeZero Tag.E6.rank := ⟨by decide⟩

abbrev longWeight (μ : ℤ × ℤ) : Prop := μ.1 * μ.1 + μ.1 * μ.2 + μ.2 * μ.2 = 3

@[expose] def Vlong (Ω : Type) [Field Ω] : Submodule Ω (RootModule .E6 Ω) :=
  Finsupp.supported Ω Ω {ℓ : Label .E6 | longWeight (diagWt 0 ℓ, diagWt 2 ℓ)}

@[expose] def VlongFixer (Ω : Type) [Field Ω] : Subgroup (ModGL .E6 Ω) :=
  (fixingSubgroup (RootModule .E6 Ω ≃ₗ[Ω] RootModule .E6 Ω)
      (Vlong Ω : Set (RootModule .E6 Ω))).comap
    (LinearMap.GeneralLinearGroup.generalLinearEquiv Ω (RootModule .E6 Ω)).toMonoidHom

@[expose] def Wlong (Ω : Type) [Field Ω] (E : Subgroup (ModGL .E6 Ω)) :
    Subgroup (ModGL .E6 Ω) :=
  E ⊓ VlongFixer Ω

theorem longWeight_inl (i : Fin Tag.E6.rank) :
    ¬ longWeight (diagWt 0 (Sum.inl i), diagWt 2 (Sum.inl i)) := by
  simp [longWeight, diagWt_inl]

theorem diagWt_inr (k : Fin Tag.E6.rank) (α : {v : Fin Tag.E6.rank → ℤ // IsRoot .E6 v}) :
    diagWt k (Sum.inr α) = wtVec k α.1 := rfl

set_option maxRecDepth 100000 in
theorem longWeight_rootFinset_filter :
    (rootFinset .E6).filter (fun δ => longWeight (wtVec 0 δ, wtVec 2 δ)) =
      fixedA2E6.toFinset := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem longWeight_inr_iff (α : {v : Fin Tag.E6.rank → ℤ // IsRoot .E6 v}) :
    longWeight (diagWt 0 (Sum.inr α), diagWt 2 (Sum.inr α)) ↔ α.1 ∈ fixedA2E6 := by
  rw [diagWt_inr, diagWt_inr]
  constructor
  · intro h
    have hmem : α.1 ∈ (rootFinset .E6).filter
        (fun δ => longWeight (wtVec 0 δ, wtVec 2 δ)) :=
      Finset.mem_filter.mpr ⟨mem_rootFinset.mpr α.2, h⟩
    rwa [longWeight_rootFinset_filter] at hmem
  · intro h
    have hmem : α.1 ∈ (rootFinset .E6).filter
        (fun δ => longWeight (wtVec 0 δ, wtVec 2 δ)) := by
      rw [longWeight_rootFinset_filter]
      exact h
    exact (Finset.mem_filter.mp hmem).2

theorem longWeight_label_iff (ℓ : Label .E6) :
    longWeight (diagWt 0 ℓ, diagWt 2 ℓ) ↔
      ∃ (α : Fin Tag.E6.rank → ℤ) (hα : IsRoot .E6 α), α ∈ fixedA2E6 ∧
        ℓ = Sum.inr ⟨α, hα⟩ := by
  rcases ℓ with i | α
  · constructor
    · exact fun h => absurd h (longWeight_inl i)
    · rintro ⟨α, hα, -, h⟩
      cases h
  · constructor
    · intro h
      exact ⟨α.1, α.2, (longWeight_inr_iff α).mp h, rfl⟩
    · rintro ⟨α, hα, hmem, h⟩
      rw [h]
      exact (longWeight_inr_iff ⟨α, hα⟩).mpr hmem

theorem longWeight_weylMatList_apply {μ ν : ℤ × ℤ} (h : (μ, ν) ∈ weylMatList) (x : ℤ × ℤ) :
    longWeight (μ.1 * x.1 + ν.1 * x.2, μ.2 * x.1 + ν.2 * x.2) ↔ longWeight x := by
  simp only [weylMatList, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [longWeight]
    constructor <;> intro hq <;> nlinarith

set_option maxRecDepth 100000 in
theorem normalizer_fixedA2Torus_support_long
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (R : ModGL .E6 Ω) (hR : R ∈ Subgroup.normalizer (fixedA2Torus Ω))
    {a b : Label .E6}
    (hb : longWeight (diagWt 0 b, diagWt 2 b))
    (hRab : (R : Module.End Ω (RootModule .E6 Ω)) (Finsupp.single b 1) a ≠ 0) :
    longWeight (diagWt 0 a, diagWt 2 a) := by
  classical
  let R' : Module.End Ω (RootModule .E6 Ω) := (R : Module.End Ω (RootModule .E6 Ω))
  have hmem : ∀ s u : Ωˣ, ∃ a b : Ωˣ,
      fixedA2Rho Ω (diagSL3 a b) = R * fixedA2Rho Ω (diagSL3 s u) * R⁻¹ := by
    intro s u
    obtain ⟨q, hq⟩ := ((Subgroup.mem_set_normalizer_iff.mp hR)
      (fixedA2Rho Ω (diagSL3 s u))).mp ⟨(s, u), rfl⟩
    exact ⟨q.1, q.2, hq⟩
  choose θ₁ θ₂ hθ using hmem
  have hθ' : ∀ s u : Ωˣ, R * rootDiagUnit .E6 (diagTuple s u) * R⁻¹ =
      rootDiagUnit .E6 (diagTuple (θ₁ s u) (θ₂ s u)) := by
    intro s u
    rw [← fixedA2Rho_diagSL3 Ω s u, ← fixedA2Rho_diagSL3 Ω (θ₁ s u) (θ₂ s u)]
    exact (hθ s u).symm
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_diagWt_eq (μ := (1, 0)) (by decide)
  obtain ⟨ℓ₂, hℓ₂⟩ := exists_diagWt_eq (μ := (0, 1)) (by decide)
  obtain ⟨b₁, b₂, hθform, hrows, hcols⟩ :=
    exists_weightMatrix_of_conj_rootDiagUnit (Ω := Ω) diagTuple (diagWt 0) (diagWt 2)
      rootChar_diagTuple R θ₁ θ₂ hθ' (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      ⟨congrArg Prod.fst hℓ₁, congrArg Prod.snd hℓ₁⟩
      ⟨congrArg Prod.fst hℓ₂, congrArg Prod.snd hℓ₂⟩
  have hμν : (((diagWt 0 b₁, diagWt 2 b₁), (diagWt 0 b₂, diagWt 2 b₂)) ∈
      weylMatList) := by
    refine weightMatrix_mem_weylMatList _ (diagWt_mem_diagWtList b₁) _
      (diagWt_mem_diagWtList b₂) ?_ ?_
    · intro α hα
      obtain ⟨a, rfl⟩ := exists_diagWt_eq hα
      obtain ⟨b, hb1, hb2⟩ := hrows a
      rw [← hb1, ← hb2]
      exact diagWt_mem_diagWtList b
    · intro β hβ
      obtain ⟨b, rfl⟩ := exists_diagWt_eq hβ
      obtain ⟨a, ha1, ha2⟩ := hcols b
      exact ⟨(diagWt 0 a, diagWt 2 a), diagWt_mem_diagWtList a,
        by rw [ha1, ha2]⟩
  have hdiag : ∀ (s : Fin Tag.E6.rank → Ωˣ) (b : Label .E6),
      (rootDiagUnit .E6 s : Module.End Ω (RootModule .E6 Ω)) (Finsupp.single b 1) =
        ((rootChar s (labelWt .E6 b) : Ωˣ) : Ω) • Finsupp.single b 1 := by
    intro s b
    change rootDiag s (Finsupp.single b 1) = _
    rw [rootDiag_single]
  have key : ∀ (s u : Ωˣ) (a b : Label .E6),
      ((s ^ diagWt 0 b * u ^ diagWt 2 b : Ωˣ) : Ω) * R' (Finsupp.single b 1) a =
        ((θ₁ s u ^ diagWt 0 a * θ₂ s u ^ diagWt 2 a : Ωˣ) : Ω) *
          R' (Finsupp.single b 1) a := by
    intro s u a b
    have e := congrArg (fun X : ModGL .E6 Ω =>
      (X : Module.End Ω (RootModule .E6 Ω)) (Finsupp.single b 1) a)
      (eq_mul_of_mul_inv_eq (hθ' s u))
    simp only [Units.val_mul, Module.End.mul_apply] at e
    rw [hdiag (diagTuple s u) b, map_smul, Finsupp.smul_apply, smul_eq_mul] at e
    rw [CFSG.HardMathSupport.C14IdxDet.rootDiagUnit_apply_apply
      (diagTuple (θ₁ s u) (θ₂ s u)) (R' (Finsupp.single b 1)) a] at e
    rw [rootChar_diagTuple s u b,
      rootChar_diagTuple (θ₁ s u) (θ₂ s u) a] at e
    exact e
  have hM : ∀ (a b : Label .E6), R' (Finsupp.single b 1) a ≠ 0 →
      ∀ s u : Ωˣ, s ^ diagWt 0 b * u ^ diagWt 2 b =
        (s ^ diagWt 0 b₁ * u ^ diagWt 2 b₁) ^ diagWt 0 a *
          (s ^ diagWt 0 b₂ * u ^ diagWt 2 b₂) ^ diagWt 2 a := by
    intro a b hb s u
    have e : s ^ diagWt 0 b * u ^ diagWt 2 b =
        θ₁ s u ^ diagWt 0 a * θ₂ s u ^ diagWt 2 a :=
      Units.ext (mul_right_cancel₀ hb (key s u a b))
    rw [e, (hθform s u).1, (hθform s u).2]
  have hA : ∀ (a b : Label .E6), R' (Finsupp.single b 1) a ≠ 0 →
      ∀ s : Ωˣ, s ^ diagWt 0 b =
        s ^ (diagWt 0 b₁ * diagWt 0 a + diagWt 0 b₂ * diagWt 2 a) := by
    intro a b hb s
    have h := hM a b hb s 1
    simp only [one_zpow, mul_one] at h
    rw [← zpow_mul, ← zpow_mul, ← zpow_add] at h
    exact h
  have hB : ∀ (a b : Label .E6), R' (Finsupp.single b 1) a ≠ 0 →
      ∀ u : Ωˣ, u ^ diagWt 2 b =
        u ^ (diagWt 2 b₁ * diagWt 0 a + diagWt 2 b₂ * diagWt 2 a) := by
    intro a b hb u
    have h := hM a b hb 1 u
    simp only [one_zpow, one_mul] at h
    rw [← zpow_mul, ← zpow_mul, ← zpow_add] at h
    exact h
  have hw₁ : diagWt 0 b = diagWt 0 b₁ * diagWt 0 a + diagWt 0 b₂ * diagWt 2 a := by
    have hk : diagWt 0 b - (diagWt 0 b₁ * diagWt 0 a + diagWt 0 b₂ * diagWt 2 a) = 0 := by
      apply CFSG.StandardType.TwE6FixedA2SL3.eq_zero_of_forall_zpow_eq_one (Ω := Ω)
      intro s
      rw [zpow_sub, hA a b hRab s, mul_inv_cancel]
    exact sub_eq_zero.1 hk
  have hw₂ : diagWt 2 b = diagWt 2 b₁ * diagWt 0 a + diagWt 2 b₂ * diagWt 2 a := by
    have hk : diagWt 2 b - (diagWt 2 b₁ * diagWt 0 a + diagWt 2 b₂ * diagWt 2 a) = 0 := by
      apply CFSG.StandardType.TwE6FixedA2SL3.eq_zero_of_forall_zpow_eq_one (Ω := Ω)
      intro u
      rw [zpow_sub, hB a b hRab u, mul_inv_cancel]
    exact sub_eq_zero.1 hk
  have hweight : (diagWt 0 b, diagWt 2 b) =
      (diagWt 0 b₁ * diagWt 0 a + diagWt 0 b₂ * diagWt 2 a,
        diagWt 2 b₁ * diagWt 0 a + diagWt 2 b₂ * diagWt 2 a) :=
    Prod.ext hw₁ hw₂
  rw [hweight] at hb
  exact (longWeight_weylMatList_apply hμν (diagWt 0 a, diagWt 2 a)).mp hb

theorem normalizer_fixedA2Torus_apply_mem_Vlong
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (R : ModGL .E6 Ω) (hR : R ∈ Subgroup.normalizer (fixedA2Torus Ω))
    {v : RootModule .E6 Ω} (hv : v ∈ Vlong Ω) :
    (R : Module.End Ω (RootModule .E6 Ω)) v ∈ Vlong Ω := by
  classical
  have hsingle : ∀ b : Label .E6, longWeight (diagWt 0 b, diagWt 2 b) →
      (R : Module.End Ω (RootModule .E6 Ω)) (Finsupp.single b 1) ∈ Vlong Ω := by
    intro b hb
    rw [Vlong, Finsupp.mem_supported']
    intro a ha
    by_contra hRab
    exact ha (normalizer_fixedA2Torus_support_long R hR hb hRab)
  have hmap : Submodule.map (R : Module.End Ω (RootModule .E6 Ω)) (Vlong Ω) ≤ Vlong Ω := by
    change Submodule.map (R : Module.End Ω (RootModule .E6 Ω))
      (Finsupp.supported Ω Ω {ℓ : Label .E6 |
        longWeight (diagWt 0 ℓ, diagWt 2 ℓ)}) ≤ Vlong Ω
    rw [Finsupp.supported_eq_span_single, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    exact hsingle b hb
  exact hmap ⟨v, hv, rfl⟩

theorem normalizer_fixedA2Torus_inv_apply_mem_Vlong
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (R : ModGL .E6 Ω) (hR : R ∈ Subgroup.normalizer (fixedA2Torus Ω))
    {v : RootModule .E6 Ω} (hv : v ∈ Vlong Ω) :
    ((R⁻¹ : ModGL .E6 Ω) : Module.End Ω (RootModule .E6 Ω)) v ∈ Vlong Ω :=
  normalizer_fixedA2Torus_apply_mem_Vlong R⁻¹ (Subgroup.inv_mem _ hR) hv

theorem mem_VlongFixer_iff {Ω : Type} [Field Ω] (R : ModGL .E6 Ω) :
    R ∈ VlongFixer Ω ↔ ∀ v ∈ Vlong Ω,
      (R : Module.End Ω (RootModule .E6 Ω)) v = v := by
  rw [VlongFixer, Subgroup.mem_comap, mem_fixingSubgroup_iff]
  constructor
  · intro h v hv
    have h' := h v hv
    rw [LinearEquiv.smul_def] at h'
    change ((LinearMap.GeneralLinearGroup.generalLinearEquiv Ω _) R) v = v at h'
    simpa only [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv] using h'
  · intro h v hv
    rw [LinearEquiv.smul_def]
    change ((LinearMap.GeneralLinearGroup.generalLinearEquiv Ω _) R) v = v
    simpa only [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv] using h v hv

theorem normalizer_Wlong
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {E : Subgroup (ModGL .E6 Ω)} {R : ModGL .E6 Ω}
    (hRE : R ∈ Subgroup.normalizer (E : Set (ModGL .E6 Ω)))
    (hRS : R ∈ Subgroup.normalizer (fixedA2Torus Ω)) :
    R ∈ Subgroup.normalizer (Wlong Ω E : Set (ModGL .E6 Ω)) := by
  classical
  have hRRinv : ∀ v : RootModule .E6 Ω,
      (R : Module.End Ω (RootModule .E6 Ω))
        (((R⁻¹ : ModGL .E6 Ω) : Module.End Ω (RootModule .E6 Ω)) v) = v := by
    intro v
    rw [← Module.End.mul_apply]
    change (((R * R⁻¹ : ModGL .E6 Ω)) : Module.End Ω (RootModule .E6 Ω)) v = v
    rw [mul_inv_cancel, Units.val_one]
    rfl
  have hRinvR : ∀ v : RootModule .E6 Ω,
      (((R⁻¹ : ModGL .E6 Ω) : Module.End Ω (RootModule .E6 Ω))
        ((R : Module.End Ω (RootModule .E6 Ω)) v)) = v := by
    intro v
    rw [← Module.End.mul_apply]
    change ((((R⁻¹ * R : ModGL .E6 Ω)) : Module.End Ω (RootModule .E6 Ω))) v = v
    rw [inv_mul_cancel, Units.val_one]
    rfl
  refine Subgroup.mem_normalizer_iff.mpr fun w => ?_
  constructor
  · intro hw
    rw [Wlong] at hw ⊢
    rw [Subgroup.mem_inf] at hw
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hRE w).mp hw.1
    · rw [mem_VlongFixer_iff] at hw ⊢
      intro v hv
      have hRv : ((R⁻¹ : ModGL .E6 Ω) : Module.End Ω (RootModule .E6 Ω)) v ∈ Vlong Ω :=
        normalizer_fixedA2Torus_inv_apply_mem_Vlong R hRS hv
      change ((R : Module.End Ω (RootModule .E6 Ω)) *
        (w : Module.End Ω (RootModule .E6 Ω)) *
          ((R⁻¹ : ModGL .E6 Ω) : Module.End Ω (RootModule .E6 Ω))) v = v
      rw [Module.End.mul_apply, Module.End.mul_apply, hw.2 _ hRv, hRRinv]
  · intro hw
    rw [Wlong] at hw ⊢
    rw [Subgroup.mem_inf] at hw
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hRE w).mpr hw.1
    · rw [mem_VlongFixer_iff] at hw ⊢
      intro v hv
      have hRv : (R : Module.End Ω (RootModule .E6 Ω)) v ∈ Vlong Ω :=
        normalizer_fixedA2Torus_apply_mem_Vlong R hRS hv
      have hzfix := hw.2 _ hRv
      change ((R : Module.End Ω (RootModule .E6 Ω)) *
        (w : Module.End Ω (RootModule .E6 Ω)) *
          ((R⁻¹ : ModGL .E6 Ω) : Module.End Ω (RootModule .E6 Ω)))
            ((R : Module.End Ω (RootModule .E6 Ω)) v) =
              (R : Module.End Ω (RootModule .E6 Ω)) v at hzfix
      rw [Module.End.mul_apply, Module.End.mul_apply, hRinvR] at hzfix
      have := congrArg (fun x => (((R⁻¹ : ModGL .E6 Ω) : Module.End Ω
        (RootModule .E6 Ω)) x)) hzfix
      simpa only [hRinvR] using this

end CFSG.StandardType.TwE6E4bFlag
