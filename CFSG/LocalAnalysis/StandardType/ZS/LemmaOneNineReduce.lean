module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineRestrict
public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineThree

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem homology_maps_mem {τ : K} {g : V ≃ₗ[K] V} {c : V} {φ : Module.Dual K V}
    {M : Submodule K V} (h : IsHomologyWith τ g c φ) (hc : c ∈ M) : ∀ m ∈ M, g m ∈ M := by
  intro m hm
  rw [h.2 m]
  exact M.add_mem hm (M.smul_mem (φ m) hc)

private theorem homology_maps_mem_inv {τ : K} {g : V ≃ₗ[K] V} {c : V} {φ : Module.Dual K V}
    {M : Submodule K V} (h : IsHomologyWith τ g c φ) (hc : c ∈ M) : ∀ m ∈ M, g⁻¹ m ∈ M :=
  homology_maps_mem h.inv hc

private theorem linearEquiv_ext_of_isCompl {A B : Submodule K V} (h : IsCompl A B)
    {f g : V ≃ₗ[K] V} (hA : ∀ a ∈ A, f a = g a) (hB : ∀ b ∈ B, f b = g b) : f = g := by
  ext v
  have hv : v ∈ A ⊔ B := by
    rw [codisjoint_iff.mp h.codisjoint]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
  rw [← hab, map_add, map_add, hA a ha, hB b hb]

end Field

variable {p : ℕ} [Fact p.Prime] {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
  {H : Subgroup (U ≃ₗ[ZMod p] U)} {τ : ZMod p} {α β γ : U ≃ₗ[ZMod p] U} {c₁ c₂ w y : U}
  {φ₁ φ₂ φ : Module.Dual (ZMod p) U}

private theorem mc_invariant {M Y₃ : Submodule (ZMod p) U}
    (h₁ : IsHomologyWith τ α c₁ φ₁) (h₂ : IsHomologyWith τ β c₂ φ₂)
    (hγh : IsHomologyWith τ γ (w + y) φ)
    (hc1M : c₁ ∈ M) (hc2M : c₂ ∈ M) (hcγmemM : w + y ∈ M)
    (hY₃ker₁ : Y₃ ≤ LinearMap.ker φ₁) (hY₃ker₂ : Y₃ ≤ LinearMap.ker φ₂)
    (hY₃kerφ : Y₃ ≤ LinearMap.ker φ) :
    ∀ g ∈ Subgroup.closure ({α, β, γ} : Set (U ≃ₗ[ZMod p] U)),
      (∀ m ∈ M, g m ∈ M) ∧ (∀ m ∈ M, g⁻¹ m ∈ M) ∧ (∀ z ∈ Y₃, g z = z) := by
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ =>
    (∀ m ∈ M, g m ∈ M) ∧ (∀ m ∈ M, g⁻¹ m ∈ M) ∧ (∀ z ∈ Y₃, g z = z)) ?_ ?_ ?_ ?_ hg
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨homology_maps_mem h₁ hc1M, homology_maps_mem_inv h₁ hc1M,
        fun z hz => h₁.apply_of_apply_eq_zero (LinearMap.mem_ker.mp (hY₃ker₁ hz))⟩
    · exact ⟨homology_maps_mem h₂ hc2M, homology_maps_mem_inv h₂ hc2M,
        fun z hz => h₂.apply_of_apply_eq_zero (LinearMap.mem_ker.mp (hY₃ker₂ hz))⟩
    · exact ⟨homology_maps_mem hγh hcγmemM, homology_maps_mem_inv hγh hcγmemM,
        fun z hz => hγh.apply_of_apply_eq_zero (LinearMap.mem_ker.mp (hY₃kerφ hz))⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro m hm; simpa using hm
    · intro m hm; simpa using hm
    · intro z hz; rfl
  · intro x y hx hy px py
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      rw [LinearEquiv.mul_apply]
      exact px.1 (y m) (py.1 m hm)
    · intro m hm
      rw [mul_inv_rev, LinearEquiv.mul_apply]
      exact py.2.1 (x⁻¹ m) (px.2.1 m hm)
    · intro z hz
      rw [LinearEquiv.mul_apply, py.2.2 z hz, px.2.2 z hz]
  · intro x hx px
    refine ⟨px.2.1, by simpa using px.1, ?_⟩
    intro z hz
    calc x⁻¹ z = x⁻¹ (x z) := by rw [px.2.2 z hz]
      _ = z := LinearEquiv.symm_apply_apply x z

private theorem mc_members {W Y M Y₃ : Submodule (ZMod p) U}
    (hW : W = Submodule.span (ZMod p) {c₁, c₂}) (hY : Y = LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂)
    (hM : M = W ⊔ Submodule.span (ZMod p) {y}) (hY₃ : Y₃ = Y ⊓ LinearMap.ker φ)
    (hw : w ∈ Submodule.span (ZMod p) {c₁, c₂}) :
    c₁ ∈ M ∧ c₂ ∈ M ∧ w ∈ M ∧ y ∈ M ∧ w + y ∈ M ∧
      Y₃ ≤ LinearMap.ker φ₁ ∧ Y₃ ≤ LinearMap.ker φ₂ ∧ Y₃ ≤ LinearMap.ker φ := by
  have hc1M : c₁ ∈ M := by
    rw [hM, hW]
    exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
  have hc2M : c₂ ∈ M := by
    rw [hM, hW]
    exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
  have hwmemM : w ∈ M := by
    rw [hM, hW]
    exact Submodule.mem_sup_left hw
  have hymemM : y ∈ M := by
    rw [hM]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
  have hcγmemM : w + y ∈ M := M.add_mem hwmemM hymemM
  have hY₃ker₁ : Y₃ ≤ LinearMap.ker φ₁ := by
    rw [hY₃, hY]
    exact inf_le_left.trans inf_le_left
  have hY₃ker₂ : Y₃ ≤ LinearMap.ker φ₂ := by
    rw [hY₃, hY]
    exact inf_le_left.trans inf_le_right
  have hY₃kerφ : Y₃ ≤ LinearMap.ker φ := by
    rw [hY₃]
    exact inf_le_right
  exact ⟨hc1M, hc2M, hwmemM, hymemM, hcγmemM, hY₃ker₁, hY₃ker₂, hY₃kerφ⟩

private theorem mc_basic (htv : QTwoLin.TransvectionFree H) (hτ : 4 ≤ orderOf τ)
    (hα : α ∈ H) (hβ : β ∈ H) (h₁ : IsHomologyWith τ α c₁ φ₁)
    (h₂ : IsHomologyWith τ β c₂ φ₂) (hcomm : α * β ≠ β * α) (hy₁ : φ₁ y = 0)
    (hy₂ : φ₂ y = 0) (hφy : φ y ≠ 0) {W Y M Y₃ : Submodule (ZMod p) U}
    (hW : W = Submodule.span (ZMod p) {c₁, c₂}) (hY : Y = LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂)
    (hM : M = W ⊔ Submodule.span (ZMod p) {y}) (hY₃ : Y₃ = Y ⊓ LinearMap.ker φ) :
    ∃ ψ : U ≃ₗ[ZMod p] U,
      y ≠ 0 ∧ τ ≠ 1 ∧ τ ^ 2 ≠ 1 ∧ y ∈ Y ∧ IsCompl W Y ∧ IsCompl M Y₃ ∧
      ψ ∈ Subgroup.closure ({α, β, γ} : Set _) ∧ (∀ v ∈ W, ψ v = τ • v) ∧
      (∀ v, φ₁ v = 0 → φ₂ v = 0 → ψ v = v) := by
  have hy0 : y ≠ 0 := fun h => hφy (by rw [h]; exact map_zero φ)
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτ
    omega
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    have hle : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hYmem : y ∈ Y := by
    rw [hY]
    exact ⟨hy₁, hy₂⟩
  have hlink := linked_of_not_commute htv hα hβ h₁ h₂ hτ2 hcomm
  have hWY : IsCompl W Y := by
    rw [hW, hY]
    exact isCompl_span_ker_inf_ker h₁ h₂ hlink.2.2.2
  have hMY : IsCompl M Y₃ := by
    rw [hM, hY₃]
    exact isCompl_sup_span_inf_ker hWY hYmem hφy
  obtain ⟨ψ, hψS', hψW, hψY⟩ :=
    exists_eq_smul_on_span_of_not_commute htv hα hβ h₁ h₂ hτ hcomm
  have hABsub : ({α, β} : Set (U ≃ₗ[ZMod p] U)) ⊆ ({α, β, γ} : Set _) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hψS : ψ ∈ Subgroup.closure ({α, β, γ} : Set _) :=
    Subgroup.closure_mono hABsub hψS'
  have hψW' : ∀ v ∈ W, ψ v = τ • v := by
    intro v hv
    exact hψW v (by simpa [hW] using hv)
  exact ⟨ψ, hy0, hτ1, hτ2, hYmem, hWY, hMY, hψS, hψW', hψY⟩

theorem false_of_mixed_centre_of_apply_ne_zero (htv : QTwoLin.TransvectionFree H)
    (hτ : 4 ≤ orderOf τ) (hα : α ∈ H) (hβ : β ∈ H) (hγ : γ ∈ H)
    (h₁ : IsHomologyWith τ α c₁ φ₁) (h₂ : IsHomologyWith τ β c₂ φ₂)
    (hγh : IsHomologyWith τ γ (w + y) φ) (hcomm : α * β ≠ β * α)
    (hw : w ∈ Submodule.span (ZMod p) {c₁, c₂}) (hy₁ : φ₁ y = 0) (hy₂ : φ₂ y = 0)
    (hφw : φ w ≠ 0) (hφy : φ y ≠ 0) : False := by
  set W : Submodule (ZMod p) U := Submodule.span (ZMod p) {c₁, c₂} with hWdef
  set Y : Submodule (ZMod p) U := LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂ with hYdef
  set M : Submodule (ZMod p) U := W ⊔ Submodule.span (ZMod p) {y} with hMdef
  set Y₃ : Submodule (ZMod p) U := Y ⊓ LinearMap.ker φ with hY₃def
  obtain ⟨ψ, hy0, hτ1, hτ2, hYmem, hWY, hMY, hψS, hψW, hψY⟩ :=
    mc_basic (γ := γ) htv hτ hα hβ h₁ h₂ hcomm hy₁ hy₂ hφy hWdef hYdef hMdef hY₃def
  let S : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure ({α, β, γ} : Set _)
  obtain ⟨hc1M, hc2M, hwmemM, hymemM, hcγmemM, hY₃ker₁, hY₃ker₂, hY₃kerφ⟩ :=
    mc_members hWdef hYdef hMdef hY₃def hw
  have hP : ∀ g ∈ S, (∀ m ∈ M, g m ∈ M) ∧ (∀ m ∈ M, g⁻¹ m ∈ M) ∧
      (∀ z ∈ Y₃, g z = z) := by
    intro g hg
    exact mc_invariant h₁ h₂ hγh hc1M hc2M hcγmemM hY₃ker₁ hY₃ker₂ hY₃kerφ g hg
  have hMS : ∀ r ∈ S, ∀ m ∈ M, r m ∈ M := fun r hr m hm => (hP r hr).1 m hm
  have hYfix : ∀ r ∈ S, ∀ z ∈ Y₃, r z = z := fun r hr z hz => (hP r hr).2.2 z hz
  have hαS : α ∈ S := Subgroup.subset_closure (by simp)
  have hβS : β ∈ S := Subgroup.subset_closure (by simp)
  have hγS : γ ∈ S := Subgroup.subset_closure (by simp)
  have hSH : S ≤ H := by
    change Subgroup.closure ({α, β, γ} : Set _) ≤ H
    refine (Subgroup.closure_le H).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  let R : Subgroup (M ≃ₗ[ZMod p] M) := scalarHull (ZS.restrictHom S M hMS).range
  have htvR : QTwoLin.TransvectionFree R :=
    transvectionFree_scalarHull_range_restrictHom htv hSH hMY hMS hYfix
  let αM : M ≃ₗ[ZMod p] M := ZS.restrictHom S M hMS ⟨α, hαS⟩
  let βM : M ≃ₗ[ZMod p] M := ZS.restrictHom S M hMS ⟨β, hβS⟩
  let γM : M ≃ₗ[ZMod p] M := ZS.restrictHom S M hMS ⟨γ, hγS⟩
  let ψM : M ≃ₗ[ZMod p] M := ZS.restrictHom S M hMS ⟨ψ, hψS⟩
  have h₁M : IsHomologyWith τ αM ⟨c₁, hc1M⟩ (φ₁ ∘ₗ M.subtype) :=
    IsHomologyWith.restrict (R := S) (M := M) (g := ⟨α, hαS⟩) hMS h₁ hc1M
  have h₂M : IsHomologyWith τ βM ⟨c₂, hc2M⟩ (φ₂ ∘ₗ M.subtype) :=
    IsHomologyWith.restrict (R := S) (M := M) (g := ⟨β, hβS⟩) hMS h₂ hc2M
  have hγM : IsHomologyWith τ γM ⟨w + y, hcγmemM⟩ (φ ∘ₗ M.subtype) :=
    IsHomologyWith.restrict (R := S) (M := M) (g := ⟨γ, hγS⟩) hMS hγh hcγmemM
  have hτ0 : τ ≠ 0 := hγh.type_ne_zero
  let u : (ZMod p)ˣ := Units.mk0 τ hτ0
  let θM : M ≃ₗ[ZMod p] M :=
    (LinearEquiv.smulOfUnit u : M ≃ₗ[ZMod p] M) * ψM⁻¹
  have hαrange : αM ∈ (ZS.restrictHom S M hMS).range := ⟨⟨α, hαS⟩, rfl⟩
  have hβrange : βM ∈ (ZS.restrictHom S M hMS).range := ⟨⟨β, hβS⟩, rfl⟩
  have hγrange : γM ∈ (ZS.restrictHom S M hMS).range := ⟨⟨γ, hγS⟩, rfl⟩
  have hψrange : ψM ∈ (ZS.restrictHom S M hMS).range := ⟨⟨ψ, hψS⟩, rfl⟩
  have hαR : αM ∈ R := le_scalarHull _ hαrange
  have hβR : βM ∈ R := le_scalarHull _ hβrange
  have hγR : γM ∈ R := le_scalarHull _ hγrange
  have hθR : θM ∈ R := by
    have hψinv : ψM⁻¹ ∈ (ZS.restrictHom S M hMS).range := Subgroup.inv_mem _ hψrange
    have hψinvR : ψM⁻¹ ∈ R := le_scalarHull _ hψinv
    have hsmul : (LinearEquiv.smulOfUnit u : M ≃ₗ[ZMod p] M) ∈ R :=
      smulOfUnit_mem_scalarHull _ u
    exact R.mul_mem hsmul hψinvR
  let W' : Submodule (ZMod p) M := W.comap M.subtype
  have hspanyY : Submodule.span (ZMod p) {y} ≤ Y := by
    rw [Submodule.span_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact hYmem
  have hWspany : W ⊓ Submodule.span (ZMod p) {y} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hvin : v ∈ W ⊓ Y := ⟨hv.1, hspanyY hv.2⟩
    rw [disjoint_iff.mp hWY.disjoint] at hvin
    simpa using hvin
  have hWM : W ≤ M := by rw [hMdef]; exact le_sup_left
  have hspanM : Submodule.span (ZMod p) {y} ≤ M := by rw [hMdef]; exact le_sup_right
  have hcomap_span : (Submodule.span (ZMod p) {y}).comap M.subtype =
      Submodule.span (ZMod p) {⟨y, hymemM⟩} := by
    ext v
    rw [Submodule.mem_comap, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  have hW'Y' : IsCompl W' (Submodule.span (ZMod p) {⟨y, hymemM⟩}) := by
    rw [← hcomap_span]
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro v hv
      have hvin : (v : U) ∈ W ⊓ Submodule.span (ZMod p) {y} := ⟨hv.1, hv.2⟩
      have hzero : (v : U) = 0 := (Submodule.eq_bot_iff _).mp hWspany (v : U) hvin
      exact Subtype.ext hzero
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro v
      obtain ⟨a, haW, b, hbS, hab⟩ := Submodule.mem_sup.mp (show (v : U) ∈ W ⊔
        Submodule.span (ZMod p) {y} from v.2)
      have haM : a ∈ M := hWM haW
      have hbM : b ∈ M := hspanM hbS
      exact Submodule.mem_sup.mpr ⟨⟨a, haM⟩, haW, ⟨b, hbM⟩, hbS, Subtype.ext hab⟩
  have hψW' : ∀ w ∈ W', ψM w = (u : ZMod p) • w := by
    intro w hw
    apply Subtype.ext
    simp only [SetLike.val_smul]
    exact hψW (w : U) hw
  have hψWinv : ∀ w ∈ W', ψM⁻¹ w = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) • w := by
    intro w hw
    change ψM.symm w = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) • w
    rw [LinearEquiv.symm_apply_eq]
    rw [hψW' (((u⁻¹ : (ZMod p)ˣ) : ZMod p) • w) (W'.smul_mem _ hw), smul_smul,
      Units.mul_inv, one_smul]
  have hθW' : ∀ w ∈ W', θM w = w := by
    intro w hw
    change (LinearEquiv.smulOfUnit u : M ≃ₗ[ZMod p] M) (ψM⁻¹ w) = w
    rw [hψWinv w hw]
    change (u : ZMod p) • (((u⁻¹ : (ZMod p)ˣ) : ZMod p) • w) = w
    rw [smul_smul, Units.mul_inv, one_smul]
  have hψMy : ψM ⟨y, hymemM⟩ = ⟨y, hymemM⟩ := by
    apply Subtype.ext
    rw [ZS.restrictHom_apply]
    exact hψY y hy₁ hy₂
  have hψMiny : ψM⁻¹ ⟨y, hymemM⟩ = ⟨y, hymemM⟩ := by
    have h := LinearEquiv.symm_apply_apply ψM ⟨y, hymemM⟩
    rwa [hψMy] at h
  have hθy : θM ⟨y, hymemM⟩ = τ • (⟨y, hymemM⟩ : M) := by
    change (LinearEquiv.smulOfUnit u : M ≃ₗ[ZMod p] M) (ψM⁻¹ (⟨y, hymemM⟩ : M)) =
      τ • (⟨y, hymemM⟩ : M)
    rw [hψMiny]
    change (u : ZMod p) • (⟨y, hymemM⟩ : M) = τ • (⟨y, hymemM⟩ : M)
    rw [Units.val_mk0]
  have hymemM_ne0 : (⟨y, hymemM⟩ : M) ≠ 0 := by
    intro h
    exact hy0 (Subtype.ext_iff.mp h)
  obtain ⟨χ, hθh, hχW⟩ :=
    exists_isHomologyWith_of_isCompl (g := θM) hymemM_ne0 hW'Y' hθW' hθy
  have hc1W' : (⟨c₁, hc1M⟩ : M) ∈ W' := by
    change (⟨c₁, hc1M⟩ : M) ∈ W.comap M.subtype
    rw [Submodule.mem_comap]
    exact Submodule.subset_span (by simp)
  have hc2W' : (⟨c₂, hc2M⟩ : M) ∈ W' := by
    change (⟨c₂, hc2M⟩ : M) ∈ W.comap M.subtype
    rw [Submodule.mem_comap]
    exact Submodule.subset_span (by simp)
  have hχ₁ : χ ⟨c₁, hc1M⟩ = 0 := hχW ⟨c₁, hc1M⟩ hc1W'
  have hχ₂ : χ ⟨c₂, hc2M⟩ = 0 := hχW ⟨c₂, hc2M⟩ hc2W'
  have hwinspanM : (⟨w, hwmemM⟩ : M) ∈
      Submodule.span (ZMod p) {⟨c₁, hc1M⟩, ⟨c₂, hc2M⟩} := by
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
    refine Submodule.mem_span_pair.mpr ⟨a, b, ?_⟩
    ext
    exact hab
  have hy₁M : (φ₁ ∘ₗ M.subtype) ⟨y, hymemM⟩ = 0 := by
    change φ₁ y = 0
    exact hy₁
  have hy₂M : (φ₂ ∘ₗ M.subtype) ⟨y, hymemM⟩ = 0 := by
    change φ₂ y = 0
    exact hy₂
  have hφwM : (φ ∘ₗ M.subtype) ⟨w, hwmemM⟩ ≠ 0 := by
    change φ w ≠ 0
    exact hφw
  have hφyM : (φ ∘ₗ M.subtype) ⟨y, hymemM⟩ ≠ 0 := by
    change φ y ≠ 0
    exact hφy
  have hcommM : αM * βM ≠ βM * αM := by
    intro h
    apply hcomm
    refine linearEquiv_ext_of_isCompl hMY ?_ ?_
    · intro m hm
      have h1 : ((αM * βM) ⟨m, hm⟩ : M) = ((βM * αM) ⟨m, hm⟩ : M) :=
        congrArg (fun e : M ≃ₗ[ZMod p] M => e ⟨m, hm⟩) h
      have h2 := congrArg (fun x : M => (x : U)) h1
      simpa [αM, βM, LinearEquiv.mul_apply, ZS.restrictHom_apply] using h2
    · intro z hz
      simp [LinearEquiv.mul_apply, hYfix β hβS z hz, hYfix α hαS z hz]
  exact false_of_mixed_centre htvR hτ hαR hβR hθR hγR h₁M h₂M hθh hγM hcommM
    hy₁M hy₂M hχ₁ hχ₂ hwinspanM hφwM hφyM

end CFSG.StandardType.ZS

end
