module

public import CFSG.Quasithin.H13.L32AH65a
public import CFSG.Quasithin.H13.L32ASecMod

public section

namespace CFSG.Quasithin.H6

open scoped MatrixGroups

theorem ll_smul_coreU4 : ∀ g : Γ, g ∈ Ll → g • coreU4 = coreU4 := by decide +kernel

theorem coreU4_ne : coreU4 ≠ 0 := by decide

@[expose] def coreH : Γ := ⟨!![0, 1, 0; 1, 0, 1; 0, 0, 1], by decide⟩

@[expose] def coreY1 : Core := ⟨![0, 0, 0, 0, 0, 0, 1, 1], by decide⟩

@[expose] def coreY2 : Core := ⟨![0, 0, 0, 0, 0, 1, 0, 1], by decide⟩

theorem coreH_mem : coreH ∈ Ll := by decide

theorem coreU4_eq_llA :
    coreU4 = (llA • coreY1 - coreY1) + ((coreH * llA * coreH⁻¹) • coreY2 - coreY2) := by
  decide

theorem exists_conj_llA :
    ∀ g : Γ, g ∈ Ll → g ^ 3 = 1 → g ≠ 1 → ∃ h : Γ, h ∈ Ll ∧ g = h * llA * h⁻¹ := by
  decide +kernel

theorem coreU4_decomp {g : Γ} (hg : g ∈ Ll) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ h : Γ, h ∈ Ll ∧ ∃ y₁ y₂ : Core, coreU4 = (g • y₁ - y₁) + ((h * g * h⁻¹) • y₂ - y₂) := by
  obtain ⟨k, hk, rfl⟩ := exists_conj_llA g hg hg3 hg1
  refine ⟨k * coreH * k⁻¹, Ll.mul_mem (Ll.mul_mem hk coreH_mem) (Ll.inv_mem hk),
    k • coreY1, k • coreY2, ?_⟩
  have e1 : ∀ (a : Γ) (y : Core), k • (a • y) = (k * a * k⁻¹) • (k • y) := fun a y => by
    rw [← mul_smul, ← mul_smul, show k * a * k⁻¹ * k = k * a by group]
  have e2 : k * coreH * k⁻¹ * (k * llA * k⁻¹) * (k * coreH * k⁻¹)⁻¹ =
      k * (coreH * llA * coreH⁻¹) * k⁻¹ := by group
  rw [← ll_smul_coreU4 k hk, coreU4_eq_llA, smul_add, smul_sub, smul_sub, e1, e1, e2]

end CFSG.Quasithin.H6

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.H6

variable {G : Type} [Group G]

theorem SecMod.exists_core_fix {L X Y : Subgroup G} {θ : ↥L →* Γ} (D : SecMod L X Y θ)
    [(Y.subgroupOf X).Normal] {ρ : Γ →* AddMonoid.End (Additive (↥X ⧸ Y.subgroupOf X))}
    (hρ : ∀ (l : ↥L) (s : ↥X), ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
      Additive.ofMul (QuotientGroup.mk (D.conjX l s)))
    (hiso : IsoMod ρ ρCore) {x : ↥L} (hxl : θ x ∈ Ll) (hx3 : θ x ^ 3 = 1) (hx1 : θ x ≠ 1) :
    ∃ e : G, (∃ l : ↥L, θ l ∈ Ll ∧ ∃ s₁ ∈ X, ∃ s₂ ∈ X,
        e = ((x : G) * s₁ * (x : G)⁻¹ * s₁⁻¹) * (((l * x * l⁻¹ : ↥L) : G) * s₂ *
          ((l * x * l⁻¹ : ↥L) : G)⁻¹ * s₂⁻¹)) ∧
      e ∉ Y ∧ ∀ l' : ↥L, θ l' ∈ Ll → (l' : G) * e * (l' : G)⁻¹ * e⁻¹ ∈ Y := by
  obtain ⟨f, hfb, hf⟩ := hiso
  obtain ⟨h, hh, y₁, y₂, hy⟩ := coreU4_decomp hxl hx3 hx1
  obtain ⟨l, rfl⟩ := D.surj h
  have hsurj : ∀ m : Additive (↥X ⧸ Y.subgroupOf X), ∃ s : ↥X,
      Additive.ofMul (QuotientGroup.mk s) = m := fun m => by
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (Additive.toMul m)
    exact ⟨s, by rw [hs]; rfl⟩
  obtain ⟨s₁, hs₁⟩ := hsurj (f y₁)
  obtain ⟨s₂, hs₂⟩ := hsurj (f y₂)
  set e' : ↥X := (D.conjX x s₁ * s₁⁻¹) * (D.conjX (l * x * l⁻¹) s₂ * s₂⁻¹) with he'
  have hθ : θ l * θ x * (θ l)⁻¹ = θ (l * x * l⁻¹) := by simp
  have hm₀ : f coreU4 = Additive.ofMul (QuotientGroup.mk e') := by
    rw [hy, map_add, map_sub, map_sub]
    have h1 : f (θ x • y₁) = ρ (θ x) (f y₁) := hf (θ x) y₁
    have h2 : f ((θ l * θ x * (θ l)⁻¹) • y₂) = ρ (θ l * θ x * (θ l)⁻¹) (f y₂) :=
      hf (θ l * θ x * (θ l)⁻¹) y₂
    rw [h1, h2, ← hs₁, ← hs₂, hθ, hρ, hρ, he']
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ofMul_mul, ofMul_inv,
      sub_eq_add_neg]
  have hf0 : ∀ y : Core, f y = 0 → y = 0 := fun y hy0 => hfb.1 (by rw [hy0, map_zero])
  refine ⟨e', ⟨l, hh, s₁, s₁.2, s₂, s₂.2, ?_⟩, ?_, ?_⟩
  · rw [he']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjX]
  · intro he
    apply coreU4_ne
    apply hf0
    rw [hm₀]
    have : (QuotientGroup.mk e' : ↥X ⧸ Y.subgroupOf X) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr he)
    rw [this]
    rfl
  · intro l' hl'
    have h1 : ρ (θ l') (f coreU4) = f coreU4 := by
      rw [← hf]
      exact congrArg f (ll_smul_coreU4 _ hl')
    rw [hm₀, hρ] at h1
    have h2 : (QuotientGroup.mk (D.conjX l' e') : ↥X ⧸ Y.subgroupOf X) = QuotientGroup.mk e' :=
      Additive.ofMul.injective h1
    have h3 := (D.mk_eq_mk_iff _ _).mp h2
    rwa [coe_conjX] at h3

end CFSG.Quasithin.H13.L32A
