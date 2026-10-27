module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Nm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab6

variable {D : Type*} [Group D] {A B : Subgroup D}

@[expose] noncomputable def Fx (V V₂ : Subgroup D) (γ δ : CosetGeom (A ⊔ B) A B) : Subgroup D :=
  Nm A B V V₂ γ ⊓ Subgroup.centralizer (↑(stab γ ⊓ stab δ) : Set D)

theorem mem_Fx {V V₂ : Subgroup D} {γ δ : CosetGeom (A ⊔ B) A B} {x : D} :
    x ∈ Fx V V₂ γ δ ↔ x ∈ Nm A B V V₂ γ ∧ ∀ u ∈ stab γ ⊓ stab δ, u * x = x * u := by
  simp [Fx, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]

variable {V V₂ : Subgroup D}

theorem mem_Fx_smul (hA : A ≤ Subgroup.normalizer (V : Set D))
    (hB : B ≤ Subgroup.normalizer (V₂ : Set D)) (g : ↥(A ⊔ B))
    (γ δ : CosetGeom (A ⊔ B) A B) {x : D} :
    x ∈ Fx V V₂ (g • γ) (g • δ) ↔ (g : D)⁻¹ * x * g ∈ Fx V V₂ γ δ := by
  rw [mem_Fx, mem_Fx, Nm_smul hA hB, mem_conjSub]
  refine and_congr Iff.rfl ⟨fun h u hu => ?_, fun h u hu => ?_⟩
  · have hu' : (g : D) * u * (g : D)⁻¹ ∈ stab (g • γ) ⊓ stab (g • δ) := by
      rw [stab_smul, stab_smul]
      exact ⟨mul_mem_conjSub hu.1, mul_mem_conjSub hu.2⟩
    have := h _ hu'
    calc u * ((g : D)⁻¹ * x * g) = (g : D)⁻¹ * ((g : D) * u * (g : D)⁻¹ * x) * g := by group
      _ = (g : D)⁻¹ * (x * ((g : D) * u * (g : D)⁻¹)) * g := by rw [this]
      _ = (g : D)⁻¹ * x * g * u := by group
  · rw [stab_smul, stab_smul, Subgroup.mem_inf, mem_conjSub, mem_conjSub] at hu
    have := h _ ⟨hu.1, hu.2⟩
    calc u * x = (g : D) * (((g : D)⁻¹ * u * g) * ((g : D)⁻¹ * x * g)) * (g : D)⁻¹ := by group
      _ = (g : D) * (((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * u * g)) * (g : D)⁻¹ := by rw [this]
      _ = x * u := by group

structure GoodV (V V₂ : Subgroup D) (γ : CosetGeom (A ⊔ B) A B) : Prop where
  nm_le : Nm A B V V₂ γ ≤ ballStab 1 γ
  norm : stab γ ≤ Subgroup.normalizer (Nm A B V V₂ γ : Set D)
  sq : ∀ x ∈ Nm A B V V₂ γ, x * x = 1
  comm : ∀ x ∈ Nm A B V V₂ γ, ∀ y ∈ Nm A B V V₂ γ, x * y = y * x
  qv_cent : ∀ q ∈ ballStab 1 γ, ∀ x ∈ Nm A B V V₂ γ, x * q = q * x
  cent_le : ∀ u ∈ stab γ, (∀ x ∈ Nm A B V V₂ γ, x * u = u * x) → u ∈ ballStab 1 γ

structure GoodE (V V₂ : Subgroup D) (γ δ : CosetGeom (A ⊔ B) A B) : Prop where
  nm_le : Nm A B V V₂ γ ≤ ballStab 1 δ
  index : ∀ u₁ u₂, u₁ ∈ stab γ ⊓ stab δ → u₂ ∈ stab γ ⊓ stab δ → u₁ ∉ ballStab 1 γ →
    u₂ ∉ ballStab 1 γ → u₁⁻¹ * u₂ ∈ ballStab 1 γ
  ne : ¬ ballStab 1 γ ≤ ballStab 1 δ
  rel3 : (stab γ ⊓ stab δ).relIndex (stab γ) = 3
  lab : ∃ w : D, (∀ x ∈ Fx V V₂ δ γ, x = 1 ∨ x = w) ∧
    ∀ g ∈ stab γ, g * w * g⁻¹ = w → g ∈ stab δ

theorem relIndex_conjSub_eq (x : D) (K W : Subgroup D) :
    (conjSub x K).relIndex (conjSub x W) = K.relIndex W :=
  Subgroup.relIndex_map_map_of_injective K W (MulAut.conj x).injective

section Transport

variable (hA : A ≤ Subgroup.normalizer (V : Set D)) (hB : B ≤ Subgroup.normalizer (V₂ : Set D))
  (g : ↥(A ⊔ B))

include hA hB

theorem GoodV.smul {γ : CosetGeom (A ⊔ B) A B} (h : GoodV V V₂ γ) : GoodV V V₂ (g • γ) where
  nm_le := by
    rw [Nm_smul hA hB, ballStab_smul]
    exact conjSub_mono _ h.nm_le
  norm := by
    rw [Nm_smul hA hB, stab_smul]
    exact conjSub_le_normalizer h.norm
  sq := fun x hx => by
    rw [Nm_smul hA hB, mem_conjSub] at hx
    have := h.sq _ hx
    calc x * x = (g : D) * (((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * x * g)) * (g : D)⁻¹ := by group
      _ = 1 := by rw [this]; group
  comm := fun x hx y hy => by
    rw [Nm_smul hA hB, mem_conjSub] at hx hy
    have := h.comm _ hx _ hy
    calc x * y = (g : D) * (((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * y * g)) * (g : D)⁻¹ := by group
      _ = (g : D) * (((g : D)⁻¹ * y * g) * ((g : D)⁻¹ * x * g)) * (g : D)⁻¹ := by rw [this]
      _ = y * x := by group
  qv_cent := fun q hq x hx => by
    rw [ballStab_smul, mem_conjSub] at hq
    rw [Nm_smul hA hB, mem_conjSub] at hx
    have := h.qv_cent _ hq _ hx
    calc x * q = (g : D) * (((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * q * g)) * (g : D)⁻¹ := by group
      _ = (g : D) * (((g : D)⁻¹ * q * g) * ((g : D)⁻¹ * x * g)) * (g : D)⁻¹ := by rw [this]
      _ = q * x := by group
  cent_le := fun u hu hc => by
    rw [stab_smul, mem_conjSub] at hu
    rw [ballStab_smul, mem_conjSub]
    refine h.cent_le _ hu fun x hx => ?_
    have hx' : (g : D) * x * (g : D)⁻¹ ∈ Nm A B V V₂ (g • γ) := by
      rw [Nm_smul hA hB]; exact mul_mem_conjSub hx
    have := hc _ hx'
    calc x * ((g : D)⁻¹ * u * g) = (g : D)⁻¹ * ((g : D) * x * (g : D)⁻¹ * u) * g := by group
      _ = (g : D)⁻¹ * (u * ((g : D) * x * (g : D)⁻¹)) * g := by rw [this]
      _ = (g : D)⁻¹ * u * g * x := by group

include hA hB in
theorem GoodE.smul {γ δ : CosetGeom (A ⊔ B) A B} (h : GoodE V V₂ γ δ) :
    GoodE V V₂ (g • γ) (g • δ) where
  nm_le := by
    rw [Nm_smul hA hB, ballStab_smul]
    exact conjSub_mono _ h.nm_le
  index := fun u₁ u₂ h1 h2 n1 n2 => by
    rw [Subgroup.mem_inf, stab_smul, stab_smul, mem_conjSub, mem_conjSub] at h1 h2
    rw [ballStab_smul, mem_conjSub] at n1 n2 ⊢
    have := h.index _ _ ⟨h1.1, h1.2⟩ ⟨h2.1, h2.2⟩ n1 n2
    have e : (g : D)⁻¹ * (u₁⁻¹ * u₂) * g = ((g : D)⁻¹ * u₁ * g)⁻¹ * ((g : D)⁻¹ * u₂ * g) := by
      group
    rw [e]
    exact this
  ne := by
    intro hle
    apply h.ne
    rw [ballStab_smul, ballStab_smul] at hle
    have := conjSub_mono (g : D)⁻¹ hle
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
  rel3 := by
    rw [stab_smul, stab_smul, ← conjSub_inf, relIndex_conjSub_eq]
    exact h.rel3
  lab := by
    obtain ⟨w, hw1, hw2⟩ := h.lab
    refine ⟨(g : D) * w * (g : D)⁻¹, fun x hx => ?_, fun g₂ hg₂ hc => ?_⟩
    · rw [mem_Fx_smul hA hB] at hx
      have e : x = (g : D) * ((g : D)⁻¹ * x * g) * (g : D)⁻¹ := by group
      rcases hw1 _ hx with h1 | h1
      · left
        rw [e, h1]
        group
      · right
        rw [e, h1]
    · rw [stab_smul, mem_conjSub] at hg₂
      rw [stab_smul, mem_conjSub]
      refine hw2 _ hg₂ ?_
      have e : (g : D)⁻¹ * g₂ * g * w * ((g : D)⁻¹ * g₂ * g)⁻¹ =
          (g : D)⁻¹ * (g₂ * ((g : D) * w * (g : D)⁻¹) * g₂⁻¹) * g := by group
      rw [e, hc]
      group

end Transport

end GoldAmLab6

end F6

end CFSG.Quasithin
