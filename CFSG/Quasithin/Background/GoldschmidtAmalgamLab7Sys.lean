module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

structure TwoSys (A B : Subgroup D) (z : D) (V : Subgroup D) (c : D) (V₂ : Subgroup D) : Prop where
  gold : GoldHyp A B
  card_ge : 32 ≤ Nat.card ↥(A ⊓ B)
  nat : IsNaturalAt A (A ⊓ B) z V
  nat₂ : IsNaturalAt B (A ⊓ B) c V₂
  V_le : V ≤ pCoreOf 2 B
  V₂_le : V₂ ≤ pCoreOf 2 A

structure GoodE0 (V V₂ : Subgroup D) (γ δ : CosetGeom (A ⊔ B) A B) : Prop where
  nm_le : Nm A B V V₂ γ ≤ ballStab 1 δ
  index : ∀ u₁ u₂, u₁ ∈ stab γ ⊓ stab δ → u₂ ∈ stab γ ⊓ stab δ → u₁ ∉ ballStab 1 γ →
    u₂ ∉ ballStab 1 γ → u₁⁻¹ * u₂ ∈ ballStab 1 γ
  ne : ¬ ballStab 1 γ ≤ ballStab 1 δ
  rel3 : (stab γ ⊓ stab δ).relIndex (stab γ) = 3
  lab : ∃ w : D, w ≠ 1 ∧ w ∈ Fx V V₂ γ δ ∧ ∀ x ∈ Fx V V₂ γ δ, x = 1 ∨ x = w

section Transport

variable (hA : A ≤ Subgroup.normalizer (V : Set D)) (hB : B ≤ Subgroup.normalizer (V₂ : Set D))
  (g : ↥(A ⊔ B))

include hA hB in
theorem GoodE0.smul {γ δ : CosetGeom (A ⊔ B) A B} (h : GoodE0 V V₂ γ δ) :
    GoodE0 V V₂ (g • γ) (g • δ) where
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
    obtain ⟨w, hw1, hwF, hw2⟩ := h.lab
    refine ⟨(g : D) * w * (g : D)⁻¹, fun e => hw1 ?_, ?_, fun x hx => ?_⟩
    · have : w = (g : D)⁻¹ * ((g : D) * w * (g : D)⁻¹) * g := by group
      rw [this, e]
      group
    · rw [mem_Fx_smul hA hB]
      have e : (g : D)⁻¹ * ((g : D) * w * (g : D)⁻¹) * g = w := by group
      rw [e]
      exact hwF
    · rw [mem_Fx_smul hA hB] at hx
      have e : x = (g : D) * ((g : D)⁻¹ * x * g) * (g : D)⁻¹ := by group
      rcases hw2 _ hx with h1 | h1
      · left
        rw [e, h1]
        group
      · right
        rw [e, h1]

end Transport

variable [Finite D]

theorem goodV_γ₀ (h : TwoSys A B z V c V₂) : GoodV V V₂ (γ₀ (A ⊔ B) A B) := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have e1 : stab (γ₀ (A ⊔ B) A B) = A := stab_γ₀ le_sup_left
  have e2 : Nm A B V V₂ (γ₀ (A ⊔ B) A B) = V := Nm_γ₀ hA
  have e3 := ballStab_one_γ₀_eq h.gold
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2, e3]
    intro x hx
    exact (h.nat.le_center hx).1
  · rw [e1, e2]
    exact hA
  · intro x hx
    rw [e2] at hx
    have := isElemAbelian_pow_eq_one h.nat.reduced.2.2.1 hx
    rwa [pow_two] at this
  · intro x hx y hy
    rw [e2] at hx hy
    exact isElemAbelian_comm h.nat.reduced.2.2.1 hx hy
  · intro q hq x hx
    rw [e3] at hq
    rw [e2] at hx
    exact (Subgroup.mem_centralizer_iff.mp (h.nat.le_center hx).2 q hq).symm
  · intro u hu hc
    rw [e1] at hu
    rw [e2] at hc
    rw [e3, ← h.nat.centralizer_eq]
    exact ⟨hu, Subgroup.mem_centralizer_iff.mpr hc⟩

theorem goodV_γ₁ (h : TwoSys A B z V c V₂) : GoodV V V₂ (γ₁ (A ⊔ B) A B) := by
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  have e1 : stab (γ₁ (A ⊔ B) A B) = B := stab_γ₁ le_sup_right
  have e2 : Nm A B V V₂ (γ₁ (A ⊔ B) A B) = V₂ := Nm_γ₁ hB
  have e3 := ballStab_one_γ₁_eq h.gold
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2, e3]
    intro x hx
    exact (h.nat₂.le_center hx).1
  · rw [e1, e2]
    exact hB
  · intro x hx
    rw [e2] at hx
    have := isElemAbelian_pow_eq_one h.nat₂.reduced.2.2.1 hx
    rwa [pow_two] at this
  · intro x hx y hy
    rw [e2] at hx hy
    exact isElemAbelian_comm h.nat₂.reduced.2.2.1 hx hy
  · intro q hq x hx
    rw [e3] at hq
    rw [e2] at hx
    exact (Subgroup.mem_centralizer_iff.mp (h.nat₂.le_center hx).2 q hq).symm
  · intro u hu hc
    rw [e1] at hu
    rw [e2] at hc
    rw [e3, ← h.nat₂.centralizer_eq]
    exact ⟨hu, Subgroup.mem_centralizer_iff.mpr hc⟩

end GoldAmLab7

end F6

end CFSG.Quasithin
