module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.EmptyFaithful.S152FinChief

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

theorem four_le_relIndex_of_three [Finite G] {F N : Subgroup G} (hN : IsPGroup 2 N) {n₁ n₂ : G}
    (h₁ : n₁ ∈ N) (h₂ : n₂ ∈ N) (h₃ : n₁ ∉ F) (h₄ : n₂ ∉ F) (h₅ : n₁ * n₂⁻¹ ∉ F) :
    4 ≤ F.relIndex N := by
  have hk := E3.relIndex_eq_two_pow hN F
  by_contra hlt
  push Not at hlt
  have hk' : E3.mQuot N F = 0 ∨ E3.mQuot N F = 1 := by
    by_contra hcon
    push Not at hcon
    have h2 : 2 ≤ E3.mQuot N F := by omega
    have : 2 ^ 2 ≤ 2 ^ E3.mQuot N F := Nat.pow_le_pow_right (by norm_num) h2
    omega
  rcases hk' with h0 | h1
  · have : F.relIndex N = 1 := by rw [hk, h0]; rfl
    exact h₃ (Subgroup.relIndex_eq_one.mp this h₁)
  · have h2 : F.relIndex N = 2 := by rw [hk, h1]; rfl
    obtain ⟨a, haN, ha⟩ := Subgroup.relIndex_eq_two_iff.mp h2
    have e₁ : n₁ * a ∈ F := by
      rcases ha n₁ h₁ with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h h₃
    have e₂ : n₂ * a ∈ F := by
      rcases ha n₂ h₂ with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h h₄
    apply h₅
    have : n₁ * n₂⁻¹ = (n₁ * a) * (n₂ * a)⁻¹ := by group
    rw [this]
    exact F.mul_mem e₁ (F.inv_mem e₂)

theorem four_le_relIndex_of_not_mem_base [Finite G] {H U L N X X₁ F₁ B : Subgroup G}
    (hU : IsElemAbelian 2 U) (hs : IsChiefStep H U L N) (hXH : X ≤ H)
    (hLX₁ : L ≤ X₁) (hX₁N : X₁ ≤ N) (h4 : L.relIndex X₁ = 4)
    (hBH : ∀ σ ∈ H, ∀ b ∈ B, σ * b * σ⁻¹ ∈ B)
    (hBX : ∀ b ∈ B, ∀ x ∈ X₁, b * x * b⁻¹ ∈ X₁)
    (hF₁B : F₁ ≤ B)
    (hIL : ∀ Y : Subgroup G, L ≤ Y → Y ≤ X₁ → (∀ f ∈ F₁, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) →
      Y = L ∨ Y = X₁)
    (hStab : ∀ σ ∈ H, (∀ x ∈ X₁, σ * x * σ⁻¹ ∈ X₁) → σ ∈ B)
    {σ : G} (hσX : σ ∈ X) (hσB : σ ∉ B) :
    4 ≤ (fixU H U L N X hU hs).relIndex N := by
  have hNU : N ≤ U := hs.1.1
  have hLN : L ≤ N := hs.2.2.1.le
  have hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a :=
    fun _ ha _ hb => F7.isElemAbelian_comm hU (hNU ha) (hNU hb)
  have hLL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_isNormalIn hs.2.1
  have hσH : σ ∈ H := hXH hσX
  have hN2 : IsPGroup 2 N := (F7.isPGroup_of_isElemAbelian hU).to_le hNU
  have hFdef : fixU H U L N X hU hs = fixMod X L N hab hLN := rfl
  rw [hFdef]
  set F : Subgroup G := fixMod X L N hab hLN with hF
  by_contra hlt
  push Not at hlt
  have hF2 : F.relIndex N ≤ 2 := by
    have hk := E3.relIndex_eq_two_pow hN2 F
    by_contra hgt
    push Not at hgt
    rcases Nat.lt_or_ge (E3.mQuot N F) 2 with h | h
    · have : 2 ^ E3.mQuot N F ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have : 2 ^ 2 ≤ 2 ^ E3.mQuot N F := Nat.pow_le_pow_right (by norm_num) h
      omega
  have hLF : L ≤ F := le_fixMod (hXH.trans hLL)
  have hY₀idx : (F ⊓ X₁).relIndex X₁ ≤ 2 := by
    rw [Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right hX₁N Subgroup.index_ne_zero_of_finite).trans hF2
  have hLY₀ : L ≤ F ⊓ X₁ := le_inf hLF hLX₁
  have hY₀ne : F ⊓ X₁ ≠ L := by
    intro h
    rw [h, h4] at hY₀idx
    omega
  have hσinv : ∀ y : G, y ∈ L → σ⁻¹ * y * σ ∈ L := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.mp (hLL (H.inv_mem hσH)) y).mp hy
    simpa using this
  have hY₀Y' : F ⊓ X₁ ≤ X₁ ⊓ conjSub σ X₁ := by
    intro y hy
    refine ⟨hy.2, mem_conjSub.mpr ?_⟩
    obtain ⟨-, hfix⟩ := mem_fixMod.mp hy.1
    have hl : σ * y * σ⁻¹ * y⁻¹ ∈ L := hfix σ hσX
    have e : σ⁻¹ * y * σ = (σ⁻¹ * (σ * y * σ⁻¹ * y⁻¹) * σ)⁻¹ * y := by group
    rw [e]
    exact X₁.mul_mem (X₁.inv_mem (hLX₁ (hσinv _ hl))) hy.2
  have hLY' : L ≤ X₁ ⊓ conjSub σ X₁ := by
    intro l hl
    exact ⟨hLX₁ hl, mem_conjSub.mpr (hLX₁ (hσinv l hl))⟩
  have hinvY' : ∀ f ∈ F₁, ∀ y ∈ X₁ ⊓ conjSub σ X₁, f * y * f⁻¹ ∈ X₁ ⊓ conjSub σ X₁ := by
    intro f hf y hy
    refine ⟨hBX f (hF₁B hf) y hy.1, mem_conjSub.mpr ?_⟩
    have hyσ : σ⁻¹ * y * σ ∈ X₁ := mem_conjSub.mp hy.2
    have hb : σ⁻¹ * f * σ⁻¹⁻¹ ∈ B := hBH σ⁻¹ (H.inv_mem hσH) f (hF₁B hf)
    have := hBX _ hb _ hyσ
    have e : σ⁻¹ * (f * y * f⁻¹) * σ =
        (σ⁻¹ * f * σ⁻¹⁻¹) * (σ⁻¹ * y * σ) * (σ⁻¹ * f * σ⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact this
  rcases hIL _ hLY' inf_le_left hinvY' with hY'L | hY'X
  · exact hY₀ne (le_antisymm (hY'L ▸ hY₀Y') hLY₀)
  · have hX₁σ : X₁ ≤ conjSub σ X₁ := fun x hx => by
      have : x ∈ X₁ ⊓ conjSub σ X₁ := by rw [hY'X]; exact hx
      exact this.2
    have heq : X₁ = conjSub σ X₁ :=
      Subgroup.eq_of_le_of_card_ge hX₁σ
        (Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj σ))).le
    apply hσB
    refine hStab σ hσH fun x hx => ?_
    rw [heq]
    exact mul_mem_conjSub hx

end S152Fin

end CFSG.Quasithin
