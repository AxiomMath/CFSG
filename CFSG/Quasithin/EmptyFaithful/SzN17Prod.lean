module

public import CFSG.Quasithin.EmptyFaithful.SzN17Basic
public import CFSG.Quasithin.EmptyFaithful.S153LComp

public section

namespace CFSG.Quasithin.SzN17

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {Ω : Type} [Group Ω]

@[expose] def CenterTrivial (G : Subgroup Ω) : Prop := ∀ a ∈ G, (∀ g ∈ G, g * a = a * g) → a = 1

theorem normalThree_le_factor {A B Q : Subgroup Ω} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) (hA : CenterTrivial A) (hQ : IsNormalThree (A ⊔ B) Q) :
    Q ≤ A ∨ Q ≤ B := by
  obtain ⟨hQH, hQn, hQc⟩ := hQ
  obtain ⟨z, hzQ, hz1⟩ := exists_ne_one_of_card_three hQc
  obtain ⟨hz3, hQz⟩ := eq_zpowers_of_card_three hQc hzQ hz1
  obtain ⟨-, hcases⟩ := card_three_cases hQc hzQ hz1
  obtain ⟨a, ha, b, hb, rfl⟩ := S153L.comp_exists_mul hc (hQH hzQ)
  have hab : Commute a b := hc a ha b hb
  have hcube : (a * b) ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one _
  have h33 : a ^ 3 * b ^ 3 = 1 := by rw [← hab.mul_pow]; exact hcube
  have ha3 : a ^ 3 = 1 := by
    have hmem : a ^ 3 ∈ A ⊓ B := ⟨A.pow_mem ha 3, by
      rw [eq_inv_of_mul_eq_one_left h33]; exact B.inv_mem (B.pow_mem hb 3)⟩
    rwa [hinf, Subgroup.mem_bot] at hmem
  have hb3 : b ^ 3 = 1 := by rwa [ha3, one_mul] at h33
  have key : ∀ g₁ ∈ A, g₁ * a * g₁⁻¹ = a ∨ b = 1 := by
    intro g₁ hg₁
    have hg₁H : g₁ ∈ A ⊔ B := Subgroup.mem_sup_left hg₁
    have hw : g₁ * (a * b) * g₁⁻¹ ∈ Q := hQn g₁ hg₁H _ hzQ
    have hgb : g₁ * b = b * g₁ := hc g₁ hg₁ b hb
    have hgb' : g₁ * b * g₁⁻¹ = b := by rw [hgb]; group
    have e1 : g₁ * (a * b) * g₁⁻¹ = (g₁ * a * g₁⁻¹) * b := by
      calc g₁ * (a * b) * g₁⁻¹ = (g₁ * a * g₁⁻¹) * (g₁ * b * g₁⁻¹) := by group
        _ = (g₁ * a * g₁⁻¹) * b := by rw [hgb']
    rcases hcases _ hw with h | h | h
    · exact absurd (by
        calc a * b = g₁⁻¹ * (g₁ * (a * b) * g₁⁻¹) * g₁ := by group
          _ = 1 := by rw [h]; group) hz1
    · left
      rw [e1] at h
      exact mul_right_cancel h
    · right
      rw [e1] at h
      have hX : g₁ * a * g₁⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem hg₁ ha) (A.inv_mem hg₁)
      have h5 : a * (g₁ * a * g₁⁻¹) = b⁻¹ * b⁻¹ := by
        have h6 : a * ((g₁ * a * g₁⁻¹) * b) = a * (a * b)⁻¹ := by rw [h]
        have h7 : a * (a * b)⁻¹ = b⁻¹ := by
          calc a * (a * b)⁻¹ = a * (b⁻¹ * a⁻¹) := by rw [mul_inv_rev]
            _ = (a * b⁻¹) * a⁻¹ := by group
            _ = (b⁻¹ * a) * a⁻¹ := by rw [hab.inv_right.eq]
            _ = b⁻¹ := by group
        rw [h7] at h6
        calc a * (g₁ * a * g₁⁻¹) = (a * ((g₁ * a * g₁⁻¹) * b)) * b⁻¹ := by group
          _ = b⁻¹ * b⁻¹ := by rw [h6]
      have hmem : b⁻¹ * b⁻¹ ∈ A ⊓ B :=
        ⟨h5 ▸ A.mul_mem ha hX, B.mul_mem (B.inv_mem hb) (B.inv_mem hb)⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      have hbb : b * b = 1 := by
        have : (b * b)⁻¹ = 1 := by rw [mul_inv_rev]; exact hmem
        exact inv_eq_one.1 this
      calc b = b ^ 3 * (b * b)⁻¹ := by group
        _ = 1 := by rw [hb3, hbb]; group
  by_cases hb1 : b = 1
  · left
    rw [hQz]
    exact Subgroup.zpowers_le.2 (by simpa [hb1] using ha)
  · right
    have ha1 : a = 1 := by
      refine hA a ha (fun g hg => ?_)
      have := (key g hg).resolve_right hb1
      calc g * a = (g * a * g⁻¹) * g := by group
        _ = a * g := by rw [this]
    rw [hQz]
    exact Subgroup.zpowers_le.2 (by simpa [ha1] using hb)

structure GoodFactor (H P A Z : Subgroup Ω) : Prop where
  le : Z ≤ A
  decomp : A ≤ perfectCore A ⊔ Z ⊔ P
  normal : Z = ⊥ ∨ IsNormalThree H Z
  unique : ∀ Q : Subgroup Ω, IsNormalThree A Q → Q = Z

theorem fixed3_sup {H Z₁ Z₂ : Subgroup Ω} (h₁ : Fixed3 H Z₁) (h₂ : Fixed3 H Z₂) :
    Fixed3 H (Z₁ ⊔ Z₂) := by
  intro g hg3 hgH z hz
  have key : ∀ Z : Subgroup Ω, Fixed3 H Z → Z ≤ Subgroup.centralizer {g} := by
    intro Z hZ x hx
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := hZ y hg3 hgH x hx
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [this]
  have hle : Z₁ ⊔ Z₂ ≤ Subgroup.centralizer {g} := sup_le (key Z₁ h₁) (key Z₂ h₂)
  have := Subgroup.mem_centralizer_iff.1 (hle hz) g rfl
  calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [this]
    _ = z := by group

theorem fixed3_bot {H : Subgroup Ω} : Fixed3 H ⊥ := by
  intro g _ _ z hz
  rw [Subgroup.mem_bot] at hz
  subst hz
  simp

theorem digest_of_product {H P A B ZA ZB : Subgroup Ω} (hH : A ⊔ B = H)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hcen : CenterTrivial A ∨ CenterTrivial B) (hA : GoodFactor H P A ZA)
    (hB : GoodFactor H P B ZB) :
    H ≤ perfectCore H ⊔ (ZA ⊔ ZB) ⊔ P ∧ Fixed3 H (ZA ⊔ ZB) ∧ ZA ⊔ ZB ≤ H := by
  have hAH : A ≤ H := hH ▸ le_sup_left
  have hBH : B ≤ H := hH ▸ le_sup_right
  have hc' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
  have hinf' : B ⊓ A = ⊥ := by rw [inf_comm]; exact hinf
  refine ⟨?_, ?_, sup_le (hA.le.trans hAH) (hB.le.trans hBH)⟩
  · set X : Subgroup Ω := perfectCore H ⊔ (ZA ⊔ ZB) ⊔ P with hX
    have hX1 : perfectCore H ≤ X := le_sup_of_le_left le_sup_left
    have hX2 : ZA ≤ X := le_sup_of_le_left (le_sup_of_le_right le_sup_left)
    have hX3 : ZB ≤ X := le_sup_of_le_left (le_sup_of_le_right le_sup_right)
    have hX4 : P ≤ X := le_sup_right
    have hAX : A ≤ X :=
      hA.decomp.trans (sup_le (sup_le ((perfectCore_mono hAH).trans hX1) hX2) hX4)
    have hBX : B ≤ X :=
      hB.decomp.trans (sup_le (sup_le ((perfectCore_mono hBH).trans hX1) hX3) hX4)
    rw [← hH]
    exact sup_le hAX hBX
  ·
    have hΞ : ∀ Q : Subgroup Ω, IsNormalThree H Q → Q = ZA ∨ Q = ZB := by
      intro Q hQ
      have hQ' : IsNormalThree (A ⊔ B) Q := hH ▸ hQ
      have hle : Q ≤ A ∨ Q ≤ B := by
        rcases hcen with h | h
        · exact normalThree_le_factor hc hinf h hQ'
        · have hQ'' : IsNormalThree (B ⊔ A) Q := by rw [sup_comm]; exact hQ'
          rcases normalThree_le_factor hc' hinf' h hQ'' with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
      rcases hle with h | h
      · exact Or.inl (hA.unique Q ⟨h, fun x hx q hq => hQ.2.1 x (hAH hx) q hq, hQ.2.2⟩)
      · exact Or.inr (hB.unique Q ⟨h, fun x hx q hq => hQ.2.1 x (hBH hx) q hq, hQ.2.2⟩)
    have hfix : ∀ Z : Subgroup Ω, (Z = ⊥ ∨ IsNormalThree H Z) → Fixed3 H Z := by
      intro Z hZ
      rcases hZ with rfl | hZ
      · exact fixed3_bot
      · exact fixed3_of_unique hΞ hZ
    exact fixed3_sup (hfix ZA hA.normal) (hfix ZB hB.normal)

end CFSG.Quasithin.SzN17
