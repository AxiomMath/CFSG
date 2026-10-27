module

public import CFSG.Quasithin.Vol2.GoldschmidtE217E4Comp
public import CFSG.Quasithin.Vol2.GoldschmidtE217Klein

public section

namespace CFSG.Quasithin

namespace E217R4

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem commutes_sup {K₁ K₂ : Subgroup Γ} {w : Γ} (h₁ : ∀ k ∈ K₁, w * k = k * w)
    (h₂ : ∀ k ∈ K₂, w * k = k * w) : ∀ k ∈ K₁ ⊔ K₂, w * k = k * w := by
  have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({w} : Set Γ) :=
    sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (h₁ k hk).symm)
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (h₂ k hk).symm)
  exact fun k hk => (Subgroup.mem_centralizer_singleton_iff.1 (hle hk)).symm

theorem e4_pair {K₁ K₂ S E : Subgroup Γ} {t b₁ : Γ} (hKn : (K₁ ⊔ K₂).Normal)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (h₁ : IsSimpleGroup ↥K₁)
    (hz₁ : ∀ x ∈ K₁, (∀ y ∈ K₁, y * x = x * y) → x = 1)
    (hz₂ : ∀ x ∈ K₂, (∀ y ∈ K₂, y * x = x * y) → x = 1) (hcard : Nat.card K₂ = Nat.card K₁)
    (hCK : ∀ a : Γ, (∀ k ∈ K₁ ⊔ K₂, a * k = k * a) → a = 1)
    (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom) (htS : t ∈ S)
    (hSE : S ≤ Subgroup.normalizer (E : Set Γ)) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ e ∈ E, e * e = 1) (hEcard : Nat.card E = 4) (hb₁E : b₁ ∈ E)
    (hb₁C : ∀ k ∈ K₁, b₁ * k = k * b₁) (hb₁1 : b₁ ≠ 1)
    (hA₁ : ∀ e ∈ E, (∀ k ∈ K₁, e * k = k * e) → e = 1 ∨ e = b₁) :
    t * b₁ * t⁻¹ ≠ b₁ ∧ Subgroup.closure ({b₁, t * b₁ * t⁻¹} : Set Γ) = E ∧
      (∀ k ∈ K₂, (t * b₁ * t⁻¹) * k = k * (t * b₁ * t⁻¹)) ∧
      ∀ s ∈ S, s * (b₁ * (t * b₁ * t⁻¹)) = (b₁ * (t * b₁ * t⁻¹)) * s := by
  set b₂ : Γ := t * b₁ * t⁻¹ with hb₂
  have hconj : ∀ g : Γ, g * b₁ * g⁻¹ ∈ E → g ∈ S → ∀ k ∈ K₁.map (MulAut.conj g).toMonoidHom,
      (g * b₁ * g⁻¹) * k = k * (g * b₁ * g⁻¹) := by
    rintro g - - k ⟨y, hy, rfl⟩
    show g * b₁ * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * b₁ * g⁻¹)
    calc g * b₁ * g⁻¹ * (g * y * g⁻¹) = g * (b₁ * y) * g⁻¹ := by group
      _ = g * (y * b₁) * g⁻¹ := by rw [hb₁C y hy]
      _ = g * y * g⁻¹ * (g * b₁ * g⁻¹) := by group
  have hb₂E : b₂ ∈ E := (Subgroup.mem_normalizer_iff.1 (hSE htS) b₁).1 hb₁E
  have hb₂C : ∀ k ∈ K₂, b₂ * k = k * b₂ := by
    intro k hk
    rw [hK₂] at hk
    exact hconj t hb₂E htS k hk
  have hb₂1 : b₂ ≠ 1 := fun h => hb₁1 (by
    calc b₁ = t⁻¹ * b₂ * t := by rw [hb₂]; group
      _ = 1 := by rw [h]; group)
  have hne : b₂ ≠ b₁ := by
    intro h
    exact hb₁1 (hCK b₁ (commutes_sup hb₁C (fun k hk => by rw [← h]; exact hb₂C k hk)))
  have hb₁2 : b₁ * b₁ = 1 := hE2 b₁ hb₁E
  have hb₂2 : b₂ * b₂ = 1 := hE2 b₂ hb₂E
  have hcomm : b₁ * b₂ = b₂ * b₁ := hEc b₁ hb₁E b₂ hb₂E
  have hclos : Subgroup.closure ({b₁, b₂} : Set Γ) = E := by
    have hle : Subgroup.closure ({b₁, b₂} : Set Γ) ≤ E := by
      refine (Subgroup.closure_le E).2 ?_
      rintro y (rfl | rfl)
      exacts [hb₁E, hb₂E]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hEcard]
    exact E217R3.four_le_card_closure hb₁2 hb₂2 hb₁1 hb₂1 hne.symm
  have hA₂ : ∀ e ∈ E, (∀ k ∈ K₂, e * k = k * e) → e = 1 ∨ e = b₂ := by
    intro e he hek
    have he' : t⁻¹ * e * t ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 (hSE (S.inv_mem htS)) e).1 he
      simpa using this
    have hC : ∀ k ∈ K₁, (t⁻¹ * e * t) * k = k * (t⁻¹ * e * t) := by
      intro k hk
      have hkt : t * k * t⁻¹ ∈ K₂ := by
        rw [hK₂]
        exact ⟨k, hk, rfl⟩
      have h := hek _ hkt
      calc t⁻¹ * e * t * k = t⁻¹ * (e * (t * k * t⁻¹)) * t := by group
        _ = t⁻¹ * ((t * k * t⁻¹) * e) * t := by rw [h]
        _ = k * (t⁻¹ * e * t) := by group
    rcases hA₁ _ he' hC with h | h
    · left
      calc e = t * (t⁻¹ * e * t) * t⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc e = t * (t⁻¹ * e * t) * t⁻¹ := by group
        _ = b₂ := by rw [h]
  have hmov : ∀ s ∈ S, s * b₁ * s⁻¹ = b₁ ∨ s * b₁ * s⁻¹ = b₂ := by
    intro s hs
    have hsE : s * b₁ * s⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hSE hs) b₁).1 hb₁E
    have hne1 : s * b₁ * s⁻¹ ≠ 1 := fun h => hb₁1 (by
      calc b₁ = s⁻¹ * (s * b₁ * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group)
    rcases conj_component hKn hc h₁ hz₁ hz₂ hcard s with h | h
    · left
      have := hconj s hsE hs
      rw [h] at this
      exact (hA₁ _ hsE this).resolve_left hne1
    · right
      have := hconj s hsE hs
      rw [h] at this
      exact (hA₂ _ hsE this).resolve_left hne1
  refine ⟨hne, hclos, hb₂C, fun s hs => ?_⟩
  have h1 := hmov s hs
  have h2 := hmov (s * t) (S.mul_mem hs htS)
  have e2 : s * t * b₁ * (s * t)⁻¹ = s * b₂ * s⁻¹ := by rw [hb₂]; group
  rw [e2] at h2
  have hsv : s * (b₁ * b₂) * s⁻¹ = b₁ * b₂ := by
    have hinj : s * b₁ * s⁻¹ ≠ s * b₂ * s⁻¹ := fun h =>
      hne.symm (mul_left_cancel (mul_right_cancel h))
    calc s * (b₁ * b₂) * s⁻¹ = (s * b₁ * s⁻¹) * (s * b₂ * s⁻¹) := by group
      _ = b₁ * b₂ := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hinj
        · rw [h1, h2]
        · rw [h1, h2, hcomm]
        · exact absurd (h1.trans h2.symm) hinj
  calc s * (b₁ * b₂) = (s * (b₁ * b₂) * s⁻¹) * s := by group
    _ = (b₁ * b₂) * s := by rw [hsv]

omit [Finite Γ] in
theorem e4_mem {K₁ K₂ E : Subgroup Γ} {b₁ b₂ : Γ} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hCK : ∀ a : Γ, (∀ k ∈ K₁ ⊔ K₂, a * k = k * a) → a = 1)
    (hEN₁ : E ≤ Subgroup.normalizer (K₁ : Set Γ)) (hb₂E : b₂ ∈ E)
    (hb₁C : ∀ k ∈ K₁, b₁ * k = k * b₁) (hb₂C : ∀ k ∈ K₂, b₂ * k = k * b₂)
    (hvN : b₁ * b₂ ∈ K₁ ⊔ K₂) : b₂ ∈ K₁ ∧ b₁ ∈ K₂ := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hv⟩ := exists_mul_of_mem_sup hc hvN
  have hw₁ : ∀ g ∈ K₁, (k₁⁻¹ * b₂) * g = g * (k₁⁻¹ * b₂) := by
    intro g hg
    have e1 : (b₁ * b₂) * g * (b₁ * b₂)⁻¹ = b₂ * g * b₂⁻¹ := by
      have hn : b₂ * g * b₂⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.1 (hEN₁ hb₂E) g).1 hg
      have h1 := hb₁C _ hn
      calc (b₁ * b₂) * g * (b₁ * b₂)⁻¹ = b₁ * (b₂ * g * b₂⁻¹) * b₁⁻¹ := by group
        _ = (b₂ * g * b₂⁻¹) * b₁ * b₁⁻¹ := by rw [h1]
        _ = b₂ * g * b₂⁻¹ := by group
    have e2 : (k₁ * k₂) * g * (k₁ * k₂)⁻¹ = k₁ * g * k₁⁻¹ := by
      have h2 := hc g hg k₂ hk₂
      calc (k₁ * k₂) * g * (k₁ * k₂)⁻¹ = k₁ * (k₂ * g) * k₂⁻¹ * k₁⁻¹ := by group
        _ = k₁ * (g * k₂) * k₂⁻¹ * k₁⁻¹ := by rw [← h2]
        _ = k₁ * g * k₁⁻¹ := by group
    rw [← hv, e2] at e1
    calc (k₁⁻¹ * b₂) * g = k₁⁻¹ * (b₂ * g * b₂⁻¹) * b₂ := by group
      _ = k₁⁻¹ * (k₁ * g * k₁⁻¹) * b₂ := by rw [← e1]
      _ = g * (k₁⁻¹ * b₂) := by group
  have hw₂ : ∀ g ∈ K₂, (k₁⁻¹ * b₂) * g = g * (k₁⁻¹ * b₂) := by
    intro g hg
    have h1 := hb₂C g hg
    have h2 := hc k₁ hk₁ g hg
    calc (k₁⁻¹ * b₂) * g = k₁⁻¹ * (b₂ * g) := by group
      _ = k₁⁻¹ * (g * b₂) := by rw [h1]
      _ = (k₁⁻¹ * g) * b₂ := by group
      _ = (g * k₁⁻¹) * b₂ := by
        have : k₁⁻¹ * g = g * k₁⁻¹ := by
          calc k₁⁻¹ * g = k₁⁻¹ * (g * k₁) * k₁⁻¹ := by group
            _ = k₁⁻¹ * (k₁ * g) * k₁⁻¹ := by rw [← h2]
            _ = g * k₁⁻¹ := by group
        rw [this]
      _ = g * (k₁⁻¹ * b₂) := by group
  have hw := hCK _ (commutes_sup hw₁ hw₂)
  have hb₂k : b₂ = k₁ := by
    calc b₂ = k₁ * (k₁⁻¹ * b₂) := by group
      _ = k₁ := by rw [hw]; group
  refine ⟨hb₂k ▸ hk₁, ?_⟩
  have : b₁ = k₂ := by
    rw [hb₂k] at hv
    calc b₁ = (b₁ * k₁) * k₁⁻¹ := by group
      _ = (k₁ * k₂) * k₁⁻¹ := by rw [hv]
      _ = k₂ := by
        have h2 := hc k₁ hk₁ k₂ hk₂
        calc (k₁ * k₂) * k₁⁻¹ = (k₂ * k₁) * k₁⁻¹ := by rw [← h2]
          _ = k₂ := by group
  exact this ▸ hk₂

end E217R4

end CFSG.Quasithin
