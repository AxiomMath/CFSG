module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructA.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace TB

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

structure TwoLines (p : ℕ) (A E F₁ F₂ : Subgroup G) : Prop where
  mem_E : E ∈ signalizerFunctorEk p 1 A
  mem₁ : F₁ ∈ signalizerFunctorEk p 1 A
  mem₂ : F₂ ∈ signalizerFunctorEk p 1 A
  ne₁ : F₁ ≠ E
  ne₂ : F₂ ≠ E
  ne₁₂ : F₁ ≠ F₂
  sup_eq : E ⊔ F₁ ⊔ F₂ = A

namespace TwoLines

variable {E F₁ F₂ : Subgroup G}

omit [Finite G] in
theorem symm (hT : TwoLines p A E F₁ F₂) : TwoLines p A E F₂ F₁ :=
  ⟨hT.mem_E, hT.mem₂, hT.mem₁, hT.ne₂, hT.ne₁, hT.ne₁₂.symm, by rw [sup_right_comm, hT.sup_eq]⟩

theorem not_le_of_card_le (h : Counterexample p A θ) {X : Subgroup G} (hX : Nat.card X ≤ p ^ 2) :
    ¬ A ≤ X := fun hAX => by
  have h1 := Subgroup.card_le_of_le hAX
  rw [h.card] at h1
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
  omega

theorem mem_E2_sup₁ (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    E ⊔ F₁ ∈ signalizerFunctorEk p 2 A :=
  h.sup_mem_E2_of_ne hT.mem_E hT.mem₁ hT.ne₁.symm

theorem mem_E2_sup₂ (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    E ⊔ F₂ ∈ signalizerFunctorEk p 2 A :=
  mem_E2_sup₁ h hT.symm

theorem not_le_sup₁ (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    ¬ F₂ ≤ E ⊔ F₁ := fun hle =>
  not_le_of_card_le h (le_of_eq (mem_E2_sup₁ h hT).2) (hT.sup_eq ▸ sup_le le_rfl hle)

theorem not_le_sup₂ (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    ¬ F₁ ≤ E ⊔ F₂ := not_le_sup₁ h hT.symm

theorem inf_sup₁_eq_bot (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    (E ⊔ F₁) ⊓ F₂ = ⊥ :=
  inf_eq_bot_of_not_le h.prime (by rw [hT.mem₂.2, pow_one]) (not_le_sup₁ h hT)

theorem inf_sup₁_eq_bot' (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    F₂ ⊓ (E ⊔ F₁) = ⊥ := by
  rw [inf_comm]
  exact inf_sup₁_eq_bot h hT

theorem inf_sup₂_eq_bot (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    (E ⊔ F₂) ⊓ F₁ = ⊥ :=
  inf_sup₁_eq_bot h hT.symm

theorem inf_sup₂_eq_bot' (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    F₁ ⊓ (E ⊔ F₂) = ⊥ :=
  inf_sup₁_eq_bot' h hT.symm

theorem sup₁_ne_sup₂ (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    E ⊔ F₁ ≠ E ⊔ F₂ := fun heq =>
  not_le_sup₁ h hT (heq ▸ le_sup_right)

theorem sup_inf_sup_eq (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    (E ⊔ F₁) ⊓ (E ⊔ F₂) = E := by
  have hl := h.inf_mem_E1_of_ne_E2 (mem_E2_sup₁ h hT) (mem_E2_sup₂ h hT) (sup₁_ne_sup₂ h hT)
  exact (Subgroup.eq_of_le_of_card_ge (le_inf le_sup_left le_sup_left)
    (by rw [hl.2, hT.mem_E.2])).symm

omit [Finite G] in
theorem sup_sup_eq (hT : TwoLines p A E F₁ F₂) : (E ⊔ F₁) ⊔ (E ⊔ F₂) = A := by
  rw [sup_sup_sup_comm, sup_idem, ← sup_assoc, hT.sup_eq]

theorem mem_E2_sup (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    F₁ ⊔ F₂ ∈ signalizerFunctorEk p 2 A :=
  h.sup_mem_E2_of_ne hT.mem₁ hT.mem₂ hT.ne₁₂

theorem not_le_sup (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) : ¬ E ≤ F₁ ⊔ F₂ :=
  fun hle => not_le_of_card_le h (le_of_eq (mem_E2_sup h hT).2)
    (by rw [← hT.sup_eq]; exact sup_le (sup_le hle le_sup_left) le_sup_right)

theorem inf_sup_eq_bot (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    (F₁ ⊔ F₂) ⊓ E = ⊥ :=
  inf_eq_bot_of_not_le h.prime (by rw [hT.mem_E.2, pow_one]) (not_le_sup h hT)

theorem inf_sup_eq_bot' (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    E ⊓ (F₁ ⊔ F₂) = ⊥ := by
  rw [inf_comm]
  exact inf_sup_eq_bot h hT

omit [Finite G] in
theorem sup_sup_eq' (hT : TwoLines p A E F₁ F₂) : E ⊔ (F₁ ⊔ F₂) = A := by
  rw [← sup_assoc, hT.sup_eq]

theorem exists_twoLines (h : Counterexample p A θ) (hE : E ∈ signalizerFunctorEk p 1 A) :
    ∃ F₁ F₂ : Subgroup G, TwoLines p A E F₁ F₂ := by
  obtain ⟨e, he, he1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hE
  obtain ⟨B₀, hB₀A, hB₀c, hdisj, hsup⟩ := h.exists_complement_zpowers he he1
  have hB₀ : B₀ ∈ signalizerFunctorEk p 2 A := ⟨hB₀A, hB₀c⟩
  obtain ⟨F₁, hF₁, hF₁B⟩ := h.exists_line_le_of_mem_E2 hB₀
  obtain ⟨F₂, hF₂, hF₂B, hne, hF₁₂⟩ := h.exists_line_sup_eq_of_mem_E2 hB₀ hF₁ hF₁B
  have hne_E : ∀ F : Subgroup G, F ∈ signalizerFunctorEk p 1 A → F ≤ B₀ →
      F ≠ Subgroup.zpowers e := by
    intro F hF hFB heq
    have h1 : Subgroup.zpowers e ≤ Subgroup.zpowers e ⊓ B₀ := le_inf le_rfl (heq ▸ hFB)
    rw [hdisj, le_bot_iff] at h1
    exact h.ne_bot_of_mem_E1 hE h1
  refine ⟨F₁, F₂, hE, hF₁, hF₂, hne_E F₁ hF₁ hF₁B, hne_E F₂ hF₂ hF₂B, hne.symm, ?_⟩
  rw [sup_assoc, hF₁₂, hsup]

end TwoLines

end TB

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
