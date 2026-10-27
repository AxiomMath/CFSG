module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} {θ θ' : G → Subgroup G}

open scoped Classical in
private theorem size_eq_sum [Fintype G] (A : Subgroup G) (θ : G → Subgroup G) :
    size A θ = ∑ a : G, if a ∈ A ∧ a ≠ 1 then Nat.card (θ a) else 0 := by
  unfold size
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases ha : a ∈ A <;> by_cases ha1 : a ≠ 1 <;> simp [ha, ha1]

theorem size_le_size [Finite G] (h : ∀ a ∈ A, a ≠ 1 → θ' a ≤ θ a) : size A θ' ≤ size A θ := by
  classical
  have := Fintype.ofFinite G
  rw [size_eq_sum, size_eq_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  split_ifs with hc
  · exact Subgroup.card_le_of_le (h a hc.1 hc.2)
  · exact le_rfl

theorem size_lt_size [Finite G] (h : ∀ a ∈ A, a ≠ 1 → θ' a ≤ θ a)
    (hne : ∃ a ∈ A, a ≠ 1 ∧ θ' a ≠ θ a) : size A θ' < size A θ := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨a₀, ha₀, ha₀1, hne⟩ := hne
  rw [size_eq_sum, size_eq_sum]
  refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a₀, Finset.mem_univ _, ?_⟩
  · split_ifs with hc
    · exact Subgroup.card_le_of_le (h a hc.1 hc.2)
    · exact le_rfl
  · have hc : a₀ ∈ A ∧ a₀ ≠ 1 := ⟨ha₀, ha₀1⟩
    split_ifs
    refine lt_of_le_of_ne (Subgroup.card_le_of_le (h a₀ ha₀ ha₀1)) fun heq => hne ?_
    exact Subgroup.eq_of_le_of_card_ge (h a₀ ha₀ ha₀1) heq.ge

theorem size_congr (h : ∀ a ∈ A, a ≠ 1 → θ' a = θ a) : size A θ' = size A θ := by
  unfold size
  refine finsum_congr fun a => finsum_congr fun ha => finsum_congr fun ha1 => ?_
  rw [h a ha ha1]

theorem card_apply_le_size [Finite G] {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Nat.card (θ a) ≤ size A θ := by
  classical
  have := Fintype.ofFinite G
  rw [size_eq_sum]
  have := Finset.single_le_sum (f := fun a => if a ∈ A ∧ a ≠ 1 then Nat.card (θ a) else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  simpa [ha, ha1] using this

theorem complete_of_subfunctor [Finite G] {P : Subgroup G → Prop} (hθ' : IsFunctor p A θ')
    (hle : ∀ a ∈ A, a ≠ 1 → θ' a ≤ θ a) (hne : ∃ a ∈ A, a ≠ 1 ∧ θ' a ≠ θ a)
    (hP : ∀ a ∈ A, a ≠ 1 → P (θ a))
    (hmono : ∀ X Y : Subgroup G, Y ≤ X → A ≤ Subgroup.normalizer (Y : Set G) → P X → P Y)
    (hmin : ∀ θ'' : G → Subgroup G, IsFunctor p A θ'' → (∀ a ∈ A, a ≠ 1 → P (θ'' a)) →
      size A θ'' < size A θ → IsCompleteIn (signalizers p A θ'' P)) :
    IsCompleteIn (signalizers p A θ' P) ∧ signalizers p A θ' P ⊆ signalizers p A θ P := by
  refine ⟨hmin θ' hθ' (fun a ha ha1 => ?_) (size_lt_size hle hne),
    signalizers_mono_functor fun a ha ha1 => (hle a ha ha1)⟩
  exact hmono _ _ (hle a ha ha1) (hθ'.normalized a ha ha1) (hP a ha ha1)

end CFSG.SignalizerFunctorTheorem.McBride
