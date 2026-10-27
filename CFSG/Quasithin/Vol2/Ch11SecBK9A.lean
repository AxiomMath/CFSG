module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

variable {K : Type} [Field K]

@[expose] def tr (a : K) : K := a + a ^ 2

theorem tr_zero : tr (0 : K) = 0 := by simp [tr]

theorem tr_add [CharP K 2] (a b : K) : tr (a + b) = tr a + tr b := by
  unfold tr
  rw [CharTwo.add_sq]
  ring

@[expose] def trHom [CharP K 2] : K →+ K where
  toFun := tr
  map_zero' := tr_zero
  map_add' := tr_add

theorem trHom_apply [CharP K 2] (a : K) : (trHom : K →+ K) a = tr a := rfl

variable [CharP K 2]

theorem tr_one : tr (1 : K) = 0 := by
  unfold tr
  rw [one_pow, CharTwo.add_self_eq_zero]

theorem exists_omega [Finite K] (hK : Nat.card K = 4) :
    ∃ ω : K, ω ^ 2 = ω + 1 ∧ ∀ a : K, a = 0 ∨ a = 1 ∨ a = ω ∨ a = ω + 1 := by
  classical
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push Not at h
    have hle : Fintype.card K ≤ 2 := by
      have : (Finset.univ : Finset K) ⊆ {0, 1} := fun a _ => by
        by_cases ha : a = 0
        · simp [ha]
        · simp [h a ha]
      calc Fintype.card K = (Finset.univ : Finset K).card := rfl
        _ ≤ ({0, 1} : Finset K).card := Finset.card_le_card this
        _ ≤ 2 := Finset.card_le_two
    omega
  have h3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hcard] at this
  have hω2 : ω ^ 2 = ω + 1 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      have e : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
      rw [e, h3, sub_self]
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · have e : ω ^ 2 = -(ω + 1) := by linear_combination h
      rw [e, CharTwo.neg_eq]
  refine ⟨ω, hω2, fun a => ?_⟩
  have hne1 : ω + 1 ≠ 0 := fun h => hω1 (by
    have : ω = -1 := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at this)
  have hne2 : ω + 1 ≠ 1 := fun h => hω0 (by simp at h; exact h)
  have hne3 : ω + 1 ≠ ω := fun h => (one_ne_zero : (1 : K) ≠ 0) (add_eq_left.mp h)
  have huniv : (Finset.univ : Finset K) = {0, 1, ω, ω + 1} := by
    refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
    have h1 : (0 : K) ∉ ({1, ω, ω + 1} : Finset K) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨zero_ne_one, hω0.symm, hne1.symm⟩
    have h2 : (1 : K) ∉ ({ω, ω + 1} : Finset K) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hω1.symm, hne2.symm⟩
    rw [Finset.card_univ, hcard, Finset.card_insert_of_notMem h1,
      Finset.card_insert_of_notMem h2, Finset.card_pair hne3.symm]
  have ha : a ∈ (Finset.univ : Finset K) := Finset.mem_univ a
  rw [huniv] at ha
  simpa using ha

theorem tr_omega {ω : K} (hω : ω ^ 2 = ω + 1) : tr ω = 1 := by
  unfold tr
  rw [hω, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem tr_eq_zero_or_one [Finite K] (hK : Nat.card K = 4) (a : K) : tr a = 0 ∨ tr a = 1 := by
  obtain ⟨ω, hω, h4⟩ := exists_omega hK
  rcases h4 a with rfl | rfl | rfl | rfl
  · exact Or.inl tr_zero
  · exact Or.inl tr_one
  · exact Or.inr (tr_omega hω)
  · right
    rw [tr_add, tr_omega hω, tr_one, add_zero]

theorem exists_tr_mul_eq [Finite K] (hK : Nat.card K = 4) (χ : K →+ K)
    (hχ : ∀ a, χ a = 0 ∨ χ a = 1) : ∃ b : K, ∀ a, χ a = tr (b * a) := by
  obtain ⟨ω, hω, h4⟩ := exists_omega hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have t0 : tr (0 : K) = 0 := tr_zero
  have t1 : tr (1 : K) = 0 := tr_one
  have tω : tr ω = 1 := tr_omega hω
  have tω1 : tr (ω + 1) = 1 := by rw [tr_add, tω, t1, add_zero]
  have hωω : ω * ω = ω + 1 := by rw [← sq, hω]
  have hω1ω : ω * (ω + 1) = 1 := by linear_combination hω + ω * h2
  have h1ω1 : (ω + 1) * (ω + 1) = ω := by linear_combination hω + (ω + 1) * h2
  have hχ1 : χ (ω + 1) = χ ω + χ 1 := map_add χ ω 1
  rcases hχ 1 with h1 | h1 <;> rcases hχ ω with hw | hw
  · refine ⟨0, fun a => ?_⟩
    rw [zero_mul, t0]
    rcases h4 a with rfl | rfl | rfl | rfl
    · exact map_zero χ
    · exact h1
    · exact hw
    · rw [hχ1, h1, hw, add_zero]
  · refine ⟨1, fun a => ?_⟩
    rw [one_mul]
    rcases h4 a with rfl | rfl | rfl | rfl
    · rw [map_zero, t0]
    · rw [h1, t1]
    · rw [hw, tω]
    · rw [hχ1, h1, hw, add_zero, tω1]
  · refine ⟨ω + 1, fun a => ?_⟩
    rcases h4 a with rfl | rfl | rfl | rfl
    · rw [map_zero, mul_zero, t0]
    · rw [h1, mul_one, tω1]
    · rw [hw, mul_comm, hω1ω, t1]
    · rw [hχ1, h1, hw, zero_add, h1ω1, tω]
  · refine ⟨ω, fun a => ?_⟩
    rcases h4 a with rfl | rfl | rfl | rfl
    · rw [map_zero, mul_zero, t0]
    · rw [h1, mul_one, tω]
    · rw [hw, hωω, tω1]
    · rw [hχ1, h1, hw, CharTwo.add_self_eq_zero, hω1ω, t1]

theorem exists_dot_eq [Finite K] (hK : Nat.card K = 4) {ι : Type} [Fintype ι] [DecidableEq ι]
    (χ : (ι → K) →+ K) (hχ : ∀ x, χ x = 0 ∨ χ x = 1) :
    ∃ a : ι → K, ∀ x, χ x = tr (a ⬝ᵥ x) := by
  have hb : ∀ i : ι, ∃ b : K, ∀ c, χ (Pi.single i c) = tr (b * c) := fun i =>
    exists_tr_mul_eq hK (χ.comp (AddMonoidHom.single (fun _ => K) i)) (fun c => hχ _)
  choose b hb using hb
  refine ⟨b, fun x => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, dotProduct, ← trHom_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => hb i (x i)

theorem exists_tr_dot_eq_one [Finite K] (hK : Nat.card K = 4) {ι : Type} [Fintype ι]
    [DecidableEq ι] {a : ι → K} (ha : a ≠ 0) : ∃ x : ι → K, tr (a ⬝ᵥ x) = 1 := by
  obtain ⟨ω, hω, -⟩ := exists_omega hK
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  refine ⟨Pi.single i (ω / a i), ?_⟩
  rw [dotProduct_single, mul_div_cancel₀ _ hi, tr_omega hω]

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
