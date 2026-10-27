module

public import CFSG.Sporadic.Co2Smith.Fusion

public section

namespace CFSG.Sporadic.Co2Smith

variable {M : Type*} [Group M] [Finite M]

abbrev conjSet (r : M) : Set M := {y : M | ∃ h : M, y = h * r * h⁻¹}

omit [Finite M] in
theorem not_conj_of_sqrtCnt {zM r r' : M} (hzc : ∀ g : M, g * zM = zM * g)
    (hne : sqrtCnt zM r ≠ sqrtCnt zM r' ∨ sqrtCnt r r ≠ sqrtCnt r' r') :
    ∀ h : M, h * r * h⁻¹ ≠ r' := by
  intro h e
  have ez : h * zM * h⁻¹ = zM := by rw [hzc h, mul_inv_cancel_right]
  rcases hne with hne | hne
  · apply hne
    rw [← e, ← sqrtCnt_conj h zM r, ez]
  · apply hne
    rw [← e, sqrtCnt_conj]

theorem exists_conj_of_card {zM : M} (r : Fin 4 → M) (m : Fin 4 → ℕ)
    (hcard : Nat.card {y : M // y * y = 1} = 2 + (m 0 + m 1 + m 2 + m 3))
    (hzz : zM * zM = 1) (hz1 : zM ≠ 1) (hzc : ∀ g : M, g * zM = zM * g)
    (hr : ∀ i, r i * r i = 1 ∧ r i ≠ 1 ∧ r i ≠ zM)
    (hm : ∀ i, m i ≤ (conjSet (r i)).ncard)
    (hdisj : ∀ i j, i ≠ j → ∀ h : M, h * r i * h⁻¹ ≠ r j) :
    ∀ y : M, y * y = 1 → y = 1 ∨ y = zM ∨ ∃ i, ∃ h : M, h * y * h⁻¹ = r i := by
  classical
  set I : Set M := {y | y * y = 1 ∧ y ≠ 1 ∧ y ≠ zM}
  have hsub : ∀ i, conjSet (r i) ⊆ I := by
    rintro i _ ⟨h, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hr i
    have hsq : h * r i * h⁻¹ * (h * r i * h⁻¹) = 1 := by
      rw [show h * r i * h⁻¹ * (h * r i * h⁻¹) = h * (r i * r i) * h⁻¹ by group, h1]
      group
    refine ⟨hsq, fun e => h2 ?_, fun e => h3 ?_⟩
    · calc r i = h⁻¹ * (h * r i * h⁻¹) * h := by group
        _ = 1 := by rw [e]; group
    · calc r i = h⁻¹ * (h * r i * h⁻¹) * h := by group
        _ = h⁻¹ * zM * h := by rw [e]
        _ = zM := by rw [mul_assoc, ← hzc h, ← mul_assoc, inv_mul_cancel, one_mul]
  have hdj : ∀ i j, i ≠ j → Disjoint (conjSet (r i)) (conjSet (r j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨h, rfl⟩ ⟨h', e⟩
    apply hdisj i j hij (h'⁻¹ * h)
    calc h'⁻¹ * h * r i * (h'⁻¹ * h)⁻¹ = h'⁻¹ * (h * r i * h⁻¹) * h' := by group
      _ = h'⁻¹ * (h' * r j * h'⁻¹) * h' := by rw [e]
      _ = r j := by group
  have hI : I.ncard + 2 = Nat.card {y : M // y * y = 1} := by
    have hset : {y : M | y * y = 1} = I ∪ {1, zM} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, I]
      constructor
      · intro hy
        by_cases h1 : y = 1
        · exact Or.inr (Or.inl h1)
        · by_cases h2 : y = zM
          · exact Or.inr (Or.inr h2)
          · exact Or.inl ⟨hy, h1, h2⟩
      · rintro (⟨hy, -, -⟩ | rfl | rfl)
        · exact hy
        · exact one_mul 1
        · exact hzz
    have hdisj' : Disjoint I {1, zM} := by
      rw [Set.disjoint_left]
      rintro y ⟨-, h1, h2⟩ (rfl | rfl)
      · exact h1 rfl
      · exact h2 rfl
    have hc : Nat.card {y : M // y * y = 1} = ({y : M | y * y = 1}).ncard :=
      Nat.card_coe_set_eq _
    rw [hc, hset, Set.ncard_union_eq hdisj' (Set.toFinite _) (Set.toFinite _),
      Set.ncard_pair hz1.symm]
  have hU : conjSet (r 0) ∪ conjSet (r 1) ∪ conjSet (r 2) ∪ conjSet (r 3) = I := by
    apply Set.eq_of_subset_of_ncard_le
    · exact Set.union_subset (Set.union_subset (Set.union_subset (hsub 0) (hsub 1)) (hsub 2))
        (hsub 3)
    · rw [Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
        Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
        Set.ncard_union_eq (hdj 0 1 (by decide)) (Set.toFinite _) (Set.toFinite _)]
      · have := hm 0
        have := hm 1
        have := hm 2
        have := hm 3
        omega
      · exact Set.disjoint_union_left.mpr ⟨hdj 0 2 (by decide), hdj 1 2 (by decide)⟩
      · exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
          ⟨hdj 0 3 (by decide), hdj 1 3 (by decide)⟩, hdj 2 3 (by decide)⟩
    · exact Set.toFinite _
  intro y hy
  by_cases h1 : y = 1
  · exact Or.inl h1
  by_cases h2 : y = zM
  · exact Or.inr (Or.inl h2)
  have hyI : y ∈ I := ⟨hy, h1, h2⟩
  rw [← hU] at hyI
  have key : ∃ i, y ∈ conjSet (r i) := by
    rcases hyI with ((h | h) | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  obtain ⟨i, h, rfl⟩ := key
  exact Or.inr (Or.inr ⟨i, h⁻¹, by group⟩)

end CFSG.Sporadic.Co2Smith
