module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltForced
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltEightK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltEightW

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Equiv

attribute [local irreducible] S16C11AltWords

theorem s16c11_alt_pass_of_card {n : ℕ} (gens : List ↥(alternatingGroup (Fin n))) (m : ℕ)
    (τ : Equiv.Perm (Fin n)) (hτ : Equiv.Perm.sign τ = -1) (P : Equiv.Perm (Fin n) → Prop)
    [DecidablePred P] (k : ℕ) (hP : (Finset.univ.filter P).card = k)
    (hU : ((S16C11AltWords gens m).image Subtype.val ∪
      (S16C11AltWords gens m).image fun t => τ * t.val).card = k)
    (hsub : ∀ w ∈ (S16C11AltWords gens m).image Subtype.val ∪
      (S16C11AltWords gens m).image fun t => τ * t.val, P w) :
    ∀ g : Equiv.Perm (Fin n), P g → Equiv.Perm.sign g = 1 →
      g ∈ (S16C11AltWords gens m).image Subtype.val := by
  intro g hg hsign
  have hsubset : (S16C11AltWords gens m).image Subtype.val ∪
      (S16C11AltWords gens m).image (fun t => τ * t.val) ⊆ Finset.univ.filter P :=
    fun w hw => Finset.mem_filter.2 ⟨Finset.mem_univ _, hsub w hw⟩
  have heq := Finset.eq_of_subset_of_card_le hsubset (by rw [hP, hU])
  have hg' : g ∈ (S16C11AltWords gens m).image Subtype.val ∪
      (S16C11AltWords gens m).image (fun t => τ * t.val) := by
    rw [heq]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩
  rcases Finset.mem_union.1 hg' with h | h
  · exact h
  · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 h
    exfalso
    have ht : Equiv.Perm.sign t.val = 1 := Equiv.Perm.mem_alternatingGroup.1 t.2
    rw [Equiv.Perm.sign_mul, hτ, ht] at hsign
    exact absurd hsign (by decide)

@[expose] def s16c11AltEightG1 : ↥(alternatingGroup (Fin 8)) :=
  S16C11AltSw2 0 1 2 3 (by decide) (by decide)

@[expose] def s16c11AltEightG2 : ↥(alternatingGroup (Fin 8)) :=
  S16C11AltSw2 0 2 1 3 (by decide) (by decide)

@[expose] def s16c11AltEightG3 : ↥(alternatingGroup (Fin 8)) :=
  S16C11AltSw2 0 1 4 5 (by decide) (by decide)

@[expose] def s16c11AltEightG4 : ↥(alternatingGroup (Fin 8)) :=
  S16C11AltSw2 4 5 6 7 (by decide) (by decide)

@[expose] def s16c11AltEightG5 : ↥(alternatingGroup (Fin 8)) :=
  S16C11AltSw2 4 6 5 7 (by decide) (by decide)

@[expose] def s16c11AltEightG6 : ↥(alternatingGroup (Fin 8)) :=
  S16C11AltSw2 0 4 1 5 (by decide) (by decide) * S16C11AltSw2 2 6 3 7 (by decide) (by decide)

@[expose] def s16c11AltEightGens : List ↥(alternatingGroup (Fin 8)) :=
  [s16c11AltEightG1, s16c11AltEightG2, s16c11AltEightG3, s16c11AltEightG4, s16c11AltEightG5,
    s16c11AltEightG6]

@[expose] def s16c11AltEightX0 : Fin 8 → ZMod 2 := ![1, 1, 1, 1, 0, 0, 0, 0]

@[expose] def s16c11AltEightXa : Fin 8 → ZMod 2 := ![1, 1, 0, 0, 1, 1, 0, 0]

@[expose] def s16c11AltEightXb : Fin 8 → ZMod 2 := ![1, 1, 0, 0, 0, 0, 1, 1]

@[expose] def s16c11AltEightSa : ↥(alternatingGroup (Fin 8)) :=
  S16C11AltSw2 2 4 3 5 (by decide) (by decide)

@[expose] def s16c11AltEightSb : ↥(alternatingGroup (Fin 8)) :=
  S16C11AltSw2 2 6 3 7 (by decide) (by decide)

private theorem s16c11_altEight_words_eq :
    S16C11AltWords s16c11AltEightGens 5 = S16C11AltEightW.wordsT := by
  decide +kernel

theorem s16c11_altEight_words_fix :
    S16C11AltWords s16c11AltEightGens 6 = S16C11AltWords s16c11AltEightGens 5 := by
  rw [S16C11AltWords.eq_2 s16c11AltEightGens 5, s16c11_altEight_words_eq]
  decide +kernel

theorem s16c11_altEight_words_card : (S16C11AltWords s16c11AltEightGens 5).card = 2 ^ 6 := by
  rw [s16c11_altEight_words_eq]
  decide +kernel

theorem s16c11_altEight_card : Nat.card ↥(alternatingGroup (Fin 8)) = 2 ^ 6 * 315 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem s16c11_altEight_uniq_aux :
    ∀ k : Fin (2 ^ 8), ∑ i, S16C11AltBits 8 k i = 0 → ¬ S16C11AltEqv 0 (S16C11AltBits 8 k) →
      S16C11AltEqv (S16C11AltBits 8 k)
        (S16C11AltPact (s16c11AltEightG1 : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k)) →
      S16C11AltEqv (S16C11AltBits 8 k)
        (S16C11AltPact (s16c11AltEightG2 : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k)) →
      S16C11AltEqv (S16C11AltBits 8 k)
        (S16C11AltPact (s16c11AltEightG3 : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k)) →
      S16C11AltEqv (S16C11AltBits 8 k)
        (S16C11AltPact (s16c11AltEightG4 : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k)) →
      S16C11AltEqv (S16C11AltBits 8 k)
        (S16C11AltPact (s16c11AltEightG5 : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k)) →
      S16C11AltEqv (S16C11AltBits 8 k)
        (S16C11AltPact (s16c11AltEightG6 : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k)) →
      S16C11AltEqv s16c11AltEightX0 (S16C11AltBits 8 k) := by
  decide +kernel

theorem s16c11_altEight_uniq :
    ∀ k : Fin (2 ^ 8), ∑ i, S16C11AltBits 8 k i = 0 → ¬ S16C11AltEqv 0 (S16C11AltBits 8 k) →
      (∀ g ∈ s16c11AltEightGens, S16C11AltEqv (S16C11AltBits 8 k)
        (S16C11AltPact (g : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k))) →
      S16C11AltEqv s16c11AltEightX0 (S16C11AltBits 8 k) := fun k h0 hn hg =>
  s16c11_altEight_uniq_aux k h0 hn (hg _ (by simp [s16c11AltEightGens]))
    (hg _ (by simp [s16c11AltEightGens])) (hg _ (by simp [s16c11AltEightGens]))
    (hg _ (by simp [s16c11AltEightGens])) (hg _ (by simp [s16c11AltEightGens]))
    (hg _ (by simp [s16c11AltEightGens]))

theorem s16c11_altEight_pair :
    ∀ k : Fin (2 ^ 8), S16C11AltWt (S16C11AltBits 8 k) = S16C11AltWt s16c11AltEightX0 →
      ¬ S16C11AltEqv s16c11AltEightX0 (S16C11AltBits 8 k) →
      ¬ S16C11AltEqv s16c11AltEightXa (S16C11AltBits 8 k) →
      ¬ S16C11AltEqv s16c11AltEightXb (S16C11AltBits 8 k) →
      ∃ t₁ ∈ S16C11AltWords s16c11AltEightGens 5, ∃ t₂ ∈ S16C11AltWords s16c11AltEightGens 5,
        ¬ S16C11AltEqv (S16C11AltBits 8 k)
          (S16C11AltPact (t₁ : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k)) ∧
        ¬ S16C11AltEqv (S16C11AltBits 8 k)
          (S16C11AltPact (t₂ : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k)) ∧
        ¬ S16C11AltEqv (S16C11AltPact (t₁ : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k))
          (S16C11AltPact (t₂ : Equiv.Perm (Fin 8)) (S16C11AltBits 8 k)) := by
  rw [s16c11_altEight_words_eq]
  decide +kernel

theorem s16c11_altEight_filter_card :
    (Finset.univ.filter fun g : Equiv.Perm (Fin 8) =>
      S16C11AltEqv s16c11AltEightX0 (S16C11AltPact g s16c11AltEightX0) ∧
        S16C11AltTriple s16c11AltEightX0 s16c11AltEightXa s16c11AltEightXb g).card = 128 :=
  S16C11AltEightK.card_T _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem s16c11_altEight_sign_swap : Equiv.Perm.sign (Equiv.swap (0 : Fin 8) 1) = -1 :=
  Equiv.Perm.sign_swap (by decide)

theorem s16c11_altEight_union_card :
    ((S16C11AltWords s16c11AltEightGens 5).image Subtype.val ∪
      (S16C11AltWords s16c11AltEightGens 5).image fun t => Equiv.swap (0 : Fin 8) 1 * t.val).card
      = 128 := by
  rw [s16c11_altEight_words_eq]
  decide +kernel

theorem s16c11_altEight_union_sub_T_card :
    ((S16C11AltWords s16c11AltEightGens 5).filter fun t : ↥(alternatingGroup (Fin 8)) =>
      ¬ (S16C11AltEqv s16c11AltEightX0 (S16C11AltPact (t : Equiv.Perm (Fin 8)) s16c11AltEightX0) ∧
        S16C11AltTriple s16c11AltEightX0 s16c11AltEightXa s16c11AltEightXb
          (t : Equiv.Perm (Fin 8)))).card = 0 := by
  rw [s16c11_altEight_words_eq]
  decide +kernel

set_option maxRecDepth 100000 in
theorem s16c11_altEight_union_sub_T :
    ∀ t ∈ S16C11AltWords s16c11AltEightGens 5,
      S16C11AltEqv s16c11AltEightX0 (S16C11AltPact (t : Equiv.Perm (Fin 8)) s16c11AltEightX0) ∧
        S16C11AltTriple s16c11AltEightX0 s16c11AltEightXa s16c11AltEightXb
          (t : Equiv.Perm (Fin 8)) := by
  intro t ht
  by_contra h
  exact Finset.filter_eq_empty_iff.1
    (Finset.card_eq_zero.1 s16c11_altEight_union_sub_T_card) ht h

theorem s16c11_altEight_union_sub_S_card :
    ((S16C11AltWords s16c11AltEightGens 5).filter fun t : ↥(alternatingGroup (Fin 8)) =>
      ¬ (S16C11AltEqv s16c11AltEightX0
        (S16C11AltPact (Equiv.swap (0 : Fin 8) 1 * (t : Equiv.Perm (Fin 8))) s16c11AltEightX0) ∧
        S16C11AltTriple s16c11AltEightX0 s16c11AltEightXa s16c11AltEightXb
          (Equiv.swap (0 : Fin 8) 1 * (t : Equiv.Perm (Fin 8))))).card = 0 := by
  rw [s16c11_altEight_words_eq]
  decide +kernel

set_option maxRecDepth 100000 in
theorem s16c11_altEight_union_sub_S :
    ∀ t ∈ S16C11AltWords s16c11AltEightGens 5,
      S16C11AltEqv s16c11AltEightX0
        (S16C11AltPact (Equiv.swap (0 : Fin 8) 1 * (t : Equiv.Perm (Fin 8))) s16c11AltEightX0) ∧
        S16C11AltTriple s16c11AltEightX0 s16c11AltEightXa s16c11AltEightXb
          (Equiv.swap (0 : Fin 8) 1 * (t : Equiv.Perm (Fin 8))) := by
  intro t ht
  by_contra h
  exact Finset.filter_eq_empty_iff.1
    (Finset.card_eq_zero.1 s16c11_altEight_union_sub_S_card) ht h

set_option maxRecDepth 100000 in
theorem s16c11_altEight_union_sub :
    ∀ w ∈ (S16C11AltWords s16c11AltEightGens 5).image Subtype.val ∪
      (S16C11AltWords s16c11AltEightGens 5).image fun t => Equiv.swap (0 : Fin 8) 1 * t.val,
      S16C11AltEqv s16c11AltEightX0 (S16C11AltPact w s16c11AltEightX0) ∧
        S16C11AltTriple s16c11AltEightX0 s16c11AltEightXa s16c11AltEightXb w := by
  intro w hw
  rcases Finset.mem_union.1 hw with h | h
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
    exact s16c11_altEight_union_sub_T t ht
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
    exact s16c11_altEight_union_sub_S t ht

set_option maxRecDepth 100000 in
theorem s16c11_altEight_pass :
    ∀ g : Equiv.Perm (Fin 8),
      S16C11AltTriple s16c11AltEightX0 s16c11AltEightXa s16c11AltEightXb g →
      S16C11AltEqv s16c11AltEightX0 (S16C11AltPact g s16c11AltEightX0) → Equiv.Perm.sign g = 1 →
      g ∈ (S16C11AltWords s16c11AltEightGens 5).image Subtype.val := fun g h1 h2 h3 =>
  s16c11_alt_pass_of_card s16c11AltEightGens 5 (Equiv.swap (0 : Fin 8) 1)
    s16c11_altEight_sign_swap
    (fun g => S16C11AltEqv s16c11AltEightX0 (S16C11AltPact g s16c11AltEightX0) ∧
      S16C11AltTriple s16c11AltEightX0 s16c11AltEightXa s16c11AltEightXb g)
    128 s16c11_altEight_filter_card s16c11_altEight_union_card s16c11_altEight_union_sub g
    ⟨h2, h1⟩ h3

theorem s16c11_altEight_hfix :
    ∀ g ∈ s16c11AltEightGens,
      S16C11AltEqv s16c11AltEightX0 (S16C11AltPact (g : Equiv.Perm (Fin 8)) s16c11AltEightX0) := by
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  exact absurd hg List.not_mem_nil

theorem s16c11_altEight_hstab :
    ∀ g ∈ s16c11AltEightGens,
      S16C11AltTriple s16c11AltEightX0 s16c11AltEightXa s16c11AltEightXb
        (g : Equiv.Perm (Fin 8)) := by
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  rcases List.mem_cons.1 hg with rfl | hg
  · decide +kernel
  exact absurd hg List.not_mem_nil

set_option maxRecDepth 100000 in
theorem s16c11_altEight_forced :
    ∃ (T₁ : Subgroup (FFModel.altDn 8).Gam) (N : ℕ) (y₀ a b : (FFModel.altDn 8).Mod),
      IsPGroup 2 ↥T₁ ∧ ¬ 2 ∣ T₁.index ∧ S16C11Forced (S16C11AltAct 8) T₁ N y₀ a b ∧
      T₁ ≤ S16C11SetStab (S16C11AltAct 8) {y₀, a, b} ∧
      T₁.relIndex (S16C11SetStab (S16C11AltAct 8) {y₀, a, b}) = 3 ∧
      ∃ g ∈ S16C11SetStab (S16C11AltAct 8) {y₀, a, b}, S16C11AltAct 8 g y₀ ≠ y₀ :=
  s16c11_alt_forced_even_of_checks s16c11AltEightGens 5 6 315 s16c11_altEight_words_fix
    s16c11_altEight_words_card s16c11_altEight_card (by decide)
    (x₀ := s16c11AltEightX0) (xa := s16c11AltEightXa) (xb := s16c11AltEightXb)
    s16c11AltEightSa s16c11AltEightSb (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    s16c11_altEight_hfix s16c11_altEight_hstab s16c11_altEight_uniq
    s16c11_altEight_pair s16c11_altEight_pass (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
