module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltCount
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Equiv

@[expose] def s16c11AltSevenG1 : ↥(alternatingGroup (Fin 7)) :=
  ⟨(swap 0 1 * swap 1 2 * swap 2 3) * swap 4 5, by
    rw [Perm.mem_alternatingGroup]
    decide⟩

@[expose] def s16c11AltSevenG2 : ↥(alternatingGroup (Fin 7)) :=
  S16C11AltSw2 0 2 4 5 (by decide) (by decide)

@[expose] def s16c11AltSevenGens : List ↥(alternatingGroup (Fin 7)) :=
  [s16c11AltSevenG1, s16c11AltSevenG2]

@[expose] def s16c11AltSevenC1 : ↥(alternatingGroup (Fin 7)) :=
  S16C11AltSw2 4 5 5 6 (by decide) (by decide)

@[expose] def s16c11AltSevenC2 : ↥(alternatingGroup (Fin 7)) :=
  S16C11AltSw2 0 1 1 2 (by decide) (by decide) * S16C11AltSw2 4 5 5 6 (by decide) (by decide)

@[expose] def s16c11AltSevenC3 : ↥(alternatingGroup (Fin 7)) :=
  S16C11AltSw2 0 1 1 2 (by decide) (by decide) * S16C11AltSw2 5 6 4 5 (by decide) (by decide)

@[expose] def s16c11AltSevenGens1 : List ↥(alternatingGroup (Fin 7)) :=
  s16c11AltSevenGens ++ [s16c11AltSevenC1]

@[expose] def s16c11AltSevenGens2 : List ↥(alternatingGroup (Fin 7)) :=
  s16c11AltSevenGens ++ [s16c11AltSevenC2]

@[expose] def s16c11AltSevenGens3 : List ↥(alternatingGroup (Fin 7)) :=
  s16c11AltSevenGens ++ [s16c11AltSevenC3]

@[expose] def s16c11AltSevenX0 : Fin 7 → ZMod 2 := ![1, 1, 1, 1, 1, 1, 0]

@[expose] def s16c11AltSevenXa : Fin 7 → ZMod 2 := ![1, 1, 1, 1, 0, 1, 1]

@[expose] def s16c11AltSevenXb : Fin 7 → ZMod 2 := ![1, 1, 1, 1, 1, 0, 1]

@[expose] def s16c11AltSevenCs : List (Fin 7 → ZMod 2) :=
  [![0, 1, 1, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 1, 1], ![1, 1, 0, 1, 1, 1, 1], ![1, 1, 1, 0, 1, 1, 1],
    ![1, 1, 1, 1, 0, 1, 1], ![1, 1, 1, 1, 1, 0, 1], ![1, 1, 1, 1, 1, 1, 0]]

@[expose] def s16c11AltSevenXs : List (Fin 7 → ZMod 2) :=
  [![1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0]]

@[expose] def s16c11AltSevenL1 : List ↥(alternatingGroup (Fin 7)) :=
  [1, S16C11AltSw2 0 4 1 5 (by decide) (by decide), S16C11AltSw2 0 4 2 5 (by decide) (by decide),
    S16C11AltSw2 0 4 3 5 (by decide) (by decide), S16C11AltSw2 1 4 2 5 (by decide) (by decide),
    S16C11AltSw2 1 4 3 5 (by decide) (by decide), S16C11AltSw2 2 4 3 5 (by decide) (by decide),
    S16C11AltSw2 0 4 1 6 (by decide) (by decide)]

@[expose] def s16c11AltSevenL2 : List ↥(alternatingGroup (Fin 7)) :=
  [1, S16C11AltSw2 4 0 5 1 (by decide) (by decide), S16C11AltSw2 4 0 5 2 (by decide) (by decide),
    S16C11AltSw2 4 0 5 3 (by decide) (by decide), S16C11AltSw2 4 1 5 2 (by decide) (by decide),
    S16C11AltSw2 4 1 5 3 (by decide) (by decide), S16C11AltSw2 4 2 5 3 (by decide) (by decide),
    S16C11AltSw2 4 0 5 6 (by decide) (by decide)]

theorem s16c11_altSeven_words_fix :
    S16C11AltWords s16c11AltSevenGens 4 = S16C11AltWords s16c11AltSevenGens 3 := by
  decide +kernel

theorem s16c11_altSeven_words_card : (S16C11AltWords s16c11AltSevenGens 3).card = 2 ^ 3 := by
  decide +kernel

theorem s16c11_altSeven_card : Nat.card ↥(alternatingGroup (Fin 7)) = 2 ^ 3 * 315 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem s16c11_altSeven_orbit_card :
    (Finset.univ.filter fun g : Equiv.Perm (Fin 7) =>
      ¬ ∃ w ∈ s16c11AltSevenCs, S16C11AltPact g s16c11AltSevenX0 = w).card = 0 := by
  open scoped CFSG.Decide.Bounded in
  rw [Finset.filter_congr_decidable]
  decide +kernel

theorem s16c11_altSeven_orbit :
    ∀ g : Equiv.Perm (Fin 7), ∃ w ∈ s16c11AltSevenCs, S16C11AltPact g s16c11AltSevenX0 = w := by
  intro g
  by_contra h
  have hmem : g ∈ Finset.univ.filter fun g : Equiv.Perm (Fin 7) =>
      ¬ ∃ w ∈ s16c11AltSevenCs, S16C11AltPact g s16c11AltSevenX0 = w :=
    Finset.mem_filter.2 ⟨Finset.mem_univ g, h⟩
  rw [Finset.card_eq_zero.1 s16c11_altSeven_orbit_card] at hmem
  exact absurd hmem (by simp)

open scoped CFSG.Decide.Bounded in
theorem s16c11_altSeven_uniq :
    ∀ k : Fin (2 ^ 7), ∑ i, S16C11AltBits 7 k i = 0 → ¬ S16C11AltEqv 0 (S16C11AltBits 7 k) →
      (∀ g ∈ s16c11AltSevenGens, S16C11AltEqv (S16C11AltBits 7 k)
        (S16C11AltPact (g : Equiv.Perm (Fin 7)) (S16C11AltBits 7 k))) →
      S16C11AltEqv s16c11AltSevenX0 (S16C11AltBits 7 k) ∨
        ∃ w ∈ s16c11AltSevenXs, S16C11AltEqv w (S16C11AltBits 7 k) := by
  decide +kernel

theorem s16c11_altSeven_L1 :
    (s16c11AltSevenL1.map fun g => S16C11AltPact (g : Equiv.Perm (Fin 7))
      ![1, 1, 1, 1, 0, 0, 0]).Pairwise fun a b => ¬ S16C11AltEqv a b := by
  decide +kernel

theorem s16c11_altSeven_L2 :
    (s16c11AltSevenL2.map fun g => S16C11AltPact (g : Equiv.Perm (Fin 7))
      ![0, 0, 0, 0, 1, 1, 0]).Pairwise fun a b => ¬ S16C11AltEqv a b := by
  decide +kernel

theorem s16c11_altSeven_pair :
    ∀ k : Fin (2 ^ 7), S16C11AltWt (S16C11AltBits 7 k) = S16C11AltWt s16c11AltSevenX0 →
      ¬ S16C11AltEqv s16c11AltSevenX0 (S16C11AltBits 7 k) →
      ¬ S16C11AltEqv s16c11AltSevenXa (S16C11AltBits 7 k) →
      ¬ S16C11AltEqv s16c11AltSevenXb (S16C11AltBits 7 k) →
      ∃ t₁ ∈ S16C11AltWords s16c11AltSevenGens 3, ∃ t₂ ∈ S16C11AltWords s16c11AltSevenGens 3,
        ¬ S16C11AltEqv (S16C11AltBits 7 k)
          (S16C11AltPact (t₁ : Equiv.Perm (Fin 7)) (S16C11AltBits 7 k)) ∧
        ¬ S16C11AltEqv (S16C11AltBits 7 k)
          (S16C11AltPact (t₂ : Equiv.Perm (Fin 7)) (S16C11AltBits 7 k)) ∧
        ¬ S16C11AltEqv (S16C11AltPact (t₁ : Equiv.Perm (Fin 7)) (S16C11AltBits 7 k))
          (S16C11AltPact (t₂ : Equiv.Perm (Fin 7)) (S16C11AltBits 7 k)) := by
  decide +kernel

theorem s16c11_altSeven_words_fix1 :
    S16C11AltWords s16c11AltSevenGens1 5 = S16C11AltWords s16c11AltSevenGens1 4 := by
  decide +kernel

theorem s16c11_altSeven_words_card1 :
    (S16C11AltWords s16c11AltSevenGens1 4).card = 2 ^ 3 * 3 := by
  decide +kernel

theorem s16c11_altSeven_words_fix2 :
    S16C11AltWords s16c11AltSevenGens2 5 = S16C11AltWords s16c11AltSevenGens2 4 := by
  decide +kernel

theorem s16c11_altSeven_words_card2 :
    (S16C11AltWords s16c11AltSevenGens2 4).card = 2 ^ 3 * 3 := by
  decide +kernel

theorem s16c11_altSeven_words_fix3 :
    S16C11AltWords s16c11AltSevenGens3 5 = S16C11AltWords s16c11AltSevenGens3 4 := by
  decide +kernel

theorem s16c11_altSeven_words_card3 :
    (S16C11AltWords s16c11AltSevenGens3 4).card = 2 ^ 3 * 3 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem s16c11_altSeven_stab :
    (∀ g ∈ s16c11AltSevenGens1, S16C11AltTriple s16c11AltSevenX0 s16c11AltSevenXa
      s16c11AltSevenXb (g : Equiv.Perm (Fin 7))) ∧
    (∀ g ∈ s16c11AltSevenGens2, S16C11AltTriple s16c11AltSevenX0 s16c11AltSevenXa
      s16c11AltSevenXb (g : Equiv.Perm (Fin 7))) ∧
    (∀ g ∈ s16c11AltSevenGens3, S16C11AltTriple s16c11AltSevenX0 s16c11AltSevenXa
      s16c11AltSevenXb (g : Equiv.Perm (Fin 7))) := by
  decide +kernel

theorem s16c11_altSeven_mov :
    (¬ S16C11AltEqv s16c11AltSevenX0
      (S16C11AltPact (s16c11AltSevenC1 : Equiv.Perm (Fin 7)) s16c11AltSevenX0)) ∧
    (¬ S16C11AltEqv s16c11AltSevenX0
      (S16C11AltPact (s16c11AltSevenC2 : Equiv.Perm (Fin 7)) s16c11AltSevenX0)) ∧
    (¬ S16C11AltEqv s16c11AltSevenX0
      (S16C11AltPact (s16c11AltSevenC3 : Equiv.Perm (Fin 7)) s16c11AltSevenX0)) := by
  decide +kernel

theorem s16c11_altSeven_ne :
    ((s16c11AltSevenC2 : Equiv.Perm (Fin 7)) ∉
      (S16C11AltWords s16c11AltSevenGens1 4).image Subtype.val) ∧
    ((s16c11AltSevenC3 : Equiv.Perm (Fin 7)) ∉
      (S16C11AltWords s16c11AltSevenGens1 4).image Subtype.val) ∧
    ((s16c11AltSevenC3 : Equiv.Perm (Fin 7)) ∉
      (S16C11AltWords s16c11AltSevenGens2 4).image Subtype.val) := by
  decide +kernel

theorem s16c11_altSeven_cover_card :
    (Finset.univ.filter fun g : Equiv.Perm (Fin 7) =>
      S16C11AltTriple s16c11AltSevenX0 s16c11AltSevenXa s16c11AltSevenXb g ∧ g ^ 3 = 1 ∧
      ¬ S16C11AltEqv s16c11AltSevenX0 (S16C11AltPact g s16c11AltSevenX0) ∧
      ¬ (g ∈ (S16C11AltWords s16c11AltSevenGens1 4).image Subtype.val ∨
        g ∈ (S16C11AltWords s16c11AltSevenGens2 4).image Subtype.val ∨
        g ∈ (S16C11AltWords s16c11AltSevenGens3 4).image Subtype.val)).card = 0 := by
  decide +kernel

theorem s16c11_altSeven_cover :
    ∀ g : Equiv.Perm (Fin 7),
      S16C11AltTriple s16c11AltSevenX0 s16c11AltSevenXa s16c11AltSevenXb g → g ^ 3 = 1 →
      ¬ S16C11AltEqv s16c11AltSevenX0 (S16C11AltPact g s16c11AltSevenX0) →
      g ∈ (S16C11AltWords s16c11AltSevenGens1 4).image Subtype.val ∨
        g ∈ (S16C11AltWords s16c11AltSevenGens2 4).image Subtype.val ∨
        g ∈ (S16C11AltWords s16c11AltSevenGens3 4).image Subtype.val := by
  intro g h1 h2 h3
  by_contra h4
  have hmem : g ∈ Finset.univ.filter fun g : Equiv.Perm (Fin 7) =>
      S16C11AltTriple s16c11AltSevenX0 s16c11AltSevenXa s16c11AltSevenXb g ∧ g ^ 3 = 1 ∧
      ¬ S16C11AltEqv s16c11AltSevenX0 (S16C11AltPact g s16c11AltSevenX0) ∧
      ¬ (g ∈ (S16C11AltWords s16c11AltSevenGens1 4).image Subtype.val ∨
        g ∈ (S16C11AltWords s16c11AltSevenGens2 4).image Subtype.val ∨
        g ∈ (S16C11AltWords s16c11AltSevenGens3 4).image Subtype.val) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ g, h1, h2, h3, h4⟩
  rw [Finset.card_eq_zero.1 s16c11_altSeven_cover_card] at hmem
  exact absurd hmem (by simp)

theorem s16c11_altSeven_sum_x0 : ∑ i, s16c11AltSevenX0 i = 0 := by
  decide +kernel

theorem s16c11_altSeven_sum_xa : ∑ i, s16c11AltSevenXa i = 0 := by
  decide +kernel

theorem s16c11_altSeven_sum_xb : ∑ i, s16c11AltSevenXb i = 0 := by
  decide +kernel

theorem s16c11_altSeven_x0_ne_zero : ¬ S16C11AltEqv 0 s16c11AltSevenX0 := by
  decide +kernel

theorem s16c11_altSeven_xa_ne_xb : ¬ S16C11AltEqv s16c11AltSevenXa s16c11AltSevenXb := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem s16c11_altSeven_hfix :
    ∀ g ∈ s16c11AltSevenGens, S16C11AltEqv s16c11AltSevenX0
      (S16C11AltPact (g : Equiv.Perm (Fin 7)) s16c11AltSevenX0) := by
  decide +kernel

theorem s16c11_altSeven_Cs_length : s16c11AltSevenCs.length ≤ 7 := by
  decide +kernel

theorem s16c11_altSeven_sum_xs : ∀ w ∈ s16c11AltSevenXs, ∑ i, w i = 0 := by
  decide +kernel

theorem s16c11_altSeven_L1_length : 7 < s16c11AltSevenL1.length := by
  decide +kernel

theorem s16c11_altSeven_L2_length : 7 < s16c11AltSevenL2.length := by
  decide +kernel

theorem s16c11_altSeven_pgroup :
    IsPGroup 2 ↥(S16C11AltGrp s16c11AltSevenGens) ∧
      ¬ 2 ∣ (S16C11AltGrp s16c11AltSevenGens).index :=
  s16c11_alt_pgroup_of_words s16c11AltSevenGens 3 3 315 s16c11_altSeven_words_fix
    s16c11_altSeven_words_card s16c11_altSeven_card (by decide)

theorem s16c11_altSeven_words_mem (gens : List ↥(alternatingGroup (Fin 7))) (k : ℕ) :
    ∀ t ∈ S16C11AltWords gens k, t ∈ S16C11AltGrp gens :=
  fun t ht => s16c11_alt_words_subset_closure gens k (Finset.mem_coe.2 ht)

theorem s16c11_altSeven_isForced :
    S16C11Forced (S16C11AltAct 7) (S16C11AltGrp s16c11AltSevenGens) 7
      (S16C11AltCls 7 s16c11AltSevenX0) (S16C11AltCls 7 s16c11AltSevenXa)
      (S16C11AltCls 7 s16c11AltSevenXb) := by
  have horb : {z : (FFModel.altDn 7).Mod | ∃ g : ↥(alternatingGroup (Fin 7)),
      S16C11AltAct 7 g (S16C11AltCls 7 s16c11AltSevenX0) = z}.ncard ≤ 7 :=
    (s16c11_alt_ncard_orbit_le s16c11_altSeven_sum_x0 s16c11AltSevenCs
      s16c11_altSeven_orbit).trans s16c11_altSeven_Cs_length
  have hlarge : ∀ w ∈ s16c11AltSevenXs, 7 < {z : (FFModel.altDn 7).Mod |
      ∃ g : ↥(alternatingGroup (Fin 7)), S16C11AltAct 7 g (S16C11AltCls 7 w) = z}.ncard := by
    intro w hw
    have hs := s16c11_altSeven_sum_xs w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact lt_of_lt_of_le s16c11_altSeven_L1_length
        (s16c11_alt_le_ncard_orbit hs s16c11AltSevenL1 s16c11_altSeven_L1)
    · rw [List.mem_singleton] at hw
      subst hw
      exact lt_of_lt_of_le s16c11_altSeven_L2_length
        (s16c11_alt_le_ncard_orbit hs s16c11AltSevenL2 s16c11_altSeven_L2)
  have huniq := s16c11_alt_uniq_of_check_large s16c11AltSevenGens s16c11_altSeven_sum_x0 7
    s16c11AltSevenXs s16c11_altSeven_sum_xs hlarge s16c11_altSeven_uniq
  exact s16c11_alt_forced_of_checks s16c11AltSevenGens (S16C11AltWords s16c11AltSevenGens 3)
    (s16c11_altSeven_words_mem s16c11AltSevenGens 3)
    s16c11_altSeven_sum_x0 s16c11_altSeven_sum_xa s16c11_altSeven_sum_xb
    s16c11_altSeven_x0_ne_zero s16c11_altSeven_hfix horb huniq s16c11_altSeven_xa_ne_xb
    s16c11_altSeven_pair

theorem s16c11_altSeven_overgroup1 :
    S16C11AltGrp s16c11AltSevenGens ≤ S16C11AltGrp s16c11AltSevenGens1 ∧
      S16C11AltGrp s16c11AltSevenGens1 ≤ S16C11SetStab (S16C11AltAct 7)
        {S16C11AltCls 7 s16c11AltSevenX0, S16C11AltCls 7 s16c11AltSevenXa,
          S16C11AltCls 7 s16c11AltSevenXb} ∧
      (S16C11AltGrp s16c11AltSevenGens).relIndex (S16C11AltGrp s16c11AltSevenGens1) = 3 ∧
      ∃ g ∈ S16C11AltGrp s16c11AltSevenGens1,
        S16C11AltAct 7 g (S16C11AltCls 7 s16c11AltSevenX0) ≠ S16C11AltCls 7 s16c11AltSevenX0 :=
  s16c11_alt_overgroup_of_checks s16c11AltSevenGens s16c11AltSevenC1 3 3 4
    s16c11_altSeven_words_fix s16c11_altSeven_words_card s16c11_altSeven_words_fix1
    s16c11_altSeven_words_card1 s16c11_altSeven_sum_x0 s16c11_altSeven_sum_xa
    s16c11_altSeven_sum_xb s16c11_altSeven_stab.1 s16c11_altSeven_mov.1

theorem s16c11_altSeven_overgroup2 :
    S16C11AltGrp s16c11AltSevenGens ≤ S16C11AltGrp s16c11AltSevenGens2 ∧
      S16C11AltGrp s16c11AltSevenGens2 ≤ S16C11SetStab (S16C11AltAct 7)
        {S16C11AltCls 7 s16c11AltSevenX0, S16C11AltCls 7 s16c11AltSevenXa,
          S16C11AltCls 7 s16c11AltSevenXb} ∧
      (S16C11AltGrp s16c11AltSevenGens).relIndex (S16C11AltGrp s16c11AltSevenGens2) = 3 ∧
      ∃ g ∈ S16C11AltGrp s16c11AltSevenGens2,
        S16C11AltAct 7 g (S16C11AltCls 7 s16c11AltSevenX0) ≠ S16C11AltCls 7 s16c11AltSevenX0 :=
  s16c11_alt_overgroup_of_checks s16c11AltSevenGens s16c11AltSevenC2 3 3 4
    s16c11_altSeven_words_fix s16c11_altSeven_words_card s16c11_altSeven_words_fix2
    s16c11_altSeven_words_card2 s16c11_altSeven_sum_x0 s16c11_altSeven_sum_xa
    s16c11_altSeven_sum_xb s16c11_altSeven_stab.2.1 s16c11_altSeven_mov.2.1

theorem s16c11_altSeven_overgroup3 :
    S16C11AltGrp s16c11AltSevenGens ≤ S16C11AltGrp s16c11AltSevenGens3 ∧
      S16C11AltGrp s16c11AltSevenGens3 ≤ S16C11SetStab (S16C11AltAct 7)
        {S16C11AltCls 7 s16c11AltSevenX0, S16C11AltCls 7 s16c11AltSevenXa,
          S16C11AltCls 7 s16c11AltSevenXb} ∧
      (S16C11AltGrp s16c11AltSevenGens).relIndex (S16C11AltGrp s16c11AltSevenGens3) = 3 ∧
      ∃ g ∈ S16C11AltGrp s16c11AltSevenGens3,
        S16C11AltAct 7 g (S16C11AltCls 7 s16c11AltSevenX0) ≠ S16C11AltCls 7 s16c11AltSevenX0 :=
  s16c11_alt_overgroup_of_checks s16c11AltSevenGens s16c11AltSevenC3 3 3 4
    s16c11_altSeven_words_fix s16c11_altSeven_words_card s16c11_altSeven_words_fix3
    s16c11_altSeven_words_card3 s16c11_altSeven_sum_x0 s16c11_altSeven_sum_xa
    s16c11_altSeven_sum_xb s16c11_altSeven_stab.2.2 s16c11_altSeven_mov.2.2

theorem s16c11_altSeven_grp_ne :
    S16C11AltGrp s16c11AltSevenGens1 ≠ S16C11AltGrp s16c11AltSevenGens2 ∧
      S16C11AltGrp s16c11AltSevenGens1 ≠ S16C11AltGrp s16c11AltSevenGens3 ∧
      S16C11AltGrp s16c11AltSevenGens2 ≠ S16C11AltGrp s16c11AltSevenGens3 :=
  ⟨s16c11_alt_grp_ne_of_mem s16c11AltSevenGens1 s16c11AltSevenGens2 4
      s16c11_altSeven_words_fix1 (g := s16c11AltSevenC2)
      (List.mem_append_right _ (List.mem_singleton_self _)) s16c11_altSeven_ne.1,
    s16c11_alt_grp_ne_of_mem s16c11AltSevenGens1 s16c11AltSevenGens3 4
      s16c11_altSeven_words_fix1 (g := s16c11AltSevenC3)
      (List.mem_append_right _ (List.mem_singleton_self _)) s16c11_altSeven_ne.2.1,
    s16c11_alt_grp_ne_of_mem s16c11AltSevenGens2 s16c11AltSevenGens3 4
      s16c11_altSeven_words_fix2 (g := s16c11AltSevenC3)
      (List.mem_append_right _ (List.mem_singleton_self _)) s16c11_altSeven_ne.2.2⟩

theorem s16c11_altSeven_cover_stab :
    ∀ g ∈ S16C11SetStab (S16C11AltAct 7)
        {S16C11AltCls 7 s16c11AltSevenX0, S16C11AltCls 7 s16c11AltSevenXa,
          S16C11AltCls 7 s16c11AltSevenXb},
      g ^ 3 = 1 → S16C11AltAct 7 g (S16C11AltCls 7 s16c11AltSevenX0) ≠
        S16C11AltCls 7 s16c11AltSevenX0 →
      g ∈ S16C11AltGrp s16c11AltSevenGens1 ∨ g ∈ S16C11AltGrp s16c11AltSevenGens2 ∨
        g ∈ S16C11AltGrp s16c11AltSevenGens3 :=
  s16c11_alt_cover_of_check s16c11AltSevenGens1 s16c11AltSevenGens2 s16c11AltSevenGens3 4 4 4
    s16c11_altSeven_sum_x0 s16c11_altSeven_sum_xa s16c11_altSeven_sum_xb
    fun g h1 h2 h3 _ => s16c11_altSeven_cover g h1 h2 h3

theorem s16c11_altSeven_pairs_ncard :
    (S16C11ForcedPairs (S16C11AltAct 7) (S16C11AltGrp s16c11AltSevenGens)
      (S16C11AltCls 7 s16c11AltSevenX0) (S16C11AltCls 7 s16c11AltSevenXa)
      (S16C11AltCls 7 s16c11AltSevenXb)).ncard = 3 := by
  obtain ⟨hP, -⟩ := s16c11_altSeven_pgroup
  obtain ⟨hl1, hS1, hi1, hm1⟩ := s16c11_altSeven_overgroup1
  obtain ⟨hl2, hS2, hi2, hm2⟩ := s16c11_altSeven_overgroup2
  obtain ⟨hl3, hS3, hi3, hm3⟩ := s16c11_altSeven_overgroup3
  obtain ⟨d12, d13, d23⟩ := s16c11_altSeven_grp_ne
  have hfixT : ∀ t ∈ S16C11AltGrp s16c11AltSevenGens,
      S16C11AltAct 7 t (S16C11AltCls 7 s16c11AltSevenX0) = S16C11AltCls 7 s16c11AltSevenX0 :=
    s16c11_alt_grp_fixes fun g hg =>
      (s16c11_alt_fixed_iff g s16c11_altSeven_sum_x0).2 (s16c11_altSeven_hfix g hg)
  haveI : Finite (FFModel.altDn 7).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 7)))
  exact s16c11_forcedPairs_ncard_three_of_cover hP hfixT hl1 hl2 hl3 hS1 hS2 hS3
    hi1 hi2 hi3 hm1 hm2 hm3 d12 d13 d23 s16c11_altSeven_cover_stab

theorem s16c11_altSeven_forced :
    ∃ (T₁ : Subgroup (FFModel.altDn 7).Gam) (N : ℕ) (y₀ a b : (FFModel.altDn 7).Mod),
      IsPGroup 2 ↥T₁ ∧ ¬ 2 ∣ T₁.index ∧ S16C11Forced (S16C11AltAct 7) T₁ N y₀ a b ∧
      (S16C11ForcedPairs (S16C11AltAct 7) T₁ y₀ a b).ncard = 3 := by
  obtain ⟨hP, hidx⟩ := s16c11_altSeven_pgroup
  exact ⟨S16C11AltGrp s16c11AltSevenGens, 7, S16C11AltCls 7 s16c11AltSevenX0,
    S16C11AltCls 7 s16c11AltSevenXa, S16C11AltCls 7 s16c11AltSevenXb, hP, hidx,
    s16c11_altSeven_isForced, s16c11_altSeven_pairs_ncard⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
