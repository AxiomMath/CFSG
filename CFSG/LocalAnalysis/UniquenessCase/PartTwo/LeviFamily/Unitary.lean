module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Blocks
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.BlocksSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Parabolic
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Unitary
import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.AGLEmbedding.LeviBlock CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
open scoped Pointwise

private theorem isLeviBlock_hypSU_one_zero_of_two_le {K : Type} [Field K] [Finite K] {f : ℕ}
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    IsLeviBlock ↥(hypSU h 1 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := exists_hypSU_one_zero_mulEquiv h
  let : Field F := hFfield
  have : Finite F := hFfin
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hFcard
  have hne : Nat.card F ≠ 2 := by
    rw [hFcard]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hbot : (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range ≠ ⊥ := by
    rw [Ne, range_toGL_eq_bot_iff]
    omega
  have hL := (range_toGL_eq_bot_or_isLeviBlock (K := F) 2).resolve_left hbot
  exact IsLeviBlock.of_mulEquiv (e.trans (slEquivToGLRange (K := F) 2)).symm hL

private theorem isLeviBlock_hypSU_one_zero_of_eq_one {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 1 K) : IsLeviBlock ↥(hypSU h 1 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := exists_hypSU_one_zero_mulEquiv h
  let : Field F := hFfield
  have : Finite F := hFfin
  have : Fintype F := Fintype.ofFinite F
  have hF : Nat.card F = 2 := by simpa using hFcard
  have : CharP F 2 := by
    apply charP_of_card_eq_prime_pow (f := 1)
    simpa using hF
  obtain ⟨e2⟩ := CFSG.StandardType.RCSPSL.nonempty_sl2_equiv_perm (F := F) hF
  exact Or.inl ⟨e.trans e2⟩

private theorem isLeviBlock_hypSU_one_one_two {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 2 K) : IsLeviBlock ↥(hypSU h 1 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have hdim : 3 ≤ 2 * 1 + 1 := by norm_num
  have hne : (2 * 1 + 1, 2 ^ 2) ≠ (3, 2) := by norm_num
  obtain ⟨hq, -⟩ := hypSU_facts_of_three_le (p := 2) (f := 2) (s := 1) (ε := 1) h hdim hne
  have hcenter := center_hypSU_eq_hypScalars_of_three_le
    (h := h) (s := 1) (ε := 1) (f := 2) (by norm_num) hdim hne
  have hodd : Odd (Nat.card (Subgroup.center (hypSU h 1 1))) := by
    rw [hcenter, card_hypScalars h (by norm_num)]
    norm_num
  have h2 : 2 ∣ Nat.card (hypSU h 1 1) := by
    have hq' := (hypSU_facts_of_three_le (p := 2) (f := 2) (s := 1) (ε := 1) h hdim hne).2
    norm_num at hq'
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (hypSU h 1 1))
    rw [hq'] at hcard
    rw [hcard]
    have h62400 : ordTwistedA 2 4 = 62400 := by decide
    rw [h62400]
    exact (show 2 ∣ 62400 by norm_num).mul_right _
  exact Or.inr (Or.inr ⟨hq, hodd, h2⟩)

private theorem hypSU_eq_bot_or_isLeviBlock_of_dim_le_three {K : Type} [Field K] [Finite K]
    {f s ε : ℕ} (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    (hdim : 2 * s + ε ≤ 3) (h3 : 2 * s + ε = 3 → f = 2) :
    hypSU h s ε = ⊥ ∨ IsLeviBlock ↥(hypSU h s ε) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have : Subsingleton (hypSU h 0 ε) := subsingleton_hypSU_zero h hε
    exact Or.inl (Subgroup.eq_bot_of_subsingleton _)
  · have hs1 : s = 1 := by omega
    subst hs1
    rcases Nat.eq_zero_or_pos ε with rfl | hεpos
    · by_cases hf : f = 1
      · subst hf
        exact Or.inr (isLeviBlock_hypSU_one_zero_of_eq_one h)
      · have hf2 : 2 ≤ f := by have := h.one_le; omega
        exact Or.inr (isLeviBlock_hypSU_one_zero_of_two_le h hf2)
    · have hε1 : ε = 1 := by omega
      subst hε1
      have hf : f = 2 := h3 (by norm_num)
      subst hf
      exact Or.inr (isLeviBlock_hypSU_one_one_two h)

private theorem uniBlockSub_some_eq_bot_of_le_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {f s ε : ℕ} (hU : UnitaryFieldData 2 f K) {I : Finset ℕ} {b : ↥I}
    (hb : b.1 - predCut I b.1 ≤ 1) :
    uniBlockSub (s := s) (ε := ε) hU I (some b) = ⊥ := by
  change (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →*
      GL (Fin (b.1 - predCut I b.1)) K).range = ⊥
  exact (range_toGL_eq_bot_iff _).mpr hb

private theorem uniBlockSub_some_isLeviBlock_of_two_le {K : Type} [Field K] [Finite K]
    [CharP K 2] {f s ε : ℕ} (hU : UnitaryFieldData 2 f K) {I : Finset ℕ} {b : ↥I}
    (hb : 2 ≤ b.1 - predCut I b.1) :
    IsLeviBlock ↥(uniBlockSub (s := s) (ε := ε) hU I (some b)) := by
  have hbot : (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →*
        GL (Fin (b.1 - predCut I b.1)) K).range ≠ ⊥ := by
    rw [Ne, range_toGL_eq_bot_iff]
    omega
  exact (range_toGL_eq_bot_or_isLeviBlock (K := K) _).resolve_left hbot

private theorem uniBlockSub_some_isQuasisimple_of_two_le {K : Type} [Field K] [Finite K]
    [CharP K 2] {f s ε : ℕ} (hU : UnitaryFieldData 2 f K) {I : Finset ℕ} {b : ↥I}
    (hK : Nat.card K ≠ 2) (hb : 2 ≤ b.1 - predCut I b.1) :
    CFSG.Open.IsQuasisimple ↥(uniBlockSub (s := s) (ε := ε) hU I (some b)) := by
  have hbot : (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →*
        GL (Fin (b.1 - predCut I b.1)) K).range ≠ ⊥ := by
    rw [Ne, range_toGL_eq_bot_iff]
    omega
  exact (range_toGL_eq_bot_or_isQuasisimple hK _).resolve_left hbot

private theorem not_isL2_uniBlockSub_some_of_f_eq_one {K : Type} [Field K] [Finite K]
    [CharP K 2] {f s ε : ℕ} (hU : UnitaryFieldData 2 f K) {I : Finset ℕ} {b : ↥I}
    (hf : f = 1) (hm2 : b.1 - predCut I b.1 = 2) {m : ℕ} (hm : 3 ≤ m) :
    ¬ IsL2 (↥(uniBlockSub (s := s) (ε := ε) hU I (some b)) ⧸
      Subgroup.center ↥(uniBlockSub (s := s) (ε := ε) hU I (some b))) m := by
  have hS : uniBlockSub (s := s) (ε := ε) hU I (some b) =
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →*
          GL (Fin (b.1 - predCut I b.1)) K).range := rfl
  refine not_isL2_of_card_lt ?_ hm
  rw [hS, card_range_toGL_quotient_center (m := b.1 - predCut I b.1) (K := K) (by omega)]
  have hm1 : b.1 - predCut I b.1 - 1 = 1 := by omega
  have hK : Nat.card K = 4 := by rw [hU.card, hf]; norm_num
  rw [hm1, hK]
  have h60 : ordA 1 4 = 60 := by decide
  rw [h60]
  norm_num

private theorem block_bot_or_isLeviBlock {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε)
    (hnf : n = 4 ∨ (n = 5 ∧ f = 2)) :
    ∀ j : Option ↥I, uniBlockSub (s := s) (ε := ε) hU I j = ⊥ ∨
      IsLeviBlock ↥(uniBlockSub (s := s) (ε := ε) hU I j) := by
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hdim : 2 * s + ε ≤ 3 := by omega
  have h3 : 2 * s + ε = 3 → f = 2 := by
    intro h3
    rcases hnf with h4 | ⟨h5, hf2⟩
    · omega
    · omega
  intro j
  cases j with
  | none => exact hypSU_eq_bot_or_isLeviBlock_of_dim_le_three hU hε hdim h3
  | some b =>
      by_cases hb : b.1 - predCut I b.1 ≤ 1
      · exact Or.inl (uniBlockSub_some_eq_bot_of_le_one hU hb)
      · exact Or.inr (uniBlockSub_some_isLeviBlock_of_two_le hU (by omega))

private theorem block_nontrivial_card_le_two_of_t_one {K : Type} [Field K] [Finite K]
    {f t s ε : ℕ} (hU : UnitaryFieldData 2 f K) {I : Finset ℕ}
    (hI : IsTopCut I t) (ht : t = 1) :
    Nat.card {j : Option ↥I // uniBlockSub (s := s) (ε := ε) hU I j ≠ ⊥} ≤ 2 := by
  subst ht
  have hIeq : I = {1} := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      have h := hI.le x hx
      rw [Finset.mem_singleton]
      omega
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact hI.mem
  have hcard : Nat.card (Option ↥I) ≤ 2 := by
    rw [hIeq, Nat.card_eq_fintype_card]
    simp
  exact (Nat.card_le_card_of_injective
    (fun x : {j : Option ↥I // uniBlockSub (s := s) (ε := ε) hU I j ≠ ⊥} =>
      (x.1 : Option ↥I)) Subtype.val_injective).trans hcard

private theorem block_nontrivial_card_le_two_of_t_two {K : Type} [Field K] [Finite K]
    {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε) (hn_le : n ≤ 5) (ht : t = 2) :
    Nat.card {j : Option ↥I // uniBlockSub (s := s) (ε := ε) hU I j ≠ ⊥} ≤ 2 := by
  subst ht
  have hs0 : s = 0 := by omega
  subst hs0
  have hres : uniBlockSub (s := 0) (ε := ε) hU I none = ⊥ := by
    change hypSU hU 0 ε = ⊥
    have : Subsingleton (hypSU hU 0 ε) := subsingleton_hypSU_zero hU hε
    exact Subgroup.eq_bot_of_subsingleton _
  let g : {j : Option ↥I // uniBlockSub (s := 0) (ε := ε) hU I j ≠ ⊥} → ↥I := fun x =>
    match x.1 with
    | none => ⟨2, hI.mem⟩
    | some b => b
  have hg : Function.Injective g := by
    intro x y hxy
    obtain ⟨jx, hx⟩ := x
    obtain ⟨jy, hy⟩ := y
    cases jx with
    | none => exact absurd hres hx
    | some bx =>
        cases jy with
        | none => exact absurd hres hy
        | some by' =>
            have h : bx = by' := by simpa [g] using hxy
            exact Subtype.ext (congrArg some h)
  have hIcard : Nat.card ↥I ≤ 2 := by
    have hsub : I ⊆ Finset.Icc 1 2 := fun i hi => by
      have h := hI.le i hi
      exact Finset.mem_Icc.mpr ⟨h.1, h.2⟩
    have hinj : Function.Injective (fun b : ↥I =>
        (⟨b.1 - 1, by have := hsub b.2; rw [Finset.mem_Icc] at this; omega⟩ :
          Fin 2)) := by
      intro a b hab
      simp only [Fin.mk.injEq] at hab
      have ha := hsub a.2
      have hb := hsub b.2
      rw [Finset.mem_Icc] at ha hb
      exact Subtype.ext (by omega)
    exact (Nat.card_le_card_of_injective _ hinj).trans (by simp)
  exact (Nat.card_le_card_of_injective g hg).trans hIcard

private theorem block_nontrivial_card_le_two {K : Type} [Field K] [Finite K]
    {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε) (hn_le : n ≤ 5) :
    Nat.card {j : Option ↥I // uniBlockSub (s := s) (ε := ε) hU I j ≠ ⊥} ≤ 2 := by
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  rcases Nat.eq_or_lt_of_le ht1 with ht | ht2
  · exact block_nontrivial_card_le_two_of_t_one hU hI ht.symm
  · have ht : t = 2 := by omega
    exact block_nontrivial_card_le_two_of_t_two hU hε hI hn hn_le ht

private theorem block_censusAlt_of_f_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε)
    (hnf : n = 4 ∨ (n = 5 ∧ f = 2)) (hf : f = 1) :
    CensusAlt (G := fun j : Option ↥I => uniBlockGroup K s ε I j)
      (fun j => uniBlockSub (s := s) (ε := ε) hU I j) := by
  subst hf
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hdim : 2 * s + ε ≤ 2 := by omega
  have ht2 : t ≤ 2 := by omega
  right
  intro j hq m hm
  cases j with
  | none =>
      change CFSG.Open.IsQuasisimple ↥(uniBlockSub (s := s) (ε := ε) hU I none) at hq
      have hn4 : n = 4 := by
        rcases hnf with h | ⟨h, hf2⟩
        · exact h
        · omega
      rcases Nat.eq_zero_or_pos s with hs0 | hs
      · subst hs0
        have hbot : uniBlockSub (s := 0) (ε := ε) hU I none = ⊥ := by
          change hypSU hU 0 ε = ⊥
          have : Subsingleton (hypSU hU 0 ε) := subsingleton_hypSU_zero hU hε
          exact Subgroup.eq_bot_of_subsingleton _
        rw [hbot] at hq
        exact absurd hq (not_isQuasisimple_of_isSolvable
          (G := ↥(⊥ : Subgroup (GL (HypIndex 0 ε) K))) inferInstance)
      · have hs1 : s = 1 := by omega
        have hε0 : ε = 0 := by omega
        subst hs1
        subst hε0
        exact absurd hq (not_isQuasisimple_of_isSolvable
          (G := hypSU hU 1 0) (isSolvable_hypSU_one hU (Nat.zero_le 1)))
  | some b =>
      change CFSG.Open.IsQuasisimple
        ↥(uniBlockSub (s := s) (ε := ε) hU I (some b)) at hq
      by_cases hb : b.1 - predCut I b.1 ≤ 1
      · have hbot : uniBlockSub (s := s) (ε := ε) hU I (some b) = ⊥ :=
          uniBlockSub_some_eq_bot_of_le_one (s := s) (ε := ε) hU hb
        rw [hbot] at hq
        exact absurd hq (not_isQuasisimple_of_isSolvable
          (G := ↥(⊥ : Subgroup (GL (Fin (b.1 - predCut I b.1)) K))) inferInstance)
      · have hb2 : b.1 - predCut I b.1 = 2 := by
          have := (hI.le b.1 b.2).2
          omega
        exact not_isL2_uniBlockSub_some_of_f_eq_one hU (f := 1) rfl hb2 hm

private theorem block_bot_or_isQuasisimple_of_f_ne_one {K : Type} [Field K] [Finite K]
    [CharP K 2] {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε) (hn_le : n ≤ 5) (hf : f ≠ 1) :
    Nat.card {j : Option ↥I // uniBlockSub (s := s) (ε := ε) hU I j ≠ ⊥} ≤ 2 ∧
      ∀ j, uniBlockSub (s := s) (ε := ε) hU I j = ⊥ ∨
        CFSG.Open.IsQuasisimple ↥(uniBlockSub (s := s) (ε := ε) hU I j) := by
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hdim : 2 * s + ε ≤ 3 := by omega
  constructor
  · exact block_nontrivial_card_le_two hU hε hI hn hn_le
  · intro j
    cases j with
    | none =>
        by_cases hs0 : s = 0
        · subst hs0
          have hbot : uniBlockSub (s := 0) (ε := ε) hU I none = ⊥ := by
            change hypSU hU 0 ε = ⊥
            have : Subsingleton (hypSU hU 0 ε) := subsingleton_hypSU_zero hU hε
            exact Subgroup.eq_bot_of_subsingleton _
          exact Or.inl hbot
        · have hs1 : s = 1 := by omega
          rcases Nat.eq_zero_or_pos ε with hε0 | hεpos
          · subst hε0
            subst hs1
            exact Or.inr (hypSU_facts_two hU (by
              have hf1 : 1 ≤ f := hU.one_le
              omega)).1
          · have hε1 : ε = 1 := by omega
            subst hε1
            subst hs1
            have hne : (2 * 1 + 1, 2 ^ f) ≠ (3, 2) := by
              intro h
              have h2 : 2 ^ f = 2 := congrArg Prod.snd h
              have hf1 : 1 ≤ f := hU.one_le
              have hf2 : 2 ≤ f := by omega
              have h4 : 4 ≤ 2 ^ f := by
                calc 4 = 2 ^ 2 := by norm_num
                  _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
              omega
            exact Or.inr (hypSU_facts_of_three_le (p := 2) (f := f) (s := 1) (ε := 1) hU
              (by norm_num) hne).1
    | some b =>
        by_cases hb : b.1 - predCut I b.1 ≤ 1
        · exact Or.inl (uniBlockSub_some_eq_bot_of_le_one hU hb)
        · have hK : Nat.card K ≠ 2 := by
            have hf1 : 1 ≤ f := hU.one_le
            have hf2 : 2 ≤ f := by omega
            have h4 : 4 ≤ 2 ^ f := by
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
            rw [hU.card]
            have h4' : 4 ≤ 2 ^ (2 * f) := by
              calc 4 = 2 ^ (2 * 1) := by norm_num
                _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
            exact ne_of_gt (lt_of_lt_of_le (by norm_num : 2 < 4) h4')
          exact Or.inr (uniBlockSub_some_isQuasisimple_of_two_le hU hK (by omega))

private theorem block_censusAlt_of_f_ne_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε) (hn_le : n ≤ 5) (hf : f ≠ 1) :
    CensusAlt (G := fun j : Option ↥I => uniBlockGroup K s ε I j)
      (fun j => uniBlockSub (s := s) (ε := ε) hU I j) :=
  Or.inl (block_bot_or_isQuasisimple_of_f_ne_one hU hε hI hn hn_le hf)

private theorem block_censusAlt {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε)
    (hnf : n = 4 ∨ (n = 5 ∧ f = 2)) :
    CensusAlt (G := fun j : Option ↥I => uniBlockGroup K s ε I j)
      (fun j => uniBlockSub (s := s) (ε := ε) hU I j) := by
  have hn_le : n ≤ 5 := by rcases hnf with h | ⟨h, -⟩ <;> omega
  by_cases hf : f = 1
  · exact block_censusAlt_of_f_eq_one hU hε hI hn hnf hf
  · exact block_censusAlt_of_f_ne_one hU hε hI hn hn_le hf

private theorem three_dvd_quotient_center_hypSU_one_zero {K : Type} [Field K] [Finite K]
    {f : ℕ} (hU : UnitaryFieldData 2 f K) :
    3 ∣ Nat.card (hypSU hU 1 0 ⧸ Subgroup.center (hypSU hU 1 0)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := hU.charP
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := exists_hypSU_one_zero_mulEquiv hU
  let : Field F := hFfield
  have : Finite F := hFfin
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hFcard
  have h := three_dvd_card_quotient_center_range_toGL (K := F) (m := 2) (by norm_num)
  rw [← CFSG.AGLEmbedding.LeviBlock.card_centerQuotient_congr
    (e.trans (slEquivToGLRange (K := F) 2))] at h
  exact h

private theorem three_dvd_quotient_center_hypSU {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε)
    (hnf : n = 4 ∨ (n = 5 ∧ f = 2)) (hq : CFSG.Open.IsQuasisimple ↥(hypSU hU s ε)) :
    3 ∣ Nat.card (hypSU hU s ε ⧸ Subgroup.center (hypSU hU s ε)) := by
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hn_le : n ≤ 5 := by rcases hnf with h | ⟨h, -⟩ <;> omega
  have hdim : 2 * s + ε ≤ 3 := by omega
  have hs : s = 1 := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs
    · subst hs0
      have hbot : hypSU hU 0 ε = ⊥ := by
        have : Subsingleton (hypSU hU 0 ε) := subsingleton_hypSU_zero hU hε
        exact Subgroup.eq_bot_of_subsingleton _
      rw [hbot] at hq
      exact absurd hq (not_isQuasisimple_of_isSolvable
        (G := ↥(⊥ : Subgroup (GL (HypIndex 0 ε) K))) inferInstance)
    · omega
  subst hs
  rcases Nat.eq_zero_or_pos ε with hε0 | hεpos
  · subst hε0
    exact three_dvd_quotient_center_hypSU_one_zero hU
  · have hε1 : ε = 1 := by omega
    subst hε1
    have hf2 : f = 2 := by
      rcases hnf with h4 | ⟨-, hf⟩
      · omega
      · exact hf
    subst hf2
    have hfacts := hypSU_facts_of_three_le (p := 2) (f := 2) (s := 1) (ε := 1) hU
      (by norm_num) (by norm_num)
    rw [hfacts.2]
    change 3 ∣ ordTwistedA 2 4
    have h62400 : ordTwistedA 2 4 = 62400 := by decide
    rw [h62400]
    norm_num

private theorem three_dvd_quotient_center_toGL {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hq : CFSG.Open.IsQuasisimple ↥((Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range)) :
    3 ∣ Nat.card (↥((Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range) ⧸
      Subgroup.center ↥((Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range)) := by
  have hm : 2 ≤ m := by
    by_contra hm
    have hbot : (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range = ⊥ :=
      (range_toGL_eq_bot_iff (K := K) m).mpr (by omega)
    rw [hbot] at hq
    exact absurd hq (not_isQuasisimple_of_isSolvable
      (G := ↥(⊥ : Subgroup (GL (Fin m) K))) inferInstance)
  exact three_dvd_card_quotient_center_range_toGL (K := K) (m := m) hm

private theorem three_dvd_quotient_center_uniBlockSub {K : Type} [Field K] [Finite K]
    [CharP K 2] {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε)
    (hnf : n = 4 ∨ (n = 5 ∧ f = 2)) (j : Option ↥I)
    (hq : CFSG.Open.IsQuasisimple ↥(uniBlockSub (s := s) (ε := ε) hU I j)) :
    3 ∣ Nat.card (↥(uniBlockSub (s := s) (ε := ε) hU I j) ⧸
      Subgroup.center ↥(uniBlockSub (s := s) (ε := ε) hU I j)) := by
  cases j with
  | none =>
      change CFSG.Open.IsQuasisimple ↥(hypSU hU s ε) at hq
      change 3 ∣ Nat.card (hypSU hU s ε ⧸ Subgroup.center (hypSU hU s ε))
      exact three_dvd_quotient_center_hypSU hU hε hI hn hnf hq
  | some b =>
      change CFSG.Open.IsQuasisimple ↥((Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →*
          GL (Fin (b.1 - predCut I b.1)) K).range) at hq
      change 3 ∣ Nat.card (↥((Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →*
          GL (Fin (b.1 - predCut I b.1)) K).range) ⧸
        Subgroup.center ↥((Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →*
            GL (Fin (b.1 - predCut I b.1)) K).range))
      exact three_dvd_quotient_center_toGL hq

private theorem blockFacts_uniBlockSub {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (hn : n = 2 * (t + s) + ε)
    (hnf : n = 4 ∨ (n = 5 ∧ f = 2)) :
    BlockFacts (f = 1) False (fun j => uniBlockSub (s := s) (ε := ε) hU I j) := by
  have hn_le : n ≤ 5 := by rcases hnf with h | ⟨h, -⟩ <;> omega
  refine ⟨fun j hq => three_dvd_quotient_center_uniBlockSub hU hε hI hn hnf j hq, ?_,
    Or.inl (block_nontrivial_card_le_two hU hε hI hn hn_le)⟩
  intro j ⟨e⟩
  by_contra hf
  have hleft := block_bot_or_isQuasisimple_of_f_ne_one hU hε hI hn hn_le hf
  exact not_nonempty_mulEquiv_perm_three
    (H := uniBlockSub (s := s) (ε := ε) hU I j) (hleft.2 j) ⟨e⟩

private theorem not_two_dvd_relIndex_pi_uniLeviHom {K : Type} [Field K] [Finite K] [CharP K 2]
    {f t s ε : ℕ} (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) :
    ¬ 2 ∣ (Subgroup.pi Set.univ (uniBlockSub (s := s) (ε := ε) hU I)).relIndex
      (uniLeviHom hU hε hI).range := by
  let S' : ∀ j : Option ↥I, Subgroup (uniBlockGroup K s ε I j) :=
    uniBlockSub (s := s) (ε := ε) hU I
  let T : ∀ j : Option ↥I, Subgroup (uniBlockGroup K s ε I j) := fun j =>
    match j with
    | none => hypUnitary hU s ε
    | some _ => ⊤
  change ¬ 2 ∣ (Subgroup.pi Set.univ S').relIndex (uniLeviHom hU hε hI).range
  refine not_two_dvd_relIndex_pi_of_finite (S := S') (T := T)
    (Λ := (uniLeviHom hU hε hI).range) ?_ (pi_uniBlockSub_le_range hU hε hI) ?_ ?_
  · intro j
    cases j with
    | none => exact hypSU_le_hypUnitary hU
    | some b => exact le_top
  · rintro _ ⟨z, rfl⟩
    rw [Subgroup.mem_pi]
    intro j _
    cases j with
    | none => exact uniLeviHom_none_mem_hypUnitary hU hε hI z
    | some b => exact Subgroup.mem_top _
  · intro j
    cases j with
    | none => exact (odd_relIndex_hypSU_hypUnitary hU s ε).not_two_dvd_nat
    | some b =>
        change ¬ 2 ∣ ((Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →*
            GL (Fin (b.1 - predCut I b.1)) K).range).relIndex ⊤
        rw [Subgroup.relIndex_top_right]
        exact not_two_dvd_index_range_toGL _

private theorem exists_beta_data {X : Type} [Group X] {f t s ε : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {I : Finset ℕ} (hI : IsTopCut I t) {J : Subgroup X}
    (ρ : hypSU hU (t + s) ε →* ↥(⊤ : Subgroup X)) (g : hypSU hU (t + s) ε)
    (hflag : ∀ y, y ∈ (J.subgroupOf ⊤).comap ρ ↔
      ∀ i ∈ (↑I : Set ℕ), y • (g • hypFlag hU (t + s) ε i) =
        g • hypFlag hU (t + s) ε i) :
    ∃ β : ↥((J.subgroupOf ⊤).comap ρ) →* ∀ j : Option ↥I, uniBlockGroup K s ε I j,
      IsPGroup 2 β.ker ∧
      Subgroup.pi Set.univ (uniBlockSub (s := s) (ε := ε) hU I) ≤ β.range ∧
      β.range ≤ Subgroup.normalizer (Subgroup.pi Set.univ
        (uniBlockSub (s := s) (ε := ε) hU I) : Set (∀ j, uniBlockGroup K s ε I j)) ∧
      ¬ 2 ∣ (Subgroup.pi Set.univ
        (uniBlockSub (s := s) (ε := ε) hU I)).relIndex β.range := by
  let eJ := stabMulEquiv g hflag
  let β : ↥((J.subgroupOf ⊤).comap ρ) →* ∀ j : Option ↥I, uniBlockGroup K s ε I j :=
    (uniLeviHom hU hε hI).comp eJ.toMonoidHom
  have hrange : β.range = (uniLeviHom hU hε hI).range := by
    rw [show β = (uniLeviHom hU hε hI).comp eJ.toMonoidHom from rfl,
      MonoidHom.range_comp, MonoidHom.range_eq_map (eJ.toMonoidHom),
      Subgroup.map_top_of_surjective _ eJ.surjective, ← MonoidHom.range_eq_map]
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · exact (isPGroup_ker_uniLeviHom hU hε hI).comap_of_injective eJ.toMonoidHom eJ.injective
  · rw [hrange]
    exact pi_uniBlockSub_le_range hU hε hI
  · rw [hrange]
    exact le_normalizer_of_commutator_le (pi_uniBlockSub_le_range hU hε hI)
      (commutator_range_le_pi hU hε hI)
  · rw [hrange]
    exact not_two_dvd_relIndex_pi_uniLeviHom hU hε hI

private theorem ker_center_odd {X : Type} [Group X] {f t s ε : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hU : UnitaryFieldData 2 f K)
    {ρ : hypSU hU (t + s) ε →* ↥(⊤ : Subgroup X)} (hdim : 1 ≤ 2 * (t + s) + ε)
    (hker : ρ.ker ≤ hypScalars hU (t + s) ε) :
    ρ.ker ≤ Subgroup.center (hypSU hU (t + s) ε) ∧ Odd (Nat.card ↥ρ.ker) := by
  refine ⟨hker.trans (normOneScalars_le_center hU _ _), ?_⟩
  have hdvd : Nat.card ↥ρ.ker ∣ Nat.card ↥(hypScalars hU (t + s) ε) :=
    Subgroup.card_dvd_of_le hker
  rw [card_hypScalars hU hdim] at hdvd
  have hodd : Odd (2 ^ f + 1) :=
    ((Nat.even_pow' (by have := hU.one_le; omega)).2 even_two).add_one
  exact Odd.of_dvd_nat hodd (hdvd.trans (Nat.gcd_dvd_right _ _))

private theorem hasLeviDataX_of_flag_data {X : Type} [Group X] [Finite X]
    {f n t s ε : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hU : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t) {J : Subgroup X}
    (hJL : J ≤ ⊤) (ρ : hypSU hU (t + s) ε →* ↥(⊤ : Subgroup X))
    (hρ : Function.Surjective ρ) (g : hypSU hU (t + s) ε)
    (hZfib : ∀ y, ρ y ∈ Subgroup.center (↥(⊤ : Subgroup X)) ↔ y ∈ hypScalars hU (t + s) ε)
    (hflag : ∀ y, y ∈ (J.subgroupOf ⊤).comap ρ ↔
      ∀ i ∈ (↑I : Set ℕ), y • (g • hypFlag hU (t + s) ε i) =
        g • hypFlag hU (t + s) ε i)
    (hn : n = 2 * (t + s) + ε) (hnf : n = 4 ∨ (n = 5 ∧ f = 2)) :
    HasLeviDataX (f = 1) False ↥J := by
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hdim : 1 ≤ 2 * (t + s) + ε := by omega
  have hker : ρ.ker ≤ hypScalars hU (t + s) ε := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    exact (hZfib y).mp (hy ▸ Subgroup.one_mem _)
  obtain ⟨hc, ho⟩ := ker_center_odd hU hdim hker
  obtain ⟨β, hβ, hle, hnrm, hi⟩ := exists_beta_data hU hε hI ρ g hflag
  have hS' : ∀ j, uniBlockSub (s := s) (ε := ε) hU I j = ⊥ ∨
      IsLeviBlock ↥(uniBlockSub (s := s) (ε := ε) hU I j) :=
    block_bot_or_isLeviBlock hU hε hI hn hnf
  have halt : CensusAlt (G := fun j : Option ↥I => uniBlockGroup K s ε I j)
      (fun j => uniBlockSub (s := s) (ε := ε) hU I j) :=
    block_censusAlt hU hε hI hn hnf
  exact hasLeviDataX_of_cover hJL ρ hρ hc ho β hβ hle hnrm hi hS' halt
    (blockFacts_uniBlockSub hU hε hI hn hnf)

private theorem exists_tauCeti_equiv_of_stated {S K : Type} [Group S] [Field K] [Finite K]
    {n f : ℕ} (hcard : Nat.card K = (2 ^ f) ^ 2) (hn3 : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    (eS : S ≃* StatedProj (StatedSU n (2 ^ f) K)) :
    ∃ (q' : TauCeti.PrimePower)
      (hv : (TauCeti.LieTypeIndex.twistedA (n - 1) q').Valid),
      q'.p = 2 ∧ q'.card = 2 ^ f ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA (n - 1) q', hv⟩).Group) := by
  have : Fintype K := Fintype.ofFinite K
  have hcard' : Nat.card K = 2 ^ (2 * f) := by
    rw [hcard, ← pow_mul]
    congr 1
    omega
  have hK2 : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * f) hcard'
  obtain ⟨q', hv, hq'p, hq'card, ⟨eC⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (K := K) (m := n) (q := 2 ^ f) (by rw [Fintype.card_eq_nat_card]; exact hcard) hn3 hnq
  have hSU := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := f) (n := n) (F := K) hcard hn3 hnq
  let eSU : StatedProj (StatedSU n (2 ^ f) K) ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedA (n - 1) q', hv⟩).Group :=
    (QuotientGroup.quotientMulEquivOfEq hSU.2).symm.trans eC
  exact ⟨q', hv, hq'p.trans (ringChar.eq K 2), hq'card, ⟨eS.trans eSU⟩⟩

theorem hasLeviDataX_of_psu
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    {n f : ℕ} (h : CFSG.Blueprint.LieModel S .PSU n 2 f) (hnf : n = 4 ∨ (n = 5 ∧ f = 2))
    {J : Subgroup S} (hJ : S19.IsNontrivialParabolic S J) : HasLeviDataX (f = 1) False ↥J := by
  have hSC := h.statedClassicalModel (by decide : .PSU ∈ CFSG.Blueprint.classicalTags)
  obtain ⟨⟨-, hf1, hn3, hnq⟩, K, hKfield, hKfin, hcard, ⟨eS⟩⟩ := hSC
  let : Field K := hKfield
  let : Finite K := hKfin
  obtain ⟨q', hv, hq'p, hq'card, ⟨eSto⟩⟩ :=
    exists_tauCeti_equiv_of_stated hcard hn3 hnq eS
  have hcenterS : Subgroup.center S = ⊥ := center_eq_bot_of_isNontrivialParabolic hS hJ
  have hcenterTop : Subgroup.center (⊤ : Subgroup S) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hxS : (x : S) ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      exact congrArg Subtype.val (hx (Subgroup.topEquiv.symm y))
    rw [hcenterS, Subgroup.mem_bot] at hxS
    exact Subtype.ext hxS
  let eTop : (↥(⊤ : Subgroup S)) ⧸ Subgroup.center ↥(⊤ : Subgroup S) ≃* S :=
    ((QuotientGroup.quotientMulEquivOfEq hcenterTop).trans
      (QuotientGroup.quotientBot (G := ↥(⊤ : Subgroup S)))).trans Subgroup.topEquiv
  let e : (↥(⊤ : Subgroup S)) ⧸ Subgroup.center ↥(⊤ : Subgroup S) ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedA (n - 1) q', hv⟩).Group := eTop.trans eSto
  have : Group.IsPerfect S := Group.IsPerfect.mk (commutator_eq_top_of_isNontrivialParabolic hS hJ)
  have hcommTop : commutator ↥(⊤ : Subgroup S) = ⊤ := Group.IsPerfect.commutator_eq_top
  have : IsSimpleGroup ((↥(⊤ : Subgroup S)) ⧸ Subgroup.center ↥(⊤ : Subgroup S)) :=
    (MulEquiv.isSimpleGroup_congr eTop).mpr hS
  have hcomp : IsComponentOf (⊤ : Subgroup S) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hcommTop, inferInstance⟩
  have htype : CFSG.AGLEmbedding.IsClassicalTwoOrG2
      ((↥(⊤ : Subgroup S)) ⧸ Subgroup.center ↥(⊤ : Subgroup S)) :=
    Or.inl ⟨⟨.twistedA (n - 1) q', hv⟩, hq'p, ⟨e⟩⟩
  have hodd : Odd (Nat.card (Subgroup.center ↥(⊤ : Subgroup S))) := by
    rw [hcenterTop, Subgroup.card_bot]
    exact odd_one
  have hCP : CFSG.AGLEmbedding.CompParab (⊤ : Subgroup S) J :=
    ⟨hcomp, htype, hodd, isParabolicTwo_top_of_isNontrivialParabolic hJ, hJ.2.1,
      fun T hT => ne_inf_normalizer_of_isNontrivialParabolic hJ T hT⟩
  have hd : CFSG.AGLEmbedding.IdxTwistedA (.twistedA (n - 1) q') := hq'p
  obtain ⟨K', _, f', t, s, ε, hU, ρ, I, g, hε, hI, hq, hρ, hZfib, hflag⟩ :=
    CFSG.AGLEmbedding.exists_uniFlag_dim_of_compParab hCP ⟨.twistedA (n - 1) q', hv⟩ hd e
  have : Finite K' := hU.finite
  have : CharP K' 2 := hU.charP
  obtain ⟨hqcard, hndim⟩ := hq (n - 1) q' rfl
  have hn_eq : n = 2 * (t + s) + ε := by
    rw [← hndim, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hinner : f' = f := by
    refine Nat.pow_right_injective (by norm_num : 2 ≤ 2) ?_
    change 2 ^ f' = 2 ^ f
    rw [← hqcard, hq'card]
  subst hinner
  exact hasLeviDataX_of_flag_data hU hε hI (le_top) ρ hρ g hZfib hflag hn_eq hnf

theorem hasLeviData_of_psu
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    {n f : ℕ} (h : CFSG.Blueprint.LieModel S .PSU n 2 f) (hnf : n = 4 ∨ (n = 5 ∧ f = 2))
    {J : Subgroup S} (hJ : S19.IsNontrivialParabolic S J) : HasLeviData ↥J :=
  (hasLeviDataX_of_psu hS h hnf hJ).hasLeviData

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
