module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Parabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Blocks
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.BlocksSL
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.OrthMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
open CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private noncomputable def blocksZero (K : Type) [Field K] {s : ℕ} (d : Fin (s + 1) → ℕ)
    (b c : K) : ∀ j : Fin s ⊕ Unit, Subgroup (orthLeviGroup K 3 d j)
  | .inl l => orthLeviBlock K 3 d b c (.inl l)
  | .inr _ => ⊥

private noncomputable def blocksT (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {s : ℕ}
    (d : Fin (s + 1) → ℕ) : ∀ j : Fin s ⊕ Unit, Subgroup (orthLeviGroup K 3 d j)
  | .inl _ => ⊤
  | .inr _ => omegaGroup (quadTail (3 - d (Fin.last s)) (minusTailForm K b c))
      (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))

private theorem orthLeviHom_range_le_blocksT {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (orthLeviHom b c hd).range ≤
      Subgroup.pi Set.univ (blocksT (K := K) (b := b) (c := c) hirr d) := by
  intro y hy
  obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [Subgroup.mem_pi]
  intro j _
  rcases j with l | u
  · exact Subgroup.mem_top _
  · obtain rfl : u = () := rfl
    rw [orthLeviHom_inr]
    exact orthResHom_mem_omegaGroup hd (by norm_num) hirr z

private theorem blocksZero_le_blocksT {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ j, blocksZero K d b c j ≤ blocksT (K := K) (b := b) (c := c) hirr d j
  | .inl _ => le_top
  | .inr _ => bot_le

private theorem orthLeviBlock_le_blocksT {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ j, orthLeviBlock K 3 d b c j ≤ blocksT (K := K) (b := b) (c := c) hirr d j
  | .inl _ => le_top
  | .inr _ => CFSG.LargeExtraspecial.DW.commutator_le_omegaGroup
      (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))

omit [Finite K] [CharP K 2] in
private theorem pi_blocksZero_le_pi_orthLeviBlock {s : ℕ} {d : Fin (s + 1) → ℕ} :
    Subgroup.pi Set.univ (blocksZero K d b c) ≤
      Subgroup.pi Set.univ (orthLeviBlock K 3 d b c) := by
  intro x hx
  rw [Subgroup.mem_pi] at hx ⊢
  intro j _
  rcases j with l | u
  · exact hx (.inl l) trivial
  · have h1 : x (.inr u) = 1 := Subgroup.mem_bot.mp (hx (.inr u) trivial)
    rw [h1]
    exact Subgroup.one_mem _

private theorem pi_blocksZero_le_range {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.pi Set.univ (blocksZero K d b c) ≤ (orthLeviHom b c hd).range :=
  (pi_blocksZero_le_pi_orthLeviBlock (K := K) (b := b) (c := c)).trans
    (pi_orthLeviBlock_le_range hd (by norm_num)
      (commutator_orthogonalGroup_quadTail_minus (by norm_num) hirr))

private theorem not_two_dvd_relIndex_pi_blocksZero {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) (hm0 : 3 - d (Fin.last s) = 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ 2 ∣ (Subgroup.pi Set.univ (blocksZero K d b c)).relIndex (orthLeviHom b c hd).range := by
  refine not_two_dvd_relIndex_pi_of_finite
    (S := blocksZero K d b c) (T := blocksT (K := K) (b := b) (c := c) hirr d)
    (blocksZero_le_blocksT (K := K) (b := b) (c := c) hirr) ?_ ?_ ?_
  · exact pi_blocksZero_le_range hd hirr
  · exact orthLeviHom_range_le_blocksT hd hirr
  · intro j
    rcases j with l | u
    · change ¬ 2 ∣ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* GL _ K).range.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact not_two_dvd_index_range_toGL _
    · obtain rfl : u = () := rfl
      change ¬ 2 ∣ (⊥ : Subgroup (orthLeviGroup K 3 d (.inr ()))).relIndex
        (omegaGroup (quadTail (3 - d (Fin.last s)) (minusTailForm K b c))
          (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)))
      rw [Subgroup.relIndex_bot_left]
      exact (odd_card_omegaGroup_tail_of_eq_zero (m := 3 - d (Fin.last s)) hm0
        hirr).not_two_dvd_nat

private theorem not_two_dvd_relIndex_pi_orthLeviBlock {f s : ℕ} {d : Fin (s + 1) → ℕ}
    (hK : Nat.card K = 2 ^ f) (hd : OrthCuts 3 d) (hm1 : 1 ≤ 3 - d (Fin.last s))
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ 2 ∣ (Subgroup.pi Set.univ (orthLeviBlock K 3 d b c)).relIndex
      (orthLeviHom b c hd).range := by
  refine not_two_dvd_relIndex_pi_of_finite
    (S := orthLeviBlock K 3 d b c) (T := blocksT (K := K) (b := b) (c := c) hirr d)
    (orthLeviBlock_le_blocksT (K := K) (b := b) (c := c) hirr) ?_ ?_ ?_
  · exact pi_orthLeviBlock_le_range hd (by norm_num)
      (commutator_orthogonalGroup_quadTail_minus (by norm_num) hirr)
  · exact orthLeviHom_range_le_blocksT hd hirr
  · intro j
    rcases j with l | u
    · change ¬ 2 ∣ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* GL _ K).range.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact not_two_dvd_index_range_toGL _
    · obtain rfl : u = () := rfl
      change ¬ 2 ∣ (orthResDer K b c (3 - d (Fin.last s))).relIndex
        (omegaGroup (quadTail (3 - d (Fin.last s)) (minusTailForm K b c))
          (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)))
      rw [relIndex_orthResDer_omegaGroup (m := 3 - d (Fin.last s)) hK hm1 hirr]
      norm_num

omit [Finite K] [CharP K 2] in
private theorem orthLeviHom_range_le_normalizer_blocksZero {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) :
    (orthLeviHom b c hd).range ≤
      Subgroup.normalizer (Subgroup.pi Set.univ (blocksZero K d b c) :
        Set (∀ j, orthLeviGroup K 3 d j)) := by
  have hnorm_inl : ∀ l : Fin s,
      Subgroup.normalizer (blocksZero K d b c (.inl l) :
        Set (orthLeviGroup K 3 d (.inl l))) = ⊤ := by
    intro l
    rw [Subgroup.normalizer_eq_top_iff]
    change (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* GL _ K).range.Normal
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact MonoidHom.normal_ker _
  have hnorm_inr : Subgroup.normalizer (blocksZero K d b c (.inr ()) :
      Set (orthLeviGroup K 3 d (.inr ()))) = ⊤ := by
    rw [Subgroup.normalizer_eq_top_iff]
    change (⊥ : Subgroup (orthLeviGroup K 3 d (.inr ()))).Normal
    infer_instance
  refine le_normalizer_pi_of_forall fun g _ j => ?_
  rcases j with l | u
  · rw [hnorm_inl l]
    exact Subgroup.mem_top _
  · obtain rfl : u = () := rfl
    rw [hnorm_inr]
    exact Subgroup.mem_top _

private theorem orthLeviHom_range_le_normalizer_orthLeviBlock {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (orthLeviHom b c hd).range ≤
      Subgroup.normalizer (Subgroup.pi Set.univ (orthLeviBlock K 3 d b c) :
        Set (∀ j, orthLeviGroup K 3 d j)) :=
  le_normalizer_of_commutator_le
    (pi_orthLeviBlock_le_range hd (by norm_num)
      (commutator_orthogonalGroup_quadTail_minus (by norm_num) hirr))
    (commutator_range_orthLeviHom_le hd)

private theorem isLeviBlock_orthResDer {f m : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 2) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsLeviBlock ↥(orthResDer K b c m) := by
  obtain ⟨hsimple, hna, hcard⟩ := orthResDer_facts hK hm1 hirr
  have : IsSimpleGroup ↥(orthResDer K b c m) := hsimple
  obtain ⟨hq, hcenter⟩ := orthMinus_isQuasisimple_of_simple hna
  refine Or.inr (Or.inr ⟨hq, ?_, ?_⟩)
  · rw [hcenter, Subgroup.card_bot]
    exact odd_one
  · rw [hcard]
    have h2q : 2 ∣ 2 ^ f := by
      have hf0 : f ≠ 0 := by omega
      exact dvd_pow_self 2 hf0
    rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl
    · rw [orthMinus_ordTwistedD_two hf]
      exact (show 2 ∣ (2 ^ f) ^ 2 from h2q.trans (dvd_pow_self _ (by norm_num))).mul_right _
    · rw [orthMinus_ordTwistedD_three hf]
      exact ((show 2 ∣ (2 ^ f) ^ 6 from
        h2q.trans (dvd_pow_self _ (by norm_num))).mul_right _).mul_right _ |>.mul_right _

private theorem blocksZero_isLeviBlock {s : ℕ} {d : Fin (s + 1) → ℕ} :
    ∀ j, blocksZero K d b c j = ⊥ ∨ IsLeviBlock ↥(blocksZero K d b c j) := by
  intro j
  rcases j with l | u
  · rcases range_toGL_eq_bot_or_isLeviBlock (K := K) (d l.succ - d l.castSucc) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact Or.inl rfl

private theorem blocksPos_isLeviBlock {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d) (hdpos : 0 < d (Fin.last s))
    (hm1 : 1 ≤ 3 - d (Fin.last s)) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ j, orthLeviBlock K 3 d b c j = ⊥ ∨ IsLeviBlock ↥(orthLeviBlock K 3 d b c j) := by
  intro j
  rcases j with l | u
  · rcases range_toGL_eq_bot_or_isLeviBlock (K := K) (d l.succ - d l.castSucc) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · obtain rfl : u = () := rfl
    have hm2 : 3 - d (Fin.last s) ≤ 2 := by
      have hlast : d (Fin.last s) ≤ 3 := hd.last
      omega
    refine Or.inr ?_
    change IsLeviBlock ↥(orthResDer K b c (3 - d (Fin.last s)))
    exact isLeviBlock_orthResDer hK hf hm1 hm2 hirr

private theorem not_two_large_blocks {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d)
    {l₁ l₂ : Fin s} (hlt : l₁ < l₂)
    (h₁ : 2 ≤ d l₁.succ - d l₁.castSucc) (h₂ : 2 ≤ d l₂.succ - d l₂.castSucc) : False := by
  have hle : l₁.succ ≤ l₂.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
  have hmono : d l₁.succ ≤ d l₂.castSucc := hd.mono.monotone hle
  have h1 : d l₁.castSucc + 2 ≤ d l₁.succ := by
    have hlt1 : l₁.castSucc < l₁.succ := Fin.castSucc_lt_succ
    have := hd.mono hlt1
    omega
  have h2 : d l₂.castSucc + 2 ≤ d l₂.succ := by
    have hlt2 : l₂.castSucc < l₂.succ := Fin.castSucc_lt_succ
    have := hd.mono hlt2
    omega
  have hlast : d l₂.succ ≤ d (Fin.last s) := hd.mono.monotone (Fin.le_last _)
  have hlast3 : d (Fin.last s) ≤ 3 := hd.last
  omega

private theorem card_subtype_ne_bot_le_two {s : ℕ} {G : Fin s ⊕ Unit → Type} [∀ j, Group (G j)]
    [∀ j, Finite (G j)] (S : ∀ j, Subgroup (G j))
    (hlin : ∀ l₁ l₂ : Fin s, l₁ ≠ l₂ → S (.inl l₁) ≠ ⊥ → S (.inl l₂) ≠ ⊥ → False) :
    Nat.card {j // S j ≠ ⊥} ≤ 2 := by
  classical
  let : Fintype {j // S j ≠ ⊥} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  by_contra h
  rw [not_le] at h
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h
  have hpair : ∃ l₁ l₂ : Fin s, l₁ ≠ l₂ ∧ S (.inl l₁) ≠ ⊥ ∧ S (.inl l₂) ≠ ⊥ := by
    rcases ha : a.1 with la | ua
    · rcases hb : b.1 with lb | ub
      · refine ⟨la, lb, fun hh => hab (Subtype.ext (by rw [ha, hb, hh])), ?_, ?_⟩
        · rw [← ha]
          exact a.2
        · rw [← hb]
          exact b.2
      · rcases hc : c.1 with lc | uc
        · refine ⟨la, lc, fun hh => hac (Subtype.ext (by rw [ha, hc, hh])), ?_, ?_⟩
          · rw [← ha]
            exact a.2
          · rw [← hc]
            exact c.2
        · exfalso
          have hui : ub = uc := Subsingleton.elim _ _
          exact hbc (Subtype.ext (by rw [hb, hc, hui]))
    · rcases hb : b.1 with lb | ub
      · rcases hc : c.1 with lc | uc
        · refine ⟨lb, lc, fun hh => hbc (Subtype.ext (by rw [hb, hc, hh])), ?_, ?_⟩
          · rw [← hb]
            exact b.2
          · rw [← hc]
            exact c.2
        · exfalso
          have hui : ua = uc := Subsingleton.elim _ _
          exact hac (Subtype.ext (by rw [ha, hc, hui]))
      · exfalso
        have hui : ua = ub := Subsingleton.elim _ _
        exact hab (Subtype.ext (by rw [ha, hb, hui]))
  obtain ⟨l₁, l₂, hlne, h₁, h₂⟩ := hpair
  rcases lt_or_gt_of_ne hlne with hlt | hgt
  · exact hlin l₁ l₂ hlne h₁ h₂
  · exact hlin l₂ l₁ (Ne.symm hlne) h₂ h₁

omit [CharP K 2] in
private theorem not_inl_ne_bot_pair {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d)
    {l₁ l₂ : Fin s} (hne : l₁ ≠ l₂)
    (h₁ : orthLeviBlock K 3 d b c (.inl l₁) ≠ ⊥)
    (h₂ : orthLeviBlock K 3 d b c (.inl l₂) ≠ ⊥) : False := by
  have hd₁ : 2 ≤ d l₁.succ - d l₁.castSucc := by
    by_contra hle
    exact h₁ ((range_toGL_eq_bot_iff (d l₁.succ - d l₁.castSucc)).mpr (by omega))
  have hd₂ : 2 ≤ d l₂.succ - d l₂.castSucc := by
    by_contra hle
    exact h₂ ((range_toGL_eq_bot_iff (d l₂.succ - d l₂.castSucc)).mpr (by omega))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact not_two_large_blocks hd hlt hd₁ hd₂
  · exact not_two_large_blocks hd hgt hd₂ hd₁

omit [CharP K 2] in
private theorem card_blocksZero_ne_bot_le_two {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) :
    Nat.card {j : Fin s ⊕ Unit // blocksZero K d b c j ≠ ⊥} ≤ 2 :=
  card_subtype_ne_bot_le_two (blocksZero K d b c) fun _ _ hne h₁ h₂ =>
    not_inl_ne_bot_pair (K := K) (b := b) (c := c) hd hne h₁ h₂

omit [CharP K 2] in
private theorem card_orthLeviBlock_ne_bot_le_two {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) :
    Nat.card {j : Fin s ⊕ Unit // orthLeviBlock K 3 d b c j ≠ ⊥} ≤ 2 :=
  card_subtype_ne_bot_le_two (orthLeviBlock K 3 d b c) fun _ _ hne h₁ h₂ =>
    not_inl_ne_bot_pair (K := K) (b := b) (c := c) hd hne h₁ h₂

private theorem three_dvd_pow_four_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 4 - 1 := by
  have h : (2 ^ f) ^ 4 = 16 ^ f := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have h15 : 15 ∣ 16 ^ f - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (x := 16) (y := 1) (n := f)
  rw [h]
  exact dvd_trans (by norm_num : 3 ∣ 15) h15

private theorem three_dvd_ordTwistedD_two {f : ℕ} (hf : 1 ≤ f) :
    3 ∣ CFSG.Open.ordTwistedD 2 (2 ^ f) := by
  rw [orthMinus_ordTwistedD_two hf]
  exact dvd_mul_of_dvd_right (three_dvd_pow_four_sub_one f) _

private theorem three_dvd_ordTwistedD_three {f : ℕ} (hf : 1 ≤ f) :
    3 ∣ CFSG.Open.ordTwistedD 3 (2 ^ f) := by
  rw [orthMinus_ordTwistedD_three hf]
  exact dvd_mul_of_dvd_right (three_dvd_pow_four_sub_one f) _

private theorem three_dvd_card_orthResDer_quotient_center {f m : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 1 ≤ f) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hq : CFSG.Open.IsQuasisimple ↥(orthResDer K b c m)) (hm : m = 1 ∨ m = 2) :
    3 ∣ Nat.card (↥(orthResDer K b c m) ⧸ center ↥(orthResDer K b c m)) := by
  obtain ⟨-, -, hquot⟩ := card_orthResDer_quotient_center hK hirr hq
  rw [hquot]
  rcases hm with rfl | rfl
  · exact three_dvd_ordTwistedD_two hf
  · exact three_dvd_ordTwistedD_three hf

private theorem not_isL2_of_card_25920 {Y : Type} [Group Y] [Finite Y]
    (hY : Nat.card Y = 25920) {n : ℕ} (hn : 3 ≤ n) : ¬ IsL2 Y n := by
  intro hL
  have hcard := S17.card_of_isL2 hL
  rw [hY] at hcard
  have hle6 : n ≤ 6 := by
    by_contra h
    rw [not_le] at h
    have hn7 : 7 ≤ n := by omega
    have h1 : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn7
    have h2 : 2 ^ (2 * 7) - 1 ≤ 2 ^ (2 * n) - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1
    have hprod : 2 ^ 7 * (2 ^ (2 * 7) - 1) ≤ 2 ^ n * (2 ^ (2 * n) - 1) :=
      Nat.mul_le_mul h1 h2
    rw [← hcard] at hprod
    norm_num at hprod
  interval_cases n <;> norm_num at hcard

private theorem blocksZero_bot_or_isQuasisimple {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {s : ℕ} {d : Fin (s + 1) → ℕ} :
    ∀ j, blocksZero K d b c j = ⊥ ∨ CFSG.Open.IsQuasisimple ↥(blocksZero K d b c j) := by
  have hKne : Nat.card K ≠ 2 := by
    rw [hK]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    exact Nat.ne_of_gt (by omega)
  intro j
  rcases j with l | u
  · exact range_toGL_eq_bot_or_isQuasisimple hKne (d l.succ - d l.castSucc)
  · exact Or.inl rfl

private theorem censusAlt_blocksZero_two_le {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d) :
    CensusAlt (blocksZero K d b c) :=
  Or.inl ⟨card_blocksZero_ne_bot_le_two hd, blocksZero_bot_or_isQuasisimple hK hf⟩

omit [CharP K 2] in
private theorem censusAlt_blocksZero_eq_one (hK : Nat.card K = 2)
    {s : ℕ} {d : Fin (s + 1) → ℕ} : CensusAlt (blocksZero K d b c) := by
  right
  intro j hq n hn
  rcases j with l | u
  · exact not_isL2_range_toGL hK (d l.succ - d l.castSucc) hq hn
  · obtain rfl : u = () := rfl
    exact absurd hq (not_isQuasisimple_of_isSolvable (G :=
      ↥(⊥ : Subgroup (orthLeviGroup K 3 d (.inr ())))) inferInstance)

private theorem orthLeviBlock_bot_or_isQuasisimple {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {s : ℕ} {d : Fin (s + 1) → ℕ} (hm1 : 1 ≤ 3 - d (Fin.last s))
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ j, orthLeviBlock K 3 d b c j = ⊥ ∨
      CFSG.Open.IsQuasisimple ↥(orthLeviBlock K 3 d b c j) := by
  have hKne : Nat.card K ≠ 2 := by
    rw [hK]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    exact Nat.ne_of_gt (by omega)
  intro j
  rcases j with l | u
  · exact range_toGL_eq_bot_or_isQuasisimple hKne (d l.succ - d l.castSucc)
  · obtain rfl : u = () := rfl
    obtain ⟨hsimple, hna, -⟩ := orthResDer_facts hK hm1 hirr
    refine Or.inr ?_
    change CFSG.Open.IsQuasisimple ↥(orthResDer K b c (3 - d (Fin.last s)))
    have : IsSimpleGroup ↥(orthResDer K b c (3 - d (Fin.last s))) := hsimple
    exact (orthMinus_isQuasisimple_of_simple hna).1

private theorem censusAlt_orthLeviBlock_two_le {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d)
    (hm1 : 1 ≤ 3 - d (Fin.last s))
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CensusAlt (orthLeviBlock K 3 d b c) :=
  Or.inl ⟨card_orthLeviBlock_ne_bot_le_two hd,
    orthLeviBlock_bot_or_isQuasisimple hK hf hm1 hirr⟩

private theorem censusAlt_orthLeviBlock_eq_one {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : f = 1)
    {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d) (hdpos : 0 < d (Fin.last s))
    (hm1 : 1 ≤ 3 - d (Fin.last s)) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CensusAlt (orthLeviBlock K 3 d b c) := by
  change CensusAlt (fun j : Fin s ⊕ Unit =>
    match j with
    | .inl l => orthLeviBlock K 3 d b c (.inl l)
    | .inr _ => orthResDer K b c (3 - d (Fin.last s)))
  right
  intro j hq n hn
  rcases j with l | u
  · have hK2 : Nat.card K = 2 := by rw [hK, hf]; norm_num
    exact not_isL2_range_toGL hK2 (d l.succ - d l.castSucc) hq hn
  · obtain rfl : u = () := rfl
    change CFSG.Open.IsQuasisimple ↥(orthResDer K b c (3 - d (Fin.last s))) at hq
    have hq' : CFSG.Open.IsQuasisimple ↥(orthResDer K b c (3 - d (Fin.last s))) := hq
    have hm2 : 3 - d (Fin.last s) ≤ 2 := by
      have hlast : d (Fin.last s) ≤ 3 := hd.last
      omega
    have hcases : (3 - d (Fin.last s) = 1) ∨ (3 - d (Fin.last s) = 2) := by omega
    have key : ¬ IsL2 (↥(orthResDer K b c (3 - d (Fin.last s))) ⧸
        Subgroup.center ↥(orthResDer K b c (3 - d (Fin.last s)))) n := by
      rcases hcases with hm | hm
      · rw [hm] at hq' ⊢
        obtain ⟨-, -, hquot⟩ := card_orthResDer_quotient_center (m := 1) hK hirr hq'
        rw [hf, orthMinus_ordTwistedD_two (by norm_num)] at hquot
        norm_num at hquot
        exact not_isL2_of_card_lt (by rw [hquot]; norm_num) hn
      · rw [hm] at hq' ⊢
        obtain ⟨-, -, hquot⟩ := card_orthResDer_quotient_center (m := 2) hK hirr hq'
        rw [hf, orthMinus_ordTwistedD_three (by norm_num)] at hquot
        norm_num at hquot
        exact not_isL2_of_card_25920 hquot hn
    exact key

private theorem blockFacts_blocksZero {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d) :
    BlockFacts (f = 1) False (blocksZero K d b c) := by
  refine ⟨?_, ?_, Or.inl (card_blocksZero_ne_bot_le_two hd)⟩
  · intro j hq
    rcases j with l | u
    · change 3 ∣ Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
            GL (Fin (d l.succ - d l.castSucc)) K).range ⧸
        Subgroup.center ↥(Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
            GL (Fin (d l.succ - d l.castSucc)) K).range)
      exact three_dvd_card_quotient_center_range_toGL (K := K)
        (two_le_of_isQuasisimple_specialLinear
          (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) _).symm hq))
    · obtain rfl : u = () := rfl
      exact absurd hq (not_isQuasisimple_of_isSolvable (G :=
        ↥(⊥ : Subgroup (orthLeviGroup K 3 d (.inr ())))) inferInstance)
  · intro j hj
    by_cases hf1 : f = 1
    · exact hf1
    · exact absurd hj (not_nonempty_mulEquiv_perm_three
        (blocksZero_bot_or_isQuasisimple hK (by omega) j))

private theorem blockFacts_orthLeviBlock {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d) (hdpos : 0 < d (Fin.last s))
    (hm1 : 1 ≤ 3 - d (Fin.last s)) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    BlockFacts (f = 1) False (orthLeviBlock K 3 d b c) := by
  refine ⟨?_, ?_, Or.inl (card_orthLeviBlock_ne_bot_le_two hd)⟩
  · intro j hq
    rcases j with l | u
    · change 3 ∣ Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
            GL (Fin (d l.succ - d l.castSucc)) K).range ⧸
        Subgroup.center ↥(Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →*
            GL (Fin (d l.succ - d l.castSucc)) K).range)
      exact three_dvd_card_quotient_center_range_toGL (K := K)
        (two_le_of_isQuasisimple_specialLinear
          (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) _).symm hq))
    · obtain rfl : u = () := rfl
      change CFSG.Open.IsQuasisimple ↥(orthResDer K b c (3 - d (Fin.last s))) at hq
      change 3 ∣ Nat.card (↥(orthResDer K b c (3 - d (Fin.last s))) ⧸
        Subgroup.center ↥(orthResDer K b c (3 - d (Fin.last s))))
      exact three_dvd_card_orthResDer_quotient_center (m := 3 - d (Fin.last s))
        hK hf hirr hq (by
          have hlast : d (Fin.last s) ≤ 3 := hd.last
          omega)
  · intro j hj
    by_cases hf1 : f = 1
    · exact hf1
    · exact absurd hj (not_nonempty_mulEquiv_perm_three
        (orthLeviBlock_bot_or_isQuasisimple hK (by omega) hm1 hirr j))

private theorem hasLeviDataX_blocksZero {S : Type} [Group S] [Finite S] {J : Subgroup S}
    {f s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d)
    (ρ : ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))) ≃* ↥(⊤ : Subgroup S))
    (hρ : (J.subgroupOf ⊤).comap ρ.toMonoidHom = orthParab 3 (minusTailForm K b c) d)
    (hm0 : 3 - d (Fin.last s) = 0) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (halt : CensusAlt (blocksZero K d b c))
    (hB : BlockFacts (f = 1) False (blocksZero K d b c)) :
    HasLeviDataX (f = 1) False ↥J := by
  classical
  have : Finite (((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  let β : ↥((J.subgroupOf ⊤).comap ρ.toMonoidHom) →*
      ∀ j : Fin s ⊕ Unit, orthLeviGroup K 3 d j :=
    (orthLeviHom b c hd).comp (MulEquiv.subgroupCongr hρ).toMonoidHom
  have hrange : β.range = (orthLeviHom b c hd).range := by
    dsimp only [β]
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (MulEquiv.subgroupCongr hρ).surjective, Subgroup.map_top]
  have hβ : IsPGroup 2 β.ker := by
    have hker_eq : β.ker = Subgroup.comap (MulEquiv.subgroupCongr hρ).toMonoidHom
        (orthLeviHom b c hd).ker := rfl
    rw [hker_eq]
    exact IsPGroup.comap_of_injective (p := 2) (isPGroup_ker_orthLeviHom hd)
      (MulEquiv.subgroupCongr hρ).toMonoidHom (MulEquiv.injective _)
  refine hasLeviDataX_of_mulEquiv le_top ρ β hβ ?_ ?_ ?_
      (blocksZero_isLeviBlock (K := K) (b := b) (c := c)) halt hB
  · rw [hrange]
    exact pi_blocksZero_le_range hd hirr
  · rw [hrange]
    exact orthLeviHom_range_le_normalizer_blocksZero hd
  · rw [hrange]
    exact not_two_dvd_relIndex_pi_blocksZero hd hm0 hirr

private theorem hasLeviDataX_orthLeviBlock {S : Type} [Group S] [Finite S] {J : Subgroup S}
    {f s : ℕ} {d : Fin (s + 1) → ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    (hd : OrthCuts 3 d) (hdpos : 0 < d (Fin.last s)) (hm1 : 1 ≤ 3 - d (Fin.last s))
    (ρ : ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))) ≃* ↥(⊤ : Subgroup S))
    (hρ : (J.subgroupOf ⊤).comap ρ.toMonoidHom = orthParab 3 (minusTailForm K b c) d)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (halt : CensusAlt (orthLeviBlock K 3 d b c))
    (hB : BlockFacts (f = 1) False (orthLeviBlock K 3 d b c)) :
    HasLeviDataX (f = 1) False ↥J := by
  classical
  have : Finite (((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  let β : ↥((J.subgroupOf ⊤).comap ρ.toMonoidHom) →*
      ∀ j : Fin s ⊕ Unit, orthLeviGroup K 3 d j :=
    (orthLeviHom b c hd).comp (MulEquiv.subgroupCongr hρ).toMonoidHom
  have hrange : β.range = (orthLeviHom b c hd).range := by
    dsimp only [β]
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (MulEquiv.subgroupCongr hρ).surjective, Subgroup.map_top]
  have hβ : IsPGroup 2 β.ker := by
    have hker_eq : β.ker = Subgroup.comap (MulEquiv.subgroupCongr hρ).toMonoidHom
        (orthLeviHom b c hd).ker := rfl
    rw [hker_eq]
    exact IsPGroup.comap_of_injective (p := 2) (isPGroup_ker_orthLeviHom hd)
      (MulEquiv.subgroupCongr hρ).toMonoidHom (MulEquiv.injective _)
  refine hasLeviDataX_of_mulEquiv le_top ρ β hβ ?_ ?_ ?_
    (blocksPos_isLeviBlock hK hf hd hdpos hm1 hirr) halt hB
  · rw [hrange]
    exact pi_orthLeviBlock_le_range hd (by norm_num)
      (commutator_orthogonalGroup_quadTail_minus (by norm_num) hirr)
  · rw [hrange]
    exact orthLeviHom_range_le_normalizer_orthLeviBlock hd hirr
  · rw [hrange]
    exact not_two_dvd_relIndex_pi_orthLeviBlock (f := f) hK hd hm1 hirr

theorem hasLeviDataX_of_pomegaMinus {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : CFSG.Blueprint.LieModel S .POmegaMinus 4 2 f) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviDataX (f = 1) False ↥J := by
  classical
  obtain ⟨⟨-, hf, -⟩, K, hKfield, hKfin, hKcard, b, c, hirr, ⟨e'⟩⟩ :=
    h.statedClassicalModel (by decide : .POmegaMinus ∈ CFSG.Blueprint.classicalTags)
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  let φ : ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))) ≃* ↥(⊤ : Subgroup S) :=
    (tailOmegaEquiv (minusTailIsometry (n := 4) (K := K) (b := b) (c := c))
      (coe_quadMinus (n := 4) (K := K) (b := b) (c := c))
      (commutator_orthogonalGroup_quadMinus (K := K) (b := b) (c := c)
        (by norm_num) hirr)).symm.trans
    ((orthMinusStatedProjEquiv (n := 4) (by norm_num)).symm.trans
      (e'.symm.trans Subgroup.topEquiv.symm))
  obtain ⟨ρ, s, d, hd, hρ⟩ := exists_comap_eq_orthParab (r := 3) (by norm_num) hirr
    (isParabolicTwo_top_of_isNontrivialParabolic hJ) φ
  have hdpos : 0 < d (Fin.last s) := by
    by_contra hzero
    have hszero : s = 0 := by
      by_contra hs
      have hlt : (0 : Fin (s + 1)) < Fin.last s := by
        rw [Fin.lt_def]
        simp [Fin.last]
        omega
      have := hd.mono hlt
      rw [hd.zero] at this
      omega
    subst hszero
    have htop : (J.subgroupOf ⊤).comap ρ.toMonoidHom = ⊤ := by
      rw [hρ, orthParab]
      have hdzero : d = fun _ => 0 := by
        funext i
        fin_cases i
        exact hd.zero
      rw [hdzero]
      simp [tailFlag_zero, MulAction.stabilizer_bot]
    have hmap := congrArg (Subgroup.map ρ.toMonoidHom) htop
    rw [Subgroup.map_comap_eq_self_of_surjective ρ.surjective, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr ρ.surjective] at hmap
    exact hJ.2.1 (by simpa using hmap)
  by_cases hm0 : 3 - d (Fin.last s) = 0
  · by_cases hf2 : 2 ≤ f
    · exact hasLeviDataX_blocksZero hd ρ hρ hm0 hirr
        (censusAlt_blocksZero_two_le hKcard hf2 hd)
        (blockFacts_blocksZero hKcard hf hd)
    · have hf1 : f = 1 := by omega
      exact hasLeviDataX_blocksZero hd ρ hρ hm0 hirr
        (censusAlt_blocksZero_eq_one (by rw [hKcard, hf1]; norm_num))
        (blockFacts_blocksZero hKcard hf hd)
  · have hm1 : 1 ≤ 3 - d (Fin.last s) := by
      have := hd.last
      omega
    by_cases hf2 : 2 ≤ f
    · exact hasLeviDataX_orthLeviBlock hKcard hf hd hdpos hm1 ρ hρ hirr
        (censusAlt_orthLeviBlock_two_le hKcard hf2 hd hm1 hirr)
        (blockFacts_orthLeviBlock hKcard hf hd hdpos hm1 hirr)
    · have hf1 : f = 1 := by omega
      exact hasLeviDataX_orthLeviBlock hKcard hf hd hdpos hm1 ρ hρ hirr
        (censusAlt_orthLeviBlock_eq_one hKcard hf1 hd hdpos hm1 hirr)
        (blockFacts_orthLeviBlock hKcard hf hd hdpos hm1 hirr)

theorem hasLeviData_of_pomegaMinus {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : CFSG.Blueprint.LieModel S .POmegaMinus 4 2 f) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviData ↥J :=
  (hasLeviDataX_of_pomegaMinus h hJ).hasLeviData

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
