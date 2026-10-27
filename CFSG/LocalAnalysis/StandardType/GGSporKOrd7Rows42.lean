module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Search
public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdersB

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

def rows42 : List LargeEvenLabel :=
  [⟨.A, 2, 1⟩, ⟨.A, 3, 1⟩, ⟨.A, 4, 1⟩, ⟨.A, 5, 1⟩, ⟨.twA, 3, 1⟩, ⟨.twA, 4, 1⟩, ⟨.twA, 5, 1⟩,
    ⟨.B, 3, 1⟩, ⟨.C, 3, 1⟩, ⟨.B, 4, 1⟩, ⟨.C, 4, 1⟩, ⟨.B, 5, 1⟩, ⟨.C, 5, 1⟩, ⟨.B, 6, 1⟩, ⟨.C, 6, 1⟩,
    ⟨.D, 3, 1⟩, ⟨.D, 4, 1⟩, ⟨.D, 5, 1⟩, ⟨.D, 6, 1⟩, ⟨.twD, 2, 1⟩, ⟨.twD, 3, 1⟩, ⟨.twD, 4, 1⟩,
    ⟨.twD, 5, 1⟩, ⟨.twD, 6, 1⟩, ⟨.F4, 0, 1⟩, ⟨.twE6, 0, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.B2der, 0, 1⟩,
    ⟨.G2der, 0, 1⟩, ⟨.twF4der, 0, 1⟩, ⟨.A, 1, 2⟩, ⟨.A, 2, 2⟩, ⟨.A, 3, 2⟩, ⟨.A, 4, 2⟩, ⟨.A, 5, 2⟩,
    ⟨.twA, 2, 2⟩, ⟨.twA, 3, 2⟩, ⟨.B, 2, 2⟩, ⟨.C, 2, 2⟩, ⟨.B, 3, 2⟩, ⟨.C, 3, 2⟩, ⟨.D, 3, 2⟩,
    ⟨.twD, 2, 2⟩, ⟨.twD, 3, 2⟩, ⟨.G2, 0, 2⟩, ⟨.A, 1, 3⟩, ⟨.twA, 2, 3⟩, ⟨.twA, 3, 3⟩, ⟨.B, 2, 3⟩,
    ⟨.C, 2, 3⟩, ⟨.twD, 2, 3⟩, ⟨.twD, 3, 3⟩, ⟨.twB2, 0, 3⟩, ⟨.A, 1, 4⟩, ⟨.A, 2, 4⟩, ⟨.A, 1, 5⟩,
    ⟨.A, 1, 6⟩]

private def lr2o42_allTags : List LargeEvenLieTag :=
  [.A, .twA, .B, .C, .D, .twD, .E6, .E7, .E8, .F4, .twE6, .triD4, .G2, .twB2,
   .B2der, .G2der, .twF4der]

private theorem lr2o42_mem_allTags {t : LargeEvenLieTag} (ht : t ≠ .twF4) :
    t ∈ lr2o42_allTags := by
  cases t <;> simp_all [lr2o42_allTags]

open CFSG.EvenSmallLie.CatalogOrders in
private theorem lr2o42_markTag_mem_searchTags {lab : LargeEvenLabel} (h4 : lab.tag ≠ .twF4)
    (h4d : lab.tag ≠ .twF4der) : markTag lab ∈ searchTags := by
  by_contra h
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals first
    | exact absurd rfl h4
    | exact absurd rfl h4d
    | (exfalso; exact h (by
        simp only [markTag]
        first | (split_ifs <;> simp [searchTags]) | simp [searchTags]))

open CFSG.EvenSmallLie.CatalogOrders in
private theorem lr2o42_lieMin_markTag_le_markRank {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) : lieMin (markTag lab) ≤ markRank lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;> simp only [markTag, markRank]
  all_goals first | (split_ifs <;> simp only [lieMin] <;> omega) | (simp only [lieMin]; omega)

private theorem lr2o42_markRank_zero_or_classical (lab : LargeEvenLabel) :
    markRank lab = 0 ∨ markTag lab = .PSL ∨ markTag lab = .PSU ∨ markTag lab = .PSp ∨
      markTag lab = .POmegaOdd ∨ markTag lab = .POmegaPlus ∨ markTag lab = .POmegaMinus := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, markRank]
  all_goals first | (split_ifs <;> simp) | simp

open CFSG.EvenSmallLie.CatalogOrders in
private theorem lr2o42_markRank_le_lieExp_add_one {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) :
    markRank lab ≤ lieExp (markTag lab) (markRank lab) + 1 :=
  le_lieExp_add_one (lr2o42_lieMin_markTag_le_markRank hl) (lr2o42_markRank_zero_or_classical lab)

private theorem lr2o42_one_le_markDeg {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) :
    1 ≤ markDeg lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;> simp only [markDeg]
  all_goals first | (split_ifs <;> omega) | omega

open CFSG.EvenSmallLie.CatalogOrders in
private theorem lr2o42_lieAdm_markTag {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) :
    lieAdm (markTag lab) (markChar lab) (markDeg lab) = true := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;>
    simp only [lieAdm, markTag, markChar, markDeg]
  case twB2 =>
    obtain ⟨-, -, hodd, h3⟩ := hl
    rw [Nat.odd_iff] at hodd
    simp [hodd, h3]
  all_goals first | rfl | (split_ifs <;> rfl)

open CFSG.EvenSmallLie.CatalogOrders in
private theorem lr2o42_labOrd_eq_lieOrd_of_markTag_mem {lab : LargeEvenLabel}
    (ht : markTag lab ∈ searchTags) :
    labOrd lab = lieOrd (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [labOrd, markTag, markRank, markChar, markDeg]
  all_goals first | rfl |
    (exact absurd ht (by simp only [markTag, searchTags]; decide))

private theorem lr2o42_rank_le_markRank {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    lab.rank ≤ markRank lab := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hlab <;> simp only [markRank]
  all_goals first | (split_ifs <;> omega) | omega

private theorem lr2o42_n_le_markDeg {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    lab.n ≤ markDeg lab := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hlab <;> simp only [markDeg]
  all_goals first | (split_ifs <;> omega) | omega

private def lr2o42_lam2 (lab : LargeEvenLabel) : Bool :=
  decide (1 ≤ lab.n) &&
    match lab.tag with
    | .A => decide (1 ≤ lab.rank) && decide (lab.rank = 1 → 2 ≤ lab.n)
    | .twA => decide (2 ≤ lab.rank) && decide (lab.rank = 2 → 2 ≤ lab.n)
    | .B | .C => decide (2 ≤ lab.rank) && decide (lab.rank = 2 → 2 ≤ lab.n)
    | .D => decide (3 ≤ lab.rank)
    | .twD => decide (2 ≤ lab.rank)
    | .E6 | .E7 | .E8 | .F4 | .twE6 | .triD4 => decide (lab.rank = 0)
    | .G2 => decide (lab.rank = 0) && decide (2 ≤ lab.n)
    | .twB2 | .twF4 => decide (lab.rank = 0) && decide (Odd lab.n) && decide (3 ≤ lab.n)
    | .B2der | .G2der | .twF4der => decide (lab.rank = 0) && decide (lab.n = 1)

private theorem lr2o42_lam2_eq_true_iff (lab : LargeEvenLabel) :
    lr2o42_lam2 lab = true ↔ LargeEvenInLambda2 lab := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;>
    simp only [lr2o42_lam2, LargeEvenInLambda2, Bool.and_eq_true, decide_eq_true_iff] <;>
    tauto

private def lr2o42_memRows (t : LargeEvenLieTag) (r n : ℕ) : Bool :=
  rows42.any fun l => l.tag == t && l.rank == r && l.n == n

private theorem lr2o42_memRows_eq_true_iff (t : LargeEvenLieTag) (r n : ℕ) :
    lr2o42_memRows t r n = true ↔ (⟨t, r, n⟩ : LargeEvenLabel) ∈ rows42 := by
  simp only [lr2o42_memRows]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hp⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    have he : l = (⟨t, r, n⟩ : LargeEvenLabel) := by
      obtain ⟨lt, lr, ln⟩ := l
      subst h1; subst h2; subst h3; rfl
    rwa [he] at hl
  · rintro h
    exact ⟨(⟨t, r, n⟩ : LargeEvenLabel), h, by simp⟩

private theorem lr2o42_memRows_mem {t : LargeEvenLieTag} {r n : ℕ}
    (h : lr2o42_memRows t r n = true) : (⟨t, r, n⟩ : LargeEvenLabel) ∈ rows42 :=
  (lr2o42_memRows_eq_true_iff t r n).mp h

private theorem lr2o42_box_all :
    (lr2o42_allTags.all fun t =>
      (List.range 14).all fun r =>
        (List.range 42).all fun n =>
          !(lr2o42_lam2 (⟨t, r, n⟩ : LargeEvenLabel)) ||
            !(4154781481226426191177580544000000 % labOrd (⟨t, r, n⟩ : LargeEvenLabel) == 0) ||
            lr2o42_memRows t r n) = true := by
  decide +kernel

private theorem lr2o42_box (t : LargeEvenLieTag) (ht : t ∈ lr2o42_allTags)
    (r : ℕ) (hr : r < 14) (n : ℕ) (hn : n < 42)
    (hlam : lr2o42_lam2 (⟨t, r, n⟩ : LargeEvenLabel) = true)
    (hmod : 4154781481226426191177580544000000 % labOrd (⟨t, r, n⟩ : LargeEvenLabel) = 0) :
    (⟨t, r, n⟩ : LargeEvenLabel) ∈ rows42 := by
  have hbox := lr2o42_box_all
  rw [List.all_eq_true] at hbox
  have h1 := hbox t ht
  rw [List.all_eq_true] at h1
  have h2 := h1 r (List.mem_range.mpr hr)
  rw [List.all_eq_true] at h2
  have h3 := h2 n (List.mem_range.mpr hn)
  simp [hlam, hmod] at h3
  exact lr2o42_memRows_mem h3

private def lr2o42_classical : StatedLieTag → Bool
  | .PSL | .PSU | .PSp | .POmegaOdd | .POmegaPlus | .POmegaMinus => true
  | _ => false

private def lr2o42_C (t : StatedLieTag) (n q : ℕ) : Bool :=
  (!(lr2o42_classical t) || decide (n ≤ 12)) && decide (q ≤ 2 ^ 41)

private theorem lr2o42_C_q {t : StatedLieTag} {n q : ℕ} (h : lr2o42_C t n q = true) :
    decide (q ≤ 2 ^ 41) = true := by
  unfold lr2o42_C at h
  rw [Bool.and_eq_true] at h
  exact h.2

private theorem lr2o42_C_n {t : StatedLieTag} {n q : ℕ} (h : lr2o42_C t n q = true)
    (ht : lr2o42_classical t = true) : decide (n ≤ 12) = true := by
  unfold lr2o42_C at h
  rw [Bool.and_eq_true] at h
  have h1 : (!(lr2o42_classical t) || decide (n ≤ 12)) = true := h.1
  rw [ht] at h1
  simpa using h1

open CFSG.EvenSmallLie.CatalogOrders in
private theorem lr2o42_lieSearchBound :
    lieSearch [2] 4154781481226426191177580544000000
      (fun t n q _ => lr2o42_C t n q) = true := by
  decide +kernel

open CFSG.EvenSmallLie.CatalogOrders in
private theorem lr2o42_markRank_markDeg_bounds {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htw : lab.tag ≠ .twF4) (htwd : lab.tag ≠ .twF4der)
    (hchar : markChar lab = 2) (hd : labOrd lab ∣ 4154781481226426191177580544000000) :
    markRank lab ≤ 12 ∧ markDeg lab ≤ 41 := by
  have htmem : markTag lab ∈ searchTags := lr2o42_markTag_mem_searchTags htw htwd
  have hmin : lieMin (markTag lab) ≤ markRank lab := lr2o42_lieMin_markTag_le_markRank hlab
  have hle : markRank lab ≤ lieExp (markTag lab) (markRank lab) + 1 :=
    lr2o42_markRank_le_lieExp_add_one hlab
  have hadm : lieAdm (markTag lab) 2 (markDeg lab) = true := by
    rw [← hchar]; exact lr2o42_lieAdm_markTag hlab
  have hf : 1 ≤ markDeg lab := lr2o42_one_le_markDeg hlab
  have hlabOrd : labOrd lab = lieOrd (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) :=
    lr2o42_labOrd_eq_lieOrd_of_markTag_mem htmem
  have hd' : lieOrd (markTag lab) (markRank lab) (2 ^ markDeg lab) ∣
      4154781481226426191177580544000000 := by
    rw [← hchar, ← hlabOrd]; exact hd
  have hC : lr2o42_C (markTag lab) (markRank lab) (2 ^ markDeg lab) = true :=
    lr2o_lieSearch_sound_mem (ps := [2]) (N := 4154781481226426191177580544000000)
      (C := fun t n q _ => lr2o42_C t n q)
      (hN := by norm_num) (hS := lr2o42_lieSearchBound)
      (t := markTag lab) (n := markRank lab) (p := 2) (f := markDeg lab)
      htmem (by norm_num) (by decide) hf hmin hle hadm hd'
  have hq : decide (2 ^ markDeg lab ≤ 2 ^ 41) = true := lr2o42_C_q hC
  have hn : markRank lab ≤ 12 := by
    rcases lr2o42_markRank_zero_or_classical lab with h0 | h | h | h | h | h | h
    · omega
    all_goals exact of_decide_eq_true (lr2o42_C_n hC (by rw [h]; rfl))
  exact ⟨hn, (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp (of_decide_eq_true hq)⟩

private theorem lr2o42_small_mem {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) : lab ∈ rows42 := by
  obtain ⟨t, r, n⟩ := lab
  rcases htag with h | h | h
  · change t = .B2der at h
    subst h
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hr, hn⟩ := hlab
    subst hr; subst hn
    exact lr2o42_memRows_mem (by decide)
  · change t = .G2der at h
    subst h
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hr, hn⟩ := hlab
    subst hr; subst hn
    exact lr2o42_memRows_mem (by decide)
  · change t = .twF4der at h
    subst h
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hr, hn⟩ := hlab
    subst hr; subst hn
    exact lr2o42_memRows_mem (by decide)

theorem mem_rows42_of_dvd {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : labOrd lab ∣ 4154781481226426191177580544000000) : lab ∈ rows42 := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨htw, _⟩ := ord7_search_B hlab hd
  by_cases hsmall : t = .B2der ∨ t = .G2der ∨ t = .twF4der
  · exact lr2o42_small_mem hlab hsmall
  · have h4d : t ≠ .twF4der := fun h => hsmall (Or.inr (Or.inr h))
    have hchar : markChar (⟨t, r, n⟩ : LargeEvenLabel) = 2 := by
      cases t <;> first | rfl | (exfalso; exact hsmall (by simp))
    have hb := lr2o42_markRank_markDeg_bounds hlab htw h4d hchar hd
    have hrm : r ≤ markRank (⟨t, r, n⟩ : LargeEvenLabel) := lr2o42_rank_le_markRank hlab
    have hnm : n ≤ markDeg (⟨t, r, n⟩ : LargeEvenLabel) := lr2o42_n_le_markDeg hlab
    have hr : r < 14 := by omega
    have hn : n < 42 := by omega
    have hlam : lr2o42_lam2 (⟨t, r, n⟩ : LargeEvenLabel) = true :=
      (lr2o42_lam2_eq_true_iff _).mpr hlab
    have hmod : 4154781481226426191177580544000000 % labOrd (⟨t, r, n⟩ : LargeEvenLabel) = 0 :=
      Nat.mod_eq_zero_of_dvd hd
    exact lr2o42_box t (lr2o42_mem_allTags htw) r hr n hn hlam hmod

theorem rows42_spec {lab : LargeEvenLabel} (h : lab ∈ rows42) :
    LargeEvenInLambda2 lab ∧ labOrd lab ∣ 4154781481226426191177580544000000 := by
  have hbox : rows42.all (fun l =>
      lr2o42_lam2 l && (4154781481226426191177580544000000 % labOrd l == 0)) = true := by
    decide +kernel
  rw [List.all_eq_true] at hbox
  have h1 := hbox lab h
  rw [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨(lr2o42_lam2_eq_true_iff lab).mp h1.1, Nat.dvd_iff_mod_eq_zero.mpr h1.2⟩

theorem mem_rows42_of_marked
    {L : Subgroup (TauCeti.CFSGIndex.sporadic .B).Group} (hLs : IsSimpleGroup L)
    (hmark : StandardType.LargeEvenMarking L (fun _ _ _ _ _ _ => True)) :
    ∃ lab ∈ rows42, MarkedModel lab ↥L ∧ Nat.card ↥L = labOrd lab ∧
      labOrd lab ∣ Nat.card (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨lab, hlab, hmodel, hcard⟩ := largeEvenMarking_card_labOrd hmark
  have hc : Subgroup.center ↥L = ⊥ := by
    rcases hLs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      have hbot : commutator ↥L = ⊥ := by
        rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro g _
        exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x)) g
      have htop : commutator ↥L = ⊤ := hmark.1
      haveI := hLs.toNontrivial
      rw [hbot] at htop
      exact bot_ne_top htop
  have e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hmodelL : MarkedModel lab ↥L := MarkedModel.of_mulEquiv e hmodel
  have hcardL : Nat.card ↥L = labOrd lab := by
    rw [← hcard]
    exact (Nat.card_congr e.toEquiv).symm
  have hdvd : labOrd lab ∣ Nat.card (TauCeti.CFSGIndex.sporadic .B).Group := by
    rw [← hcardL]
    exact Subgroup.card_subgroup_dvd_card L
  have hdvdB : labOrd lab ∣ 4154781481226426191177580544000000 := by
    rw [← ggSporK_card_sporadicB]
    exact hdvd
  exact ⟨lab, mem_rows42_of_dvd hlab hdvdB, hmodelL, hcardL, hdvd⟩

open CFSG.EvenSmallLie.CatalogOrders in
theorem lr2o_labSearch_sound {N : ℕ} (hN : N ≠ 0)
    {C : StatedLieTag → ℕ → ℕ → ℕ → Bool}
    (hS : CFSG.EvenSmallLie.CatalogOrders.lieSearch [2] N C = true) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hc : markChar lab = 2)
    (hnt : lab.tag ≠ .twF4 ∧ lab.tag ≠ .twF4der) (hd : labOrd lab ∣ N) :
    C (markTag lab) (markRank lab) (2 ^ markDeg lab) (labOrd lab) = true := by
  have htmem : markTag lab ∈ CFSG.EvenSmallLie.CatalogOrders.searchTags := lr2o42_markTag_mem_searchTags hnt.1 hnt.2
  have hlabOrd : labOrd lab = lieOrd (markTag lab) (markRank lab) (2 ^ markDeg lab) := by
    rw [lr2o42_labOrd_eq_lieOrd_of_markTag_mem htmem, hc]
  have hadm : lieAdm (markTag lab) 2 (markDeg lab) = true := by
    rw [← hc]; exact lr2o42_lieAdm_markTag hlab
  have hd' : lieOrd (markTag lab) (markRank lab) (2 ^ markDeg lab) ∣ N := by
    rw [← hlabOrd]; exact hd
  have h := lr2o_lieSearch_sound_mem (ps := [2]) (N := N) (C := C) hN hS htmem
    (p := 2) (f := markDeg lab) Nat.prime_two (List.mem_singleton_self 2)
    (lr2o42_one_le_markDeg hlab) (lr2o42_lieMin_markTag_le_markRank hlab)
    (lr2o42_markRank_le_lieExp_add_one hlab) hadm hd'
  simpa [hlabOrd] using h

end CFSG.StandardType.SporadicShape
