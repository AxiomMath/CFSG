module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.EvenSmallLie.CatalogOrders

private theorem lr2os_markTag_mem_searchTags {lab : LargeEvenLabel} (h4 : lab.tag ≠ .twF4)
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

private theorem lr2os_lieMin_markTag_le_markRank {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) : lieMin (markTag lab) ≤ markRank lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;> simp only [markTag, markRank]
  all_goals first | (split_ifs <;> simp only [lieMin] <;> omega) | (simp only [lieMin]; omega)

private theorem lr2os_markRank_zero_or_classical (lab : LargeEvenLabel) :
    markRank lab = 0 ∨ markTag lab = .PSL ∨ markTag lab = .PSU ∨ markTag lab = .PSp ∨
      markTag lab = .POmegaOdd ∨ markTag lab = .POmegaPlus ∨ markTag lab = .POmegaMinus := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, markRank]
  all_goals first | (split_ifs <;> simp) | simp

private theorem lr2os_markRank_le_lieExp_add_one {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) :
    markRank lab ≤ lieExp (markTag lab) (markRank lab) + 1 :=
  le_lieExp_add_one (lr2os_lieMin_markTag_le_markRank hl) (lr2os_markRank_zero_or_classical lab)

private theorem lr2os_one_le_markDeg {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) :
    1 ≤ markDeg lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;> simp only [markDeg]
  all_goals first | (split_ifs <;> omega) | omega

private theorem lr2os_lieAdm_markTag {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) :
    lieAdm (markTag lab) (markChar lab) (markDeg lab) = true := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;>
    simp only [lieAdm, markTag, markChar, markDeg]
  case twB2 =>
    obtain ⟨-, -, hodd, h3⟩ := hl
    rw [Nat.odd_iff] at hodd
    simp [hodd, h3]
  all_goals first | rfl | (split_ifs <;> rfl)

private theorem lr2os_labOrd_eq_lieOrd_of_markTag_mem {lab : LargeEvenLabel}
    (ht : markTag lab ∈ searchTags) :
    labOrd lab = lieOrd (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [labOrd, markTag, markRank, markChar, markDeg]
  all_goals first | rfl |
    (exact absurd ht (by simp only [markTag, searchTags]; decide))

private theorem lr2os_labOrd_twF4_eq {lab : LargeEvenLabel} (h : lab.tag = .twF4) :
    labOrd lab = CFSG.Open.ordTwistedF4 (2 ^ lab.n) := by
  obtain ⟨t, l, n⟩ := lab
  subst h
  rfl

private theorem lr2os_twF4_facts {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (h : lab.tag = .twF4) : 3 ≤ lab.n ∧ Odd lab.n := by
  obtain ⟨t, l, n⟩ := lab
  subst h
  simp only [LargeEvenInLambda2] at hl
  exact ⟨hl.2.2.2, hl.2.2.1⟩

private theorem lr2os_pow_dvd_ordTwistedF4 (q : ℕ) : q ^ 12 ∣ CFSG.Open.ordTwistedF4 q := by
  unfold CFSG.Open.ordTwistedF4
  simp only [mul_assoc]
  exact dvd_mul_right _ _

private theorem lr2os_markTag_E6_of_tag {lab : LargeEvenLabel} (h : lab.tag = .E6) :
    markTag lab = .E6 := by
  obtain ⟨t, l, n⟩ := lab
  subst h
  rfl

private theorem lr2os_markTag_E7_of_tag {lab : LargeEvenLabel} (h : lab.tag = .E7) :
    markTag lab = .E7 := by
  obtain ⟨t, l, n⟩ := lab
  subst h
  rfl

private theorem lr2os_markTag_E8_of_tag {lab : LargeEvenLabel} (h : lab.tag = .E8) :
    markTag lab = .E8 := by
  obtain ⟨t, l, n⟩ := lab
  subst h
  rfl

@[expose] def ord7Pred (t : StatedLieTag) (n q : ℕ) : Bool :=
  (q - 1) % 127 != 0 && (t != .PSL || n == 2 || (q - 1) % 7 != 0) &&
    (t != .E6 && t != .E7 && t != .E8) && (t != .POmegaPlus || n != 4 || q == 2)

theorem ord7_lieSearch_B :
    lieSearch [2] 4154781481226426191177580544000000 (fun t n q _ => ord7Pred t n q) = true := by
  decide +kernel

theorem lr2o_lieSearch_sound_mem {ps : List ℕ} {N : ℕ} (hN : N ≠ 0)
    {C : StatedLieTag → ℕ → ℕ → ℕ → Bool} (hS : lieSearch ps N C = true) {t : StatedLieTag}
    (ht : t ∈ searchTags) {n p f : ℕ} (hp : p.Prime) (hpm : p ∈ ps) (hf : 1 ≤ f) (hn : lieMin t ≤ n)
    (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true) (hd : lieOrd t n (p ^ f) ∣ N) :
    C t n (p ^ f) (lieOrd t n (p ^ f)) = true := by
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hqd : (p ^ f) ^ lieExp t n ∣ N := (pow_dvd_pow_of_dvd (dvd_refl _) _).trans
    ((pow_lieExp_dvd hn _).trans hd)
  have he := one_le_lieExp ht hn
  have hfB : f ≤ Nat.log 2 N := le_log_of_pow_dvd hN hp.two_le
    ((pow_dvd_pow p (Nat.le_mul_of_pos_right f he)).trans (by rw [pow_mul]; exact hqd))
  have heB : lieExp t n ≤ Nat.log 2 N := le_log_of_pow_dvd hN hq hqd
  unfold lieSearch at hS
  rw [List.all_eq_true] at hS
  have h1 := hS p hpm
  rw [List.all_eq_true] at h1
  have h2 := h1 (f - 1) (List.mem_range.2 (by omega))
  rw [List.all_eq_true] at h2
  have h3 := h2 t ht
  rw [List.all_eq_true] at h3
  have h4 := h3 n (List.mem_range.2 (by omega))
  rw [Nat.sub_add_cancel hf] at h4
  have hg : (decide (lieMin t ≤ n) && lieAdm t p f && N % ((p ^ f) ^ lieExp t n) == 0 &&
      N % lieOrd t n (p ^ f) == 0) = true := by
    simp [hn, hadm, Nat.mod_eq_zero_of_dvd hqd, Nat.mod_eq_zero_of_dvd hd]
  rw [hg] at h4
  simpa using h4

theorem ord7_search_B {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hd : labOrd lab ∣ 4154781481226426191177580544000000) :
    lab.tag ≠ .twF4 ∧ (lab.tag ≠ .twF4der → markChar lab = 2 →
      ¬ 7 ∣ markDeg lab ∧ (markTag lab = .PSL → 3 ≤ markRank lab → ¬ 7 ∣ 2 ^ markDeg lab - 1) ∧
        lab.tag ≠ .E6 ∧ lab.tag ≠ .E7 ∧ lab.tag ≠ .E8 ∧
        (lab.tag = .D → lab.rank = 4 → markDeg lab = 1)) := by
  have htw : lab.tag ≠ .twF4 := by
    intro htag
    obtain ⟨hn3, _hodd⟩ := lr2os_twF4_facts hlab htag
    have hld : labOrd lab = CFSG.Open.ordTwistedF4 (2 ^ lab.n) := lr2os_labOrd_twF4_eq htag
    have hdF4 : CFSG.Open.ordTwistedF4 (2 ^ lab.n) ∣ 4154781481226426191177580544000000 := by
      rw [← hld]
      exact hd
    have h2dvd : 2 ^ (12 * lab.n) ∣ 4154781481226426191177580544000000 := by
      have hq : (2 ^ lab.n) ^ 12 = 2 ^ (12 * lab.n) := by rw [← pow_mul, mul_comm]
      have h := lr2os_pow_dvd_ordTwistedF4 (2 ^ lab.n)
      rw [hq] at h
      exact h.trans hdF4
    have h42 : ¬ 2 ^ 42 ∣ 4154781481226426191177580544000000 := by decide +kernel
    have hbound : 12 * lab.n ≤ 41 := by
      by_contra h
      exact h42 (dvd_trans (Nat.pow_dvd_pow 2 (by omega : 42 ≤ 12 * lab.n)) h2dvd)
    have hn_eq : lab.n = 3 := by omega
    have h37 : 37 ∣ CFSG.Open.ordTwistedF4 (2 ^ lab.n) := by
      rw [hn_eq]
      decide +kernel
    have h37N : ¬ 37 ∣ 4154781481226426191177580544000000 := by decide +kernel
    exact h37N (dvd_trans h37 hdF4)
  refine ⟨htw, ?_⟩
  intro htagder hchar
  have htmem : markTag lab ∈ searchTags := lr2os_markTag_mem_searchTags htw htagder
  have hmin : lieMin (markTag lab) ≤ markRank lab := lr2os_lieMin_markTag_le_markRank hlab
  have hle : markRank lab ≤ lieExp (markTag lab) (markRank lab) + 1 :=
    lr2os_markRank_le_lieExp_add_one hlab
  have hadm : lieAdm (markTag lab) 2 (markDeg lab) = true := by
    rw [← hchar]
    exact lr2os_lieAdm_markTag hlab
  have hf : 1 ≤ markDeg lab := lr2os_one_le_markDeg hlab
  have hlabOrd : labOrd lab = lieOrd (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) :=
    lr2os_labOrd_eq_lieOrd_of_markTag_mem htmem
  have hd' : lieOrd (markTag lab) (markRank lab) (2 ^ markDeg lab) ∣
      4154781481226426191177580544000000 := by
    rw [← hchar, ← hlabOrd]
    exact hd
  have hC : ord7Pred (markTag lab) (markRank lab) (2 ^ markDeg lab) = true :=
    lr2o_lieSearch_sound_mem (ps := [2]) (N := 4154781481226426191177580544000000)
      (C := fun t n q _ => ord7Pred t n q) (t := markTag lab) (n := markRank lab) (p := 2)
      (f := markDeg lab) (by norm_num) ord7_lieSearch_B htmem (by norm_num) (by decide) hf
      hmin hle hadm hd'
  have h127 : (2 ^ markDeg lab - 1) % 127 ≠ 0 := by
    intro h
    simpa [ord7Pred, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, h] using hC
  have h7f : ¬ 7 ∣ markDeg lab := by
    intro h7
    obtain ⟨k, hk⟩ := h7
    have hdvd : 127 ∣ 2 ^ markDeg lab - 1 := by
      rw [hk]
      have h := Nat.sub_dvd_pow_sub_pow (2 ^ 7) 1 k
      have h2 : (2 ^ 7) ^ k = 2 ^ (7 * k) := by rw [← pow_mul]
      rw [h2, one_pow] at h
      norm_num at h
      exact h
    exact h127 (Nat.mod_eq_zero_of_dvd hdvd)
  have hPSL : markTag lab = .PSL → 3 ≤ markRank lab → ¬ 7 ∣ 2 ^ markDeg lab - 1 := by
    intro ht h3 h7
    have hmod : (2 ^ markDeg lab - 1) % 7 = 0 := Nat.dvd_iff_mod_eq_zero.mp h7
    have hn2 : markRank lab ≠ 2 := by omega
    simpa [ord7Pred, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ht, hmod, hn2]
      using hC
  have hE6 : markTag lab ≠ .E6 := by
    intro h
    simpa [ord7Pred, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, h] using hC
  have hE7 : markTag lab ≠ .E7 := by
    intro h
    simpa [ord7Pred, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, h] using hC
  have hE8 : markTag lab ≠ .E8 := by
    intro h
    simpa [ord7Pred, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, h] using hC
  have hE6' : lab.tag ≠ .E6 := fun h => hE6 (lr2os_markTag_E6_of_tag h)
  have hE7' : lab.tag ≠ .E7 := fun h => hE7 (lr2os_markTag_E7_of_tag h)
  have hE8' : lab.tag ≠ .E8 := fun h => hE8 (lr2os_markTag_E8_of_tag h)
  have hDclause : lab.tag = .D → lab.rank = 4 → markDeg lab = 1 := by
    intro hDtag hDrank
    have ht : markTag lab = .POmegaPlus := by
      obtain ⟨u, l, n⟩ := lab
      change u = .D at hDtag
      change l = 4 at hDrank
      subst hDtag
      subst hDrank
      rfl
    have hn : markRank lab = 4 := by
      obtain ⟨u, l, n⟩ := lab
      change u = .D at hDtag
      change l = 4 at hDrank
      subst hDtag
      subst hDrank
      rfl
    have hlast : 2 ^ markDeg lab = 2 := by
      by_contra h
      simpa [ord7Pred, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ht, hn, h]
        using hC
    exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) (by simpa [hlast])
  exact ⟨h7f, hPSL, hE6', hE7', hE8', hDclause⟩

end CFSG.StandardType.SporadicShape
