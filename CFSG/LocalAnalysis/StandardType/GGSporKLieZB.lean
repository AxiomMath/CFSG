module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZRows
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Rows42

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

private def l937z_zb_inSq (l : LargeEvenLabel) : Bool :=
  sevenSqLabels.any fun m => m.tag == l.tag && m.rank == l.rank && m.n == l.n

private theorem l937z_zb_inSq_iff (lab : LargeEvenLabel) :
    l937z_zb_inSq lab = true ↔ lab ∈ sevenSqLabels := by
  simp only [l937z_zb_inSq]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hp⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    have he : l = lab := by
      obtain ⟨lt, lr, ln⟩ := l
      obtain ⟨mt, mr, mn⟩ := lab
      subst h1; subst h2; subst h3; rfl
    rwa [he] at hl
  · rintro h
    exact ⟨lab, h, by simp⟩

private def l937z_zb_tags : List LargeEvenLieTag :=
  [.A, .twA, .B, .C, .D, .twD, .E6, .E7, .E8, .F4, .twE6, .triD4, .G2, .twB2,
   .B2der, .G2der, .twF4der]

private theorem l937z_zb_mem_tags {t : LargeEvenLieTag} (ht : t ≠ .twF4) :
    t ∈ l937z_zb_tags := by
  cases t <;> simp_all [l937z_zb_tags]

private def l937z_zb_classical : StatedLieTag → Bool
  | .PSL | .PSU | .PSp | .POmegaOdd | .POmegaPlus | .POmegaMinus => true
  | _ => false

private def l937z_zb_C (t : StatedLieTag) (n q : ℕ) : Bool :=
  (!(l937z_zb_classical t) || decide (n ≤ 12)) && decide (q ≤ 2 ^ 41)

private theorem l937z_zb_C_q {t : StatedLieTag} {n q : ℕ} (h : l937z_zb_C t n q = true) :
    decide (q ≤ 2 ^ 41) = true := by
  unfold l937z_zb_C at h
  rw [Bool.and_eq_true] at h
  exact h.2

private theorem l937z_zb_C_n {t : StatedLieTag} {n q : ℕ} (h : l937z_zb_C t n q = true)
    (ht : l937z_zb_classical t = true) : decide (n ≤ 12) = true := by
  unfold l937z_zb_C at h
  rw [Bool.and_eq_true] at h
  have h1 : (!(l937z_zb_classical t) || decide (n ≤ 12)) = true := h.1
  rw [ht] at h1
  simpa using h1

private theorem l937z_zb_lieSearchBound :
    CFSG.EvenSmallLie.CatalogOrders.lieSearch [2] 4154781481226426191177580544000000
      (fun t n q _ => l937z_zb_C t n q) = true := by
  decide +kernel

private theorem l937z_zb_markRank_zero_or_classical (lab : LargeEvenLabel) :
    markRank lab = 0 ∨ markTag lab = .PSL ∨ markTag lab = .PSU ∨ markTag lab = .PSp ∨
      markTag lab = .POmegaOdd ∨ markTag lab = .POmegaPlus ∨ markTag lab = .POmegaMinus := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, markRank]
  all_goals first | (split_ifs <;> simp) | simp

private theorem l937z_zb_rank_le_markRank {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    lab.rank ≤ markRank lab := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hlab <;> simp only [markRank]
  all_goals first | (split_ifs <;> omega) | omega

private theorem l937z_zb_n_le_markDeg {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    lab.n ≤ markDeg lab := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hlab <;> simp only [markDeg]
  all_goals first | (split_ifs <;> omega) | omega

private def l937z_zb_lam2 (lab : LargeEvenLabel) : Bool :=
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

private theorem l937z_zb_lam2_iff (lab : LargeEvenLabel) :
    l937z_zb_lam2 lab = true ↔ LargeEvenInLambda2 lab := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;>
    simp only [l937z_zb_lam2, LargeEvenInLambda2, Bool.and_eq_true, decide_eq_true_iff] <;>
    tauto

private theorem l937z_zb_box_all :
    (l937z_zb_tags.all fun t =>
      (List.range 13).all fun r =>
        (List.range 42).all fun n =>
          !(l937z_zb_lam2 (⟨t, r, n⟩ : LargeEvenLabel)) ||
            !(decide (labOrd (⟨t, r, n⟩ : LargeEvenLabel) ∣
              4154781481226426191177580544000000)) ||
            !(decide (7 ^ 2 ∣ labOrd (⟨t, r, n⟩ : LargeEvenLabel))) ||
            l937z_zb_inSq (⟨t, r, n⟩ : LargeEvenLabel)) = true := by
  decide +kernel

private theorem l937z_zb_box (t : LargeEvenLieTag) (ht : t ∈ l937z_zb_tags)
    (r : ℕ) (hr : r < 13) (n : ℕ) (hn : n < 42)
    (hlam : l937z_zb_lam2 (⟨t, r, n⟩ : LargeEvenLabel) = true)
    (hdvd : labOrd (⟨t, r, n⟩ : LargeEvenLabel) ∣ 4154781481226426191177580544000000)
    (h49 : 7 ^ 2 ∣ labOrd (⟨t, r, n⟩ : LargeEvenLabel)) :
    l937z_zb_inSq (⟨t, r, n⟩ : LargeEvenLabel) = true := by
  have hbox := l937z_zb_box_all
  rw [List.all_eq_true] at hbox
  have h1 := hbox t ht
  rw [List.all_eq_true] at h1
  have h2 := h1 r (List.mem_range.mpr hr)
  rw [List.all_eq_true] at h2
  have h3 := h2 n (List.mem_range.mpr hn)
  simp only [hlam, decide_eq_true hdvd, decide_eq_true h49, Bool.not_true,
    Bool.false_or] at h3
  exact h3

theorem sevenSq_of_rows42 : ∀ lab ∈ rows42, 7 ^ 2 ∣ labOrd lab → lab ∈ sevenSqLabels := by
  intro lab hlab h49
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨hlam2, hdvd⟩ := rows42_spec hlab
  have htw : t ≠ .twF4 := (ord7_search_B hlam2 hdvd).1
  have htwd : t ≠ .twF4der := by
    intro h
    have hc : ¬ 7 ^ 2 ∣ labOrd (⟨.twF4der, r, n⟩ : LargeEvenLabel) := by
      rw [show labOrd (⟨.twF4der, r, n⟩ : LargeEvenLabel) = CFSG.Open.ordTits from rfl]
      decide +kernel
    rw [h] at h49
    exact absurd h49 hc
  have hB2 : t ≠ .B2der := by
    intro h
    rw [h] at h49
    exact absurd h49 (by
      change ¬ 7 ^ 2 ∣ labOrd (⟨.B2der, 0, 0⟩ : LargeEvenLabel)
      decide +kernel)
  have hG2 : t ≠ .G2der := by
    intro h
    rw [h] at h49
    exact absurd h49 (by
      change ¬ 7 ^ 2 ∣ labOrd (⟨.G2der, 0, 0⟩ : LargeEvenLabel)
      decide +kernel)
  have hchar : markChar (⟨t, r, n⟩ : LargeEvenLabel) = 2 := by
    cases t <;> simp only [markChar]
    all_goals first | rfl | (exfalso; exact hB2 rfl) | (exfalso; exact hG2 rfl)
  have hC : l937z_zb_C (markTag (⟨t, r, n⟩ : LargeEvenLabel))
      (markRank (⟨t, r, n⟩ : LargeEvenLabel))
      (2 ^ markDeg (⟨t, r, n⟩ : LargeEvenLabel)) = true :=
    lr2o_labSearch_sound (N := 4154781481226426191177580544000000)
      (C := fun a b c _ => l937z_zb_C a b c) (by norm_num) l937z_zb_lieSearchBound
      hlam2 hchar ⟨htw, htwd⟩ hdvd
  have hq : 2 ^ markDeg (⟨t, r, n⟩ : LargeEvenLabel) ≤ 2 ^ 41 :=
    of_decide_eq_true (l937z_zb_C_q hC)
  have hdeg : markDeg (⟨t, r, n⟩ : LargeEvenLabel) ≤ 41 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hq
  have hrank : markRank (⟨t, r, n⟩ : LargeEvenLabel) ≤ 12 := by
    rcases l937z_zb_markRank_zero_or_classical (⟨t, r, n⟩) with h0 | h | h | h | h | h | h
    · omega
    all_goals exact of_decide_eq_true (l937z_zb_C_n hC (by rw [h]; rfl))
  have hr : r < 13 := by
    have h := l937z_zb_rank_le_markRank hlam2
    change r ≤ markRank (⟨t, r, n⟩ : LargeEvenLabel) at h
    omega
  have hn : n < 42 := by
    have h := l937z_zb_n_le_markDeg hlam2
    change n ≤ markDeg (⟨t, r, n⟩ : LargeEvenLabel) at h
    omega
  have hlam2' : l937z_zb_lam2 (⟨t, r, n⟩ : LargeEvenLabel) = true :=
    (l937z_zb_lam2_iff _).mpr hlam2
  exact (l937z_zb_inSq_iff _).mp
    (l937z_zb_box t (l937z_zb_mem_tags htw) r hr n hn hlam2' hdvd h49)

theorem lieSevenOddCentre7sq_B [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    LieSevenOddCentre7sq (TauCeti.CFSGIndex.sporadic .B).Group := by
  refine lieSevenOddCentre7sq_of_marked (K := (TauCeti.CFSGIndex.sporadic .B).Group)
    (fun G _ hG => lieZRow_of_untwistedChevalleyModel_F4_two hG)
    (fun G _ hG => lieZRow_of_twistedChevalleyModel_E6_two hG)
    (fun G _ hG => lieZRow_of_twistedChevalleyModel_D4_two hG) ?_
  intro L hLs hmark
  obtain ⟨lab, hlab, hM, hcard, -⟩ := mem_rows42_of_marked hLs hmark
  exact ⟨lab, hM, hcard, sevenSq_of_rows42 lab hlab⟩

end CFSG.StandardType.SporadicShape
