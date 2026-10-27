module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMRed
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Search
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLieFast

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.EvenSmallLie.CatalogOrders

@[expose] def bmAutBnd (t : StatedLieTag) (n q : ℕ) : ℕ :=
  let f := Nat.log2 q
  match t with
  | .PSL => if n == 2 then lieOrd t n q * f else lieOrd t n q * (2 * f * Nat.gcd n (q - 1))
  | .PSU => lieOrd t n q * (2 * f * Nat.gcd n (q + 1))
  | .PSp => if n == 2 then bmGlOrd 4 q * f else lieOrd t n q * f
  | .POmegaPlus =>
      if n == 4 then (if q == 2 then 3 * lieOrd t n q else 0) else bmGlOrd (2 * n) q * f
  | .POmegaMinus => bmGlOrd (2 * n) q * f
  | .G2 => if q == 4 then lieOrd t n q * 2 else 0
  | .F4 => if q == 2 then lieOrd t n q * 2 else 0
  | .trialityD4 => if q == 2 then lieOrd t n q * 3 else 0
  | .twistedE6 => if q == 2 then lieOrd t n q * 18 else 0
  | .twistedB2 => if q == 8 || q == 32 then lieOrd t n q * f else 0
  | _ => 0

@[expose] def bmAutExcl (t : StatedLieTag) (n q : ℕ) : Bool :=
  (t == .PSL && n == 2 && q == 2) || (t == .PSU && n == 3 && q == 2) ||
    (t == .PSp && n == 2 && q == 2) || (t == .G2 && q == 2) || t == .POmegaOdd

@[expose] def bmAutOk (p k A : ℕ) : Bool := A % p ^ k != 0

theorem ordBM_search_B :
    lieSearch [2] 4154781481226426191177580544000000 (fun t n q _ =>
      bmAutExcl t n q || (bmAutOk 3 13 (bmAutBnd t n q) && bmAutOk 5 6 (bmAutBnd t n q))) = true :=
  CFSG.EvenSmallLie.CatalogOrders.lieSearch_of_lieSearchB (L := 111) (by decide +kernel)

theorem ordBM_search_M :
    lieSearch [2] 808017424794512875886459904961710757005754368000000000 (fun t n q _ =>
      bmAutExcl t n q || (bmAutOk 3 20 (bmAutBnd t n q) && bmAutOk 5 9 (bmAutBnd t n q) &&
        bmAutOk 7 6 (bmAutBnd t n q) && bmAutOk 13 3 (bmAutBnd t n q))) = true :=
  CFSG.EvenSmallLie.CatalogOrders.lieSearch_of_lieSearchB (L := 179) (by decide +kernel)

theorem bmLieSearch_mono {ps : List ℕ} {N : ℕ}
    {C C' : StatedLieTag → ℕ → ℕ → ℕ → Bool}
    (h : ∀ t n q o, C t n q o = true → C' t n q o = true) (hS : lieSearch ps N C = true) :
    lieSearch ps N C' = true := by
  unfold lieSearch at hS ⊢
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hS ⊢
  intro p hp f hf t ht n hn
  rcases hS p hp f hf t ht n hn with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (h _ _ _ _ h1)

private theorem lre6bsa_lieMin_markTag_le_markRank {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) : lieMin (markTag lab) ≤ markRank lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;> simp only [markTag, markRank]
  all_goals first | (split_ifs <;> simp only [lieMin] <;> omega) | (simp only [lieMin]; omega)

private theorem lre6bsa_markRank_zero_or_classical (lab : LargeEvenLabel) :
    markRank lab = 0 ∨ markTag lab = .PSL ∨ markTag lab = .PSU ∨ markTag lab = .PSp ∨
      markTag lab = .POmegaOdd ∨ markTag lab = .POmegaPlus ∨ markTag lab = .POmegaMinus := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, markRank]
  all_goals first | (split_ifs <;> simp) | simp

private theorem lre6bsa_markRank_le_lieExp_add_one {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) :
    markRank lab ≤ lieExp (markTag lab) (markRank lab) + 1 :=
  le_lieExp_add_one (lre6bsa_lieMin_markTag_le_markRank hl) (lre6bsa_markRank_zero_or_classical lab)

private theorem lre6bsa_one_le_markDeg {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) :
    1 ≤ markDeg lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;> simp only [markDeg]
  all_goals first | (split_ifs <;> omega) | omega

private theorem lre6bsa_lieAdm_markTag {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) :
    lieAdm (markTag lab) (markChar lab) (markDeg lab) = true := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;>
    simp only [lieAdm, markTag, markChar, markDeg]
  case twB2 =>
    obtain ⟨-, -, hodd, h3⟩ := hl
    rw [Nat.odd_iff] at hodd
    simp [hodd, h3]
  all_goals first | rfl | (split_ifs <;> rfl)

private theorem lre6bsa_labOrd_eq_lieOrd_of_markTag_mem {lab : LargeEvenLabel}
    (ht : markTag lab ∈ searchTags) :
    labOrd lab = lieOrd (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [labOrd, markTag, markRank, markChar, markDeg]
  all_goals first | rfl |
    (exact absurd ht (by simp only [markTag, searchTags]; decide))

theorem ordBM_search_label {N : ℕ} (hN : N ≠ 0) {C : StatedLieTag → ℕ → ℕ → ℕ → Bool}
    (hS : lieSearch [2] N C = true) {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hchar : markChar lab = 2) (ht : markTag lab ∈ searchTags) (hd : labOrd lab ∣ N) :
    C (markTag lab) (markRank lab) (2 ^ markDeg lab)
      (lieOrd (markTag lab) (markRank lab) (2 ^ markDeg lab)) = true := by
  have hmin : lieMin (markTag lab) ≤ markRank lab := lre6bsa_lieMin_markTag_le_markRank hl
  have hle : markRank lab ≤ lieExp (markTag lab) (markRank lab) + 1 :=
    lre6bsa_markRank_le_lieExp_add_one hl
  have hadm : lieAdm (markTag lab) 2 (markDeg lab) = true := by
    rw [← hchar]
    exact lre6bsa_lieAdm_markTag hl
  have hf : 1 ≤ markDeg lab := lre6bsa_one_le_markDeg hl
  have hlabOrd : labOrd lab = lieOrd (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) :=
    lre6bsa_labOrd_eq_lieOrd_of_markTag_mem ht
  have hd' : lieOrd (markTag lab) (markRank lab) (2 ^ markDeg lab) ∣ N := by
    rw [← hchar, ← hlabOrd]
    exact hd
  exact lr2o_lieSearch_sound_mem (ps := [2]) (N := N)
    (C := C) (t := markTag lab) (n := markRank lab) (p := 2) (f := markDeg lab)
    hN hS ht (by norm_num) (by decide) hf hmin hle hadm hd'

private theorem lre6bsb_factorization_of {N p k m : ℕ} (hN : N = p ^ k * m)
    (hm : ¬ p ∣ m) (hp : p.Prime) : N.factorization p = k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  rw [hN, Nat.factorization_def (p ^ k * m) hp,
    padicValNat.mul (pow_ne_zero k hp.ne_zero) hm0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]

private theorem lre6bsb_labOrd_twF4_eq {lab : LargeEvenLabel} (h : lab.tag = .twF4) :
    labOrd lab = CFSG.Open.ordTwistedF4 (2 ^ lab.n) := by
  obtain ⟨t, l, n⟩ := lab
  subst h
  rfl

private theorem lre6bsb_twF4_facts {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (h : lab.tag = .twF4) : 3 ≤ lab.n ∧ Odd lab.n := by
  obtain ⟨t, l, n⟩ := lab
  subst h
  simp only [LargeEvenInLambda2] at hl
  exact ⟨hl.2.2.2, hl.2.2.1⟩

private theorem lre6bsb_pow_dvd_ordTwistedF4 (q : ℕ) : q ^ 12 ∣ CFSG.Open.ordTwistedF4 q := by
  unfold CFSG.Open.ordTwistedF4
  simp only [mul_assoc]
  exact dvd_mul_right _ _

theorem ordBM_twF4_B (lab : LargeEvenLabel) (hl : LargeEvenInLambda2 lab) (h : lab.tag = .twF4) :
    ¬ labOrd lab ∣ 4154781481226426191177580544000000 := by
  intro hdvd
  obtain ⟨hn3, _hodd⟩ := lre6bsb_twF4_facts hl h
  have hld : labOrd lab = CFSG.Open.ordTwistedF4 (2 ^ lab.n) := lre6bsb_labOrd_twF4_eq h
  rw [hld] at hdvd
  have h2dvd : 2 ^ (12 * lab.n) ∣ 4154781481226426191177580544000000 := by
    have hq : (2 ^ lab.n) ^ 12 = 2 ^ (12 * lab.n) := by rw [← pow_mul, mul_comm]
    have h := lre6bsb_pow_dvd_ordTwistedF4 (2 ^ lab.n)
    rw [hq] at h
    exact h.trans hdvd
  have h42 : ¬ 2 ^ 42 ∣ 4154781481226426191177580544000000 := by decide +kernel
  have hbound : 12 * lab.n ≤ 41 := by
    by_contra hlt
    exact h42 (dvd_trans (Nat.pow_dvd_pow 2 (by omega : 42 ≤ 12 * lab.n)) h2dvd)
  have hn_eq : lab.n = 3 := by omega
  have h37 : 37 ∣ CFSG.Open.ordTwistedF4 (2 ^ lab.n) := by
    rw [hn_eq]
    decide +kernel
  have h37N : ¬ 37 ∣ 4154781481226426191177580544000000 := by decide +kernel
  exact h37N (dvd_trans h37 hdvd)

theorem ordBM_twF4_M (lab : LargeEvenLabel) (hl : LargeEvenInLambda2 lab) (h : lab.tag = .twF4) :
    ¬ labOrd lab ∣ 808017424794512875886459904961710757005754368000000000 := by
  intro hdvd
  obtain ⟨hn3, _hodd⟩ := lre6bsb_twF4_facts hl h
  have hld : labOrd lab = CFSG.Open.ordTwistedF4 (2 ^ lab.n) := lre6bsb_labOrd_twF4_eq h
  rw [hld] at hdvd
  have h2dvd : 2 ^ (12 * lab.n) ∣ 808017424794512875886459904961710757005754368000000000 := by
    have hq : (2 ^ lab.n) ^ 12 = 2 ^ (12 * lab.n) := by rw [← pow_mul, mul_comm]
    have h := lre6bsb_pow_dvd_ordTwistedF4 (2 ^ lab.n)
    rw [hq] at h
    exact h.trans hdvd
  have h47 : ¬ 2 ^ 47 ∣ 808017424794512875886459904961710757005754368000000000 := by decide +kernel
  have hbound : 12 * lab.n ≤ 46 := by
    by_contra hlt
    exact h47 (dvd_trans (Nat.pow_dvd_pow 2 (by omega : 47 ≤ 12 * lab.n)) h2dvd)
  have hn_eq : lab.n = 3 := by omega
  have h37 : 37 ∣ CFSG.Open.ordTwistedF4 (2 ^ lab.n) := by
    rw [hn_eq]
    decide +kernel
  have h37N : ¬ 37 ∣ 808017424794512875886459904961710757005754368000000000 := by decide +kernel
  exact h37N (dvd_trans h37 hdvd)

theorem ordBM_factorization_B_three : (4154781481226426191177580544000000 : ℕ).factorization 3 = 13 :=
  lre6bsb_factorization_of (m := 2605984785533688086528000000)
    (by norm_num) (by norm_num) (by norm_num)
theorem ordBM_factorization_B_five : (4154781481226426191177580544000000 : ℕ).factorization 5 = 6 :=
  lre6bsb_factorization_of (m := 265906014798491276235365154816)
    (by norm_num) (by norm_num) (by norm_num)
theorem ordBM_factorization_M_three : (808017424794512875886459904961710757005754368000000000 : ℕ).factorization 3 = 20 :=
  lre6bsb_factorization_of (m := 231737134238290082302814542435975168000000000)
    (by norm_num) (by norm_num) (by norm_num)
theorem ordBM_factorization_M_five : (808017424794512875886459904961710757005754368000000000 : ℕ).factorization 5 = 9 :=
  lre6bsb_factorization_of (m := 413704921494790592453867471340395907586946236416)
    (by norm_num) (by norm_num) (by norm_num)
theorem ordBM_factorization_M_seven : (808017424794512875886459904961710757005754368000000000 : ℕ).factorization 7 = 6 :=
  lre6bsb_factorization_of (m := 6868034788179354485685895374900855570432000000000)
    (by norm_num) (by norm_num) (by norm_num)
theorem ordBM_factorization_M_thirteen : (808017424794512875886459904961710757005754368000000000 : ℕ).factorization 13 = 3 :=
  lre6bsb_factorization_of (m := 367782168773105542051187940355808264454144000000000)
    (by norm_num) (by norm_num) (by norm_num)

end CFSG.StandardType.SporadicShape
