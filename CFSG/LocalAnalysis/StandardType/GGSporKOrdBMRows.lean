module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMLiftRows
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMExc
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMSearch

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.EvenSmallLie.CatalogOrders

private theorem lre6br4_not_dvd {a B p k : ℕ} (hp : p.Prime) (ha : a ≠ 0)
    (hb : a.factorization p ≤ B.factorization p) (hok : bmAutOk p k B = true) :
    ¬ p ^ k ∣ a := by
  have hB : B ≠ 0 := by
    rintro rfl
    simp [bmAutOk] at hok
  intro h
  have hk : k ≤ a.factorization p := (hp.pow_dvd_iff_le_factorization ha).mp h
  have hk' : k ≤ B.factorization p := le_trans hk hb
  have hpk : p ^ k ∣ B := (hp.pow_dvd_iff_le_factorization hB).mpr hk'
  have hmod : B % p ^ k = 0 := Nat.mod_eq_zero_of_dvd hpk
  have hfalse : bmAutOk p k B = false := by simp [bmAutOk, hmod]
  rw [hok] at hfalse
  exact Bool.false_ne_true hfalse.symm

private theorem lre6br4_finish {R : Type} [Group R] [Finite R] {p k B : ℕ}
    (hp : p.Prime) (hok : bmAutOk p k B = true)
    (hbound : (Nat.card (MulAut R)).factorization p ≤ B.factorization p) :
    ¬ p ^ k ∣ Nat.card (MulAut R) :=
  lre6br4_not_dvd hp Nat.card_pos.ne' hbound hok

private theorem lre6br4_lieOrd_PSL_two_even (q : ℕ) (hq : 2 ∣ q) (hq0 : q ≠ 0) :
    lieOrd .PSL 2 q = q * (q ^ 2 - 1) := by
  have hmain : lieOrd .PSL 2 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
    simp only [lieOrd, ordA]
    norm_num
  have hodd : Odd (q - 1) := by
    obtain ⟨k, hk⟩ := hq
    have hk1 : 1 ≤ k := by omega
    rw [hk]
    exact ⟨k - 1, by omega⟩
  have hgcd : Nat.gcd 2 (q - 1) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)
  rw [hmain, hgcd, Nat.div_one]

private theorem lre6br4_not_excl {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) : ¬ bmAutExcl t n (2 ^ f) = true := by
  intro h
  cases t <;>
    simp only [StatedLieAdmissible] at hadm <;>
    simp [bmAutExcl] at h
  · exact hadm.2.2.2.1 (by simp [h.1, h.2])
  · exact hadm.2.2.2 (by simp [h.1, h.2])
  · exact hadm.2.2.2 (by simp [h.1, h.2])
  · exact absurd rfl hadm.2.2.2
  · omega

private theorem lre6br4_search_or {N p k : ℕ} (hN : N ≠ 0)
    (hS : lieSearch [2] N
      (fun t n q _ => bmAutExcl t n q || bmAutOk p k (bmAutBnd t n q)) = true)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hchar : markChar lab = 2)
    (ht : markTag lab ∈ searchTags) (hd : labOrd lab ∣ N) :
    bmAutExcl (markTag lab) (markRank lab) (2 ^ markDeg lab) = true ∨
      bmAutOk p k (bmAutBnd (markTag lab) (markRank lab) (2 ^ markDeg lab)) = true := by
  have h := ordBM_search_label hN hS hlab hchar ht hd
  simpa only [Bool.or_eq_true] using h

theorem ordBMRow_of_search
    {N p k : ℕ} (hN : N ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : lieSearch [2] N (fun t n q _ => bmAutExcl t n q || bmAutOk p k (bmAutBnd t n q)) = true)
    (htw : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twF4 → ¬ labOrd lab ∣ N)
    (hA6 : bmAutOk p k 1440 = true) (hU33 : bmAutOk p k 12096 = true)
    (hTits : bmAutOk p k (2 * CFSG.Open.ordTits) = true) :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → labOrd lab ∣ N → OrdBMRow p k lab := by
  intro lab hlab hd R _ _ hR hmodel hdiv
  obtain ⟨t, l, n⟩ := lab
  cases t
  case twF4 =>
    exact absurd hd (htw ⟨.twF4, l, n⟩ hlab rfl)
  case twF4der =>
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hn1⟩ := hlab.2
    subst hn1
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hbound := ordBMBound_Tits R hR hmodel p hp hp2
    exact lre6br4_finish hp hTits hbound hdiv
  case B2der =>
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hn1⟩ := hlab.2
    subst hn1
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hbound := ordBMBound_PSL_two (p := 3) (f := 2) (by norm_num) (by norm_num)
      R hR hmodel p hp hp2
    have hb : (Nat.card (MulAut R)).factorization p ≤ (1440 : ℕ).factorization p := by
      simpa only [show 3 ^ 2 * ((3 ^ 2) ^ 2 - 1) * 2 = 1440 by norm_num] using hbound
    exact lre6br4_finish hp hA6 hb hdiv
  case G2der =>
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hn1⟩ := hlab.2
    subst hn1
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hBv : lieOrd .PSU 3 (3 ^ 1) * (2 * 1 * Nat.gcd 3 (3 ^ 1 + 1)) = 12096 := by
      decide +kernel
    have hbound := ordBMBound_PSU (n := 3) (p := 3) (f := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) R hR hmodel p hp hp2
    have hb : (Nat.card (MulAut R)).factorization p ≤ (12096 : ℕ).factorization p := by
      simpa only [hBv] using hbound
    exact lre6br4_finish hp hU33 hb hdiv
  case A =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hadm : StatedLieAdmissible .PSL (l + 1) 2 n := hmodel.admissible
    simp only [LargeEvenInLambda2] at hlab
    rcases hC with hexcl | hok
    · exact lre6br4_not_excl hadm hexcl
    · by_cases h2 : l + 1 = 2
      · have hl1 : l = 1 := by omega
        have hn2 : 2 ≤ n := hlab.2.2 hl1
        have hq : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
        have hq0 : 2 ^ n ≠ 0 := by positivity
        have hbm : bmAutBnd .PSL (l + 1) (2 ^ n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) * n := by
          simp only [bmAutBnd, Nat.log2_two_pow]
          rw [if_pos ((beq_iff_eq).mpr h2), h2]
          rw [lre6br4_lieOrd_PSL_two_even (2 ^ n) hq hq0]
        have hmodel2 : LieModel R .PSL 2 2 n := by simpa only [h2] using hmodel
        have hbound0 := ordBMBound_PSL_two (p := 2) (f := n) Nat.prime_two (by omega) R hR hmodel2 p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .PSL (l + 1) (2 ^ n)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
      · have h3 : 3 ≤ l + 1 := by omega
        have hbm : bmAutBnd .PSL (l + 1) (2 ^ n) =
            lieOrd .PSL (l + 1) (2 ^ n) * (2 * n * Nat.gcd (l + 1) (2 ^ n - 1)) := by
          simp only [bmAutBnd, Nat.log2_two_pow]
          rw [if_neg (fun hc => h2 (eq_of_beq hc))]
        have hbound0 := ordBMBound_PSL (n := l + 1) (f := n) h3 hlab.1 R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .PSL (l + 1) (2 ^ n)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
  case twA =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hadm : StatedLieAdmissible .PSU (l + 1) 2 n := hmodel.admissible
    simp only [LargeEvenInLambda2] at hlab
    rcases hC with hexcl | hok
    · exact lre6br4_not_excl hadm hexcl
    · have hbm : bmAutBnd .PSU (l + 1) (2 ^ n) =
          lieOrd .PSU (l + 1) (2 ^ n) * (2 * n * Nat.gcd (l + 1) (2 ^ n + 1)) := by
        simp [bmAutBnd, Nat.log2_two_pow]
      have hbound0 := ordBMBound_PSU (n := l + 1) (p := 2) (f := n) hadm.2.2.1 Nat.prime_two
        hlab.1 hadm.2.2.2 R hR hmodel p hp hp2
      have hb : (Nat.card (MulAut R)).factorization p ≤
          (bmAutBnd .PSU (l + 1) (2 ^ n)).factorization p := by
        rw [hbm]
        exact hbound0
      exact lre6br4_finish hp hok hb hdiv
  case B =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hadm : StatedLieAdmissible .PSp l 2 n := hmodel.admissible
    simp only [LargeEvenInLambda2] at hlab
    rcases hC with hexcl | hok
    · exact lre6br4_not_excl hadm hexcl
    · by_cases hl2 : l = 2
      · have hn2 : 2 ≤ n := hlab.2.2 hl2
        have hbm : bmAutBnd .PSp l (2 ^ n) = bmGlOrd 4 (2 ^ n) * n := by
          simp only [bmAutBnd, Nat.log2_two_pow]
          rw [if_pos ((beq_iff_eq).mpr hl2)]
        have hmodel2 : LieModel R .PSp 2 2 n := by simpa only [hl2] using hmodel
        have hbound0 := ordBMBound_PSp_two (f := n) hn2 R hR hmodel2 p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .PSp l (2 ^ n)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
      · have h3 : 3 ≤ l := by omega
        have hbm : bmAutBnd .PSp l (2 ^ n) = lieOrd .PSp l (2 ^ n) * n := by
          simp only [bmAutBnd, Nat.log2_two_pow]
          rw [if_neg (fun hc => hl2 (eq_of_beq hc))]
        have hbound0 := ordBMBound_PSp (r := l) (f := n) h3 hlab.1 R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .PSp l (2 ^ n)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
  case C =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hadm : StatedLieAdmissible .PSp l 2 n := hmodel.admissible
    simp only [LargeEvenInLambda2] at hlab
    rcases hC with hexcl | hok
    · exact lre6br4_not_excl hadm hexcl
    · by_cases hl2 : l = 2
      · have hn2 : 2 ≤ n := hlab.2.2 hl2
        have hbm : bmAutBnd .PSp l (2 ^ n) = bmGlOrd 4 (2 ^ n) * n := by
          simp only [bmAutBnd, Nat.log2_two_pow]
          rw [if_pos ((beq_iff_eq).mpr hl2)]
        have hmodel2 : LieModel R .PSp 2 2 n := by simpa only [hl2] using hmodel
        have hbound0 := ordBMBound_PSp_two (f := n) hn2 R hR hmodel2 p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .PSp l (2 ^ n)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
      · have h3 : 3 ≤ l := by omega
        have hbm : bmAutBnd .PSp l (2 ^ n) = lieOrd .PSp l (2 ^ n) * n := by
          simp only [bmAutBnd, Nat.log2_two_pow]
          rw [if_neg (fun hc => hl2 (eq_of_beq hc))]
        have hbound0 := ordBMBound_PSp (r := l) (f := n) h3 hlab.1 R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .PSp l (2 ^ n)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
  case D =>
    by_cases h3 : l = 3
    · subst h3
      have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
      simp only [markTag, markRank, markChar, markDeg, if_true, if_false] at hC
      simp only [MarkedModel, markTag, markRank, markChar, markDeg, if_true, if_false] at hmodel
      have hadm : StatedLieAdmissible .PSL 4 2 n := hmodel.admissible
      simp only [LargeEvenInLambda2] at hlab
      rcases hC with hexcl | hok
      · exact lre6br4_not_excl hadm hexcl
      · have hbm : bmAutBnd .PSL 4 (2 ^ n) =
            lieOrd .PSL 4 (2 ^ n) * (2 * n * Nat.gcd 4 (2 ^ n - 1)) := by
          simp only [bmAutBnd, Nat.log2_two_pow]
          rw [if_neg (by decide : ¬ ((4 == 2) = true))]
        have hbound0 := ordBMBound_PSL (n := 4) (f := n) (by norm_num) hlab.1 R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .PSL 4 (2 ^ n)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
    · have htag : markTag ⟨.D, l, n⟩ = .POmegaPlus := by
        simp only [markTag]
        rw [if_neg h3]
      have hrank : markRank ⟨.D, l, n⟩ = l := by
        simp only [markRank]
        rw [if_neg h3]
      have hdeg : markDeg ⟨.D, l, n⟩ = n := rfl
      have hC := lre6br4_search_or hN hS hlab (by rfl) (by rw [htag]; simp [searchTags]) hd
      simp only [htag, hrank, hdeg, markChar] at hC
      simp only [MarkedModel, htag, hrank, hdeg, markChar] at hmodel
      have hadm : StatedLieAdmissible .POmegaPlus l 2 n := hmodel.admissible
      simp only [LargeEvenInLambda2] at hlab
      rcases hC with hexcl | hok
      · exact lre6br4_not_excl hadm hexcl
      · by_cases h4 : l = 4
        · subst h4
          by_cases hn1 : n = 1
          · subst hn1
            have hbm : bmAutBnd .POmegaPlus 4 (2 ^ 1) = 3 * lieOrd .POmegaPlus 4 2 := by
              simp only [bmAutBnd, Nat.log2_two_pow]
              rw [if_pos (by decide : ((4 == 4) = true))]
              rw [if_pos (by decide : (((2 : ℕ) ^ 1 == 2) = true))]
              norm_num
            have hbound0 := ordBMBound_D4_two R hR hmodel p hp hp2
            have hb : (Nat.card (MulAut R)).factorization p ≤
                (bmAutBnd .POmegaPlus 4 (2 ^ 1)).factorization p := by
              rw [hbm]
              exact hbound0
            exact lre6br4_finish hp hok hb hdiv
          · have hne : 2 ^ n ≠ 2 := by
              intro hc
              exact hn1 (Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hc))
            have hbm : bmAutBnd .POmegaPlus 4 (2 ^ n) = 0 := by
              simp only [bmAutBnd, Nat.log2_two_pow]
              rw [if_pos (by decide : ((4 == 4) = true))]
              rw [if_neg (fun hc => hne (eq_of_beq hc))]
            rw [hbm] at hok
            simp [bmAutOk] at hok
        · have h5 : 5 ≤ l := by omega
          have hbm : bmAutBnd .POmegaPlus l (2 ^ n) = bmGlOrd (2 * l) (2 ^ n) * n := by
            simp only [bmAutBnd, Nat.log2_two_pow]
            rw [if_neg (fun hc => h4 (eq_of_beq hc))]
          have hbound0 := ordBMBound_POmegaPlus (n := l) (f := n) h5 hlab.1 R hR hmodel p hp hp2
          have hb : (Nat.card (MulAut R)).factorization p ≤
              (bmAutBnd .POmegaPlus l (2 ^ n)).factorization p := by
            rw [hbm]
            exact hbound0
          exact lre6br4_finish hp hok hb hdiv
  case twD =>
    by_cases h2 : l = 2
    · subst h2
      have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
      simp only [markTag, markRank, markChar, markDeg, if_true, if_false] at hC
      simp only [MarkedModel, markTag, markRank, markChar, markDeg, if_true, if_false] at hmodel
      have hadm : StatedLieAdmissible .PSL 2 2 (2 * n) := hmodel.admissible
      simp only [LargeEvenInLambda2] at hlab
      rcases hC with hexcl | hok
      · exact lre6br4_not_excl hadm hexcl
      · have hq : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
        have hq0 : 2 ^ (2 * n) ≠ 0 := by positivity
        have hbm : bmAutBnd .PSL 2 (2 ^ (2 * n)) =
            2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) * (2 * n) := by
          simp only [bmAutBnd, Nat.log2_two_pow]
          rw [if_pos (by decide : ((2 == 2) = true))]
          rw [lre6br4_lieOrd_PSL_two_even (2 ^ (2 * n)) hq hq0]
        have hbound0 := ordBMBound_PSL_two (p := 2) (f := 2 * n) Nat.prime_two (by omega)
          R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .PSL 2 (2 ^ (2 * n))).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
    · by_cases h3 : l = 3
      · subst h3
        have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
        simp only [markTag, markRank, markChar, markDeg, if_true, if_false] at hC
        simp only [MarkedModel, markTag, markRank, markChar, markDeg, if_true, if_false] at hmodel
        have hadm : StatedLieAdmissible .PSU 4 2 n := hmodel.admissible
        simp only [LargeEvenInLambda2] at hlab
        rcases hC with hexcl | hok
        · exact lre6br4_not_excl hadm hexcl
        · have hbm : bmAutBnd .PSU 4 (2 ^ n) =
              lieOrd .PSU 4 (2 ^ n) * (2 * n * Nat.gcd 4 (2 ^ n + 1)) := by
            simp [bmAutBnd, Nat.log2_two_pow]
          have hbound0 := ordBMBound_PSU (n := 4) (p := 2) (f := n) (by norm_num) Nat.prime_two
            hlab.1 (by simp) R hR hmodel p hp hp2
          have hb : (Nat.card (MulAut R)).factorization p ≤
              (bmAutBnd .PSU 4 (2 ^ n)).factorization p := by
            rw [hbm]
            exact hbound0
          exact lre6br4_finish hp hok hb hdiv
      · have htag : markTag ⟨.twD, l, n⟩ = .POmegaMinus := by
          simp only [markTag]
          rw [if_neg h2, if_neg h3]
        have hrank : markRank ⟨.twD, l, n⟩ = l := by
          simp only [markRank]
          rw [if_neg h2, if_neg h3]
        have hdeg : markDeg ⟨.twD, l, n⟩ = n := by
          simp only [markDeg]
          rw [if_neg h2]
        have hC := lre6br4_search_or hN hS hlab (by rfl) (by rw [htag]; simp [searchTags]) hd
        simp only [htag, hrank, hdeg, markChar] at hC
        simp only [MarkedModel, htag, hrank, hdeg, markChar] at hmodel
        have hadm : StatedLieAdmissible .POmegaMinus l 2 n := hmodel.admissible
        simp only [LargeEvenInLambda2] at hlab
        rcases hC with hexcl | hok
        · exact lre6br4_not_excl hadm hexcl
        · have hbm : bmAutBnd .POmegaMinus l (2 ^ n) = bmGlOrd (2 * l) (2 ^ n) * n := by
            simp [bmAutBnd, Nat.log2_two_pow]
          have hbound0 := ordBMBound_POmegaMinus (n := l) (f := n) hadm.2.2 hlab.1 R hR hmodel p hp hp2
          have hb : (Nat.card (MulAut R)).factorization p ≤
              (bmAutBnd .POmegaMinus l (2 ^ n)).factorization p := by
            rw [hbm]
            exact hbound0
          exact lre6br4_finish hp hok hb hdiv
  case E6 =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    rcases hC with hexcl | hok
    · simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
      exact lre6br4_not_excl hmodel.admissible hexcl
    · have hbm : bmAutBnd .E6 0 (2 ^ n) = 0 := by simp [bmAutBnd]
      rw [hbm] at hok
      simp [bmAutOk] at hok
  case E7 =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    rcases hC with hexcl | hok
    · simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
      exact lre6br4_not_excl hmodel.admissible hexcl
    · have hbm : bmAutBnd .E7 0 (2 ^ n) = 0 := by simp [bmAutBnd]
      rw [hbm] at hok
      simp [bmAutOk] at hok
  case E8 =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    rcases hC with hexcl | hok
    · simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
      exact lre6br4_not_excl hmodel.admissible hexcl
    · have hbm : bmAutBnd .E8 0 (2 ^ n) = 0 := by simp [bmAutBnd]
      rw [hbm] at hok
      simp [bmAutOk] at hok
  case F4 =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hadm : StatedLieAdmissible .F4 0 2 n := hmodel.admissible
    rcases hC with hexcl | hok
    · exact lre6br4_not_excl hadm hexcl
    · by_cases hn1 : n = 1
      · subst hn1
        have hbm : bmAutBnd .F4 0 (2 ^ 1) = lieOrd .F4 0 2 * 2 := by
          simp only [bmAutBnd]
          rw [if_pos (by decide : (((2 : ℕ) ^ 1 == 2) = true))]
          norm_num
        have hbound0 := ordBMBound_F4_two R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .F4 0 (2 ^ 1)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
      · have hne : 2 ^ n ≠ 2 := by
          intro hc
          exact hn1 (Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hc))
        have hbm : bmAutBnd .F4 0 (2 ^ n) = 0 := by
          simp only [bmAutBnd]
          rw [if_neg (fun hc => hne (eq_of_beq hc))]
        rw [hbm] at hok
        simp [bmAutOk] at hok
  case twE6 =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hadm : StatedLieAdmissible .twistedE6 0 2 n := hmodel.admissible
    rcases hC with hexcl | hok
    · exact lre6br4_not_excl hadm hexcl
    · by_cases hn1 : n = 1
      · subst hn1
        have hbm : bmAutBnd .twistedE6 0 (2 ^ 1) = lieOrd .twistedE6 0 2 * 18 := by
          simp only [bmAutBnd]
          rw [if_pos (by decide : (((2 : ℕ) ^ 1 == 2) = true))]
          norm_num
        have hbound0 := ordBMBound_twistedE6_two R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .twistedE6 0 (2 ^ 1)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
      · have hne : 2 ^ n ≠ 2 := by
          intro hc
          exact hn1 (Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hc))
        have hbm : bmAutBnd .twistedE6 0 (2 ^ n) = 0 := by
          simp only [bmAutBnd]
          rw [if_neg (fun hc => hne (eq_of_beq hc))]
        rw [hbm] at hok
        simp [bmAutOk] at hok
  case triD4 =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hadm : StatedLieAdmissible .trialityD4 0 2 n := hmodel.admissible
    rcases hC with hexcl | hok
    · exact lre6br4_not_excl hadm hexcl
    · by_cases hn1 : n = 1
      · subst hn1
        have hbm : bmAutBnd .trialityD4 0 (2 ^ 1) = lieOrd .trialityD4 0 2 * 3 := by
          simp only [bmAutBnd]
          rw [if_pos (by decide : (((2 : ℕ) ^ 1 == 2) = true))]
          norm_num
        have hbound0 := ordBMBound_trialityD4_two R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .trialityD4 0 (2 ^ 1)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
      · have hne : 2 ^ n ≠ 2 := by
          intro hc
          exact hn1 (Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hc))
        have hbm : bmAutBnd .trialityD4 0 (2 ^ n) = 0 := by
          simp only [bmAutBnd]
          rw [if_neg (fun hc => hne (eq_of_beq hc))]
        rw [hbm] at hok
        simp [bmAutOk] at hok
  case G2 =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hadm : StatedLieAdmissible .G2 0 2 n := hmodel.admissible
    rcases hC with hexcl | hok
    · exact lre6br4_not_excl hadm hexcl
    · by_cases hn2 : n = 2
      · subst hn2
        have hbm : bmAutBnd .G2 0 (2 ^ 2) = lieOrd .G2 0 4 * 2 := by
          simp only [bmAutBnd]
          rw [if_pos (by decide : (((2 : ℕ) ^ 2 == 4) = true))]
          norm_num
        have hbound0 := ordBMBound_G2_four R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .G2 0 (2 ^ 2)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
      · have hne : 2 ^ n ≠ 4 := by
          intro hc
          exact hn2 (Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hc))
        have hbm : bmAutBnd .G2 0 (2 ^ n) = 0 := by
          simp only [bmAutBnd]
          rw [if_neg (fun hc => hne (eq_of_beq hc))]
        rw [hbm] at hok
        simp [bmAutOk] at hok
  case twB2 =>
    have hC := lre6br4_search_or hN hS hlab (by rfl) (by simp [markTag, searchTags]) hd
    simp only [markTag, markRank, markChar, markDeg] at hC
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmodel
    have hadm : StatedLieAdmissible .twistedB2 0 2 n := hmodel.admissible
    rcases hC with hexcl | hok
    · exact lre6br4_not_excl hadm hexcl
    · by_cases hn3 : n = 3
      · subst hn3
        have hbm : bmAutBnd .twistedB2 0 (2 ^ 3) = lieOrd .twistedB2 0 (2 ^ 3) * 3 := by
          simp only [bmAutBnd, Nat.log2_two_pow]
          rw [if_pos (by decide : ((((2 : ℕ) ^ 3 == 8) || ((2 : ℕ) ^ 3 == 32)) = true))]
        have hbound0 := ordBMBound_twistedB2 (f := 3) (Or.inl rfl) R hR hmodel p hp hp2
        have hb : (Nat.card (MulAut R)).factorization p ≤
            (bmAutBnd .twistedB2 0 (2 ^ 3)).factorization p := by
          rw [hbm]
          exact hbound0
        exact lre6br4_finish hp hok hb hdiv
      · by_cases hn5 : n = 5
        · subst hn5
          have hbm : bmAutBnd .twistedB2 0 (2 ^ 5) = lieOrd .twistedB2 0 (2 ^ 5) * 5 := by
            simp only [bmAutBnd, Nat.log2_two_pow]
            rw [if_pos (by decide : ((((2 : ℕ) ^ 5 == 8) || ((2 : ℕ) ^ 5 == 32)) = true))]
          have hbound0 := ordBMBound_twistedB2 (f := 5) (Or.inr rfl) R hR hmodel p hp hp2
          have hb : (Nat.card (MulAut R)).factorization p ≤
              (bmAutBnd .twistedB2 0 (2 ^ 5)).factorization p := by
            rw [hbm]
            exact hbound0
          exact lre6br4_finish hp hok hb hdiv
        · have hne3 : 2 ^ n ≠ 8 := by
            intro hc
            exact hn3 (Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hc))
          have hne5 : 2 ^ n ≠ 32 := by
            intro hc
            exact hn5 (Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hc))
          have hbm : bmAutBnd .twistedB2 0 (2 ^ n) = 0 := by
            simp only [bmAutBnd]
            rw [if_neg]
            · intro hc
              rw [Bool.or_eq_true] at hc
              rcases hc with h8 | h32
              · exact hne3 (eq_of_beq h8)
              · exact hne5 (eq_of_beq h32)
          rw [hbm] at hok
          simp [bmAutOk] at hok

end CFSG.StandardType.SporadicShape
