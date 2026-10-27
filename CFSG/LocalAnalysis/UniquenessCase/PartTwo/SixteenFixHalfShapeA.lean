module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16fh_sq_dvd_card_of_two_le_pRank {X : Type} [Group X] [Finite X]
    {q : ℕ} (hq : q.Prime) {H : Subgroup X} (hr : 2 ≤ CFSG.Open.pRank q H) :
    q ^ 2 ∣ Nat.card H := by
  obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt H
  have hdiv : q ^ 2 ∣ q ^ CFSG.Open.pRank q H := pow_dvd_pow q hr
  rw [← hEcard] at hdiv
  exact hdiv.trans (Subgroup.card_dvd_of_le hE)

private theorem s16fh_not_sq_dvd_sixty {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ 60 := by
  intro h
  have hle : q ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h
  have hq3 : 3 ≤ q := Nat.succ_le_of_lt (lt_of_le_of_ne hq.two_le (Ne.symm hq2))
  have hq7 : q ≤ 7 := by
    have hlt : q ^ 2 < 8 ^ 2 := lt_of_le_of_lt hle (by norm_num)
    have hq8 : q < 8 := lt_of_pow_lt_pow_left' 2 hlt
    omega
  interval_cases q <;> norm_num at h

private theorem s16fh_not_sq_dvd_168 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ 168 := by
  intro h
  have hle : q ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h
  have hq3 : 3 ≤ q := Nat.succ_le_of_lt (lt_of_le_of_ne hq.two_le (Ne.symm hq2))
  have hq12 : q ≤ 12 := by
    have hlt : q ^ 2 < 13 ^ 2 := lt_of_le_of_lt hle (by norm_num)
    have hq13 : q < 13 := lt_of_pow_lt_pow_left' 2 hlt
    omega
  interval_cases q <;> norm_num at h

private theorem s16fh_card_alt_five {X : Type} [Group X] {H : Subgroup X}
    (h : IsAlt ↥H 5) : Nat.card H = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

private theorem s16fh_pRank_le_one_of_isAlt_five {X : Type} [Group X] [Finite X]
    {H : Subgroup X} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h : IsAlt ↥H 5) :
    CFSG.Open.pRank q H ≤ 1 := by
  by_contra hlt
  have hr : 2 ≤ CFSG.Open.pRank q H := by omega
  exact s16fh_not_sq_dvd_sixty hq hq2
    (s16fh_card_alt_five h ▸ s16fh_sq_dvd_card_of_two_le_pRank hq hr)

private theorem s16fh_pRank_le_one_of_isL3 {X : Type} [Group X] [Finite X]
    {H : Subgroup X} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h : IsL3 ↥H 1) :
    CFSG.Open.pRank q H ≤ 1 := by
  by_contra hlt
  have hr : 2 ≤ CFSG.Open.pRank q H := by omega
  exact s16fh_not_sq_dvd_168 hq hq2
    (card_eq_of_isL3 h ▸ s16fh_sq_dvd_card_of_two_le_pRank hq hr)

private theorem s16fh_pRank_le_one_of_isL2 {X : Type} [Group X] [Finite X]
    {H : Subgroup X} {f q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h : IsL2 ↥H f) :
    CFSG.Open.pRank q H ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
  exact pRank_le_one_of_isL2_or_isSz (Or.inl h) hq hq2

private theorem s16fh_pRank_le_one_of_isOmegaMinus_four {X : Type} [Group X] [Finite X]
    {H : Subgroup X} {k q : ℕ} (hk : 1 ≤ k) (hq : q.Prime) (hq2 : q ≠ 2)
    (h : IsOmegaMinus ↥H 4 k) : CFSG.Open.pRank q H ≤ 1 :=
  s16fh_pRank_le_one_of_isL2 hq hq2 (S18.isL2_of_isOmegaMinus_four hk h)

private theorem s16fh_nontrivial_of_isQuasisimple {X : Type} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : Nontrivial X := by
  haveI := h.2
  exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial

private theorem s16fh_not_isNilpotent_of_isQuasisimple {X : Type} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : ¬ Group.IsNilpotent X := by
  haveI : Nontrivial X := s16fh_nontrivial_of_isQuasisimple h
  haveI : Group.IsPerfect X := Group.isPerfect_def.mpr h.1
  exact Group.IsPerfect.not_isNilpotent (G := X)

private theorem s16fh_false_of_isPGroup {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hQ : CFSG.Open.IsQuasisimple X) (h : IsPGroup p X) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact s16fh_not_isNilpotent_of_isQuasisimple hQ h.isNilpotent

private theorem s16fh_false_of_isPOnePlusTwo {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hQ : CFSG.Open.IsQuasisimple X) (h : IsPOnePlusTwo p X) : False :=
  s16fh_false_of_isPGroup hp hQ (IsPGroup.of_card (n := 3) h.2.1)

private theorem s16fh_false_of_isCyclicOrd {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : n.Prime) (hQ : CFSG.Open.IsQuasisimple X) (h : IsCyclicOrd X n) : False :=
  s16fh_false_of_isPGroup hn hQ (IsPGroup.of_card (n := 1) (by rw [h.2, pow_one]))

private theorem s16fh_isMulCommutative_of_isElemAbelianOfRank {X : Type} [Group X]
    {p n : ℕ} (h : IsElemAbelianOfRank p n X) : IsMulCommutative X := by
  obtain ⟨e⟩ := h
  exact IsMulCommutative.of_comm fun a b =>
    e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s16fh_false_of_isElemAbelianOfRank {X : Type} [Group X]
    (hQ : CFSG.Open.IsQuasisimple X) {p n : ℕ} (h : IsElemAbelianOfRank p n X) : False := by
  haveI : IsMulCommutative X := s16fh_isMulCommutative_of_isElemAbelianOfRank h
  exact s16fh_not_isNilpotent_of_isQuasisimple hQ (inferInstance : Group.IsNilpotent X)

theorem s16fh_nonthin_alt_concl162 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hs : 1 < s15 D.M V₀ V hV L)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hr : 2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    (h : Concl162 D V₀ V hV L) :
    ∃ n : ℕ, 6 ≤ n ∧ n ≤ 8 ∧ UC22.IsAlt ↥(lBar V₀ V hV L) n ∧
      SumOfNat (fun H U Z => AlternatingNatural H U Z n) (lStar D.M V₀ V hV L)
        (wStar D.M V₀ V hV L) ⊥ 2 := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have h' : Desc153 D V₀ V hV L ∨ Case162_1 D V₀ V hV L ∨ Case162_2 D V₀ V hV L ∨
      Case162_3 D V₀ V hV L ∨ Case162_4 D V₀ V hV L ∨ Case162_5 D V₀ V hV L ∨
      Case162_6 D V₀ V hV L ∨ Case162_7 D V₀ V hV L ∨ Case162_8 D V₀ V hV L ∨
      Case162_9 D V₀ V hV L := h
  rcases h' with h | h | h | h | h | h | h | h | h | h
  ·
    have h'' : Case153_1 D V₀ V hV L ∨ Case153_2 D V₀ V hV L ∨ Case153_3 D V₀ V hV L := h
    rcases h'' with h | h | h
    ·
      obtain ⟨-, -, -, -, hs1, -⟩ := h
      exfalso
      omega
    ·
      obtain ⟨K₀, p, -, hshape, hdirect, -, -, hrs, -⟩ := h
      set K : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV K₀ with hKdef
      set N : Subgroup (MulAut (Vtil V₀ V hV)) :=
        Mbar D.M V₀ V hV ⊓
          normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set _) with hNdef
      have hKmem : K ∈ conjSet K N := s15_T7_mem_conjSet_self K N
      have hpos : 0 < (conjSet K N).ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨K, hKmem⟩
      have hr1 : (conjSet K N).ncard ≤ 1 := by
        by_contra hlt
        have h2 : 2 ≤ (conjSet K N).ncard := by omega
        have h2s : 2 * s15 D.M V₀ V hV L ≤ (conjSet K N).ncard * s15 D.M V₀ V hV L :=
          Nat.mul_le_mul_right _ h2
        omega
      have hone : (conjSet K N).ncard = 1 := by omega
      have hXeq : lBar V₀ V hV L = K := s15_T7_eq_of_ncard_one hdirect hone
      rcases hshape with ⟨-, hAlt5, -⟩ | ⟨-, hL3, -⟩
      · exfalso
        have hle : CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1 := by
          rw [hXeq]
          exact s16fh_pRank_le_one_of_isAlt_five hq hq2 hAlt5
        omega
      · exfalso
        have hle : CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1 := by
          rw [hXeq]
          exact s16fh_pRank_le_one_of_isL3 hq hq2 hL3
        omega
    ·
      obtain ⟨⟨K₀, -, hcyc, hdir, -⟩, -⟩ := h
      exfalso
      have hKabel : IsElemAbelian 3 (barSub V₀ V hV K₀) :=
        s15_T7_isElemAbelian_of_cyclicOrd hcyc
      have hXabel : IsElemAbelian 3 (lBar V₀ V hV L) :=
        s15_T7_isElemAbelian_of_directProd hKabel hdir
      haveI : IsMulCommutative ↥(lBar V₀ V hV L) := hXabel.1
      exact s16fh_not_isNilpotent_of_isQuasisimple hcomp.2.2
        (inferInstance : Group.IsNilpotent ↥(lBar V₀ V hV L))
  ·
    obtain ⟨hshape, -⟩ := h
    rcases hshape with ⟨n, hn5, hn8, hAlt, hsum⟩ | ⟨hL3, -⟩
    · by_cases hn : n = 5
      · exfalso
        have hAlt5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5 := hn ▸ hAlt
        have hle : CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1 :=
          s16fh_pRank_le_one_of_isAlt_five hq hq2 hAlt5
        omega
      · exact ⟨n, by omega, hn8, hAlt, hsum⟩
    · exfalso
      have hle : CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1 :=
        s16fh_pRank_le_one_of_isL3 hq hq2 hL3
      omega
  ·
    obtain ⟨hs1, -⟩ := h
    exfalso
    omega
  ·
    exfalso
    exact s16fh_false_of_isCyclicOrd Nat.prime_five hcomp.2.2 h.1
  ·
    exfalso
    exact s16fh_false_of_isPOnePlusTwo Nat.prime_three hcomp.2.2 h.1
  ·
    obtain ⟨⟨r, hrk, -⟩, -⟩ := h
    exfalso
    exact s16fh_false_of_isElemAbelianOfRank hcomp.2.2 hrk
  ·
    obtain ⟨-, -, hs1, -, -⟩ := h
    exfalso
    omega
  ·
    obtain ⟨-, -, hs1⟩ := h
    exfalso
    omega
  ·
    obtain ⟨hshape, -⟩ := h
    exfalso
    rcases hshape with ⟨hL2, -⟩ | ⟨hOm, -⟩
    · have hle : CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1 :=
        s16fh_pRank_le_one_of_isL2 hq hq2 hL2
      omega
    · have hle : CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1 :=
        s16fh_pRank_le_one_of_isOmegaMinus_four (by norm_num) hq hq2 hOm
      omega
  ·
    obtain ⟨-, -, hs1, -, -⟩ := h
    exfalso
    omega
end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
