module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeD2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeD3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section CaseOne

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

private theorem s15_Three_pRank_le_add {M N : Subgroup G} (hNM : N ≤ M)
    [(N.subgroupOf M).Normal] {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p N +
      CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ N.subgroupOf M)) := by
  have h1 := GL83.I713.pRank_top_le_add_pRank_quotient (G := ↥M) hp (N.subgroupOf M)
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup M] at h1
  have h2 : CFSG.Open.pRank p (N.subgroupOf M) = CFSG.Open.pRank p N := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank p (N.subgroupOf M),
      CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNM) p,
      CFSG.SectionRank.pRank_coe_eq_openPRank p N]
  rwa [h2] at h1

private theorem s15_Three_pRank_le_of_relIndex {H K : Subgroup G} (hKH : K ≤ H) {n : ℕ}
    (h : K.relIndex H = 2 ^ n) : CFSG.Open.pRank 3 H ≤ CFSG.Open.pRank 3 K := by
  have hnot : ¬ 3 ∣ (K.subgroupOf H).index := by
    rw [show (K.subgroupOf H).index = K.relIndex H from rfl, h]
    intro hd
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have h1 := CFSG.SectionRank.pRank_top_le_of_not_dvd_index Nat.prime_three (K.subgroupOf H) hnot
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H] at h1
  have h2 : CFSG.Open.pRank 3 (K.subgroupOf H) = CFSG.Open.pRank 3 K := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 (K.subgroupOf H),
      CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH) 3,
      CFSG.SectionRank.pRank_coe_eq_openPRank 3 K]
  rwa [h2] at h1

private theorem s15_Three_R113_apply (h : Hyp151 D V₀ V L) (h127 : R127 D) (hV0 : mSub V₀ ≤ 2)
    {v : G} (hv : v ∈ V) (hv0 : v ∉ V₀) : ∃ n ≤ 2,
      (D.M ⊓ centralizer ({v} : Set G)).relIndex (F11.CElt D.M V₀ v) = 2 ^ n := by
  have hcard : Nat.card V₀ ≤ 4 := by
    rw [card_eq_two_pow_mSub h.hyp125.pairFacts.elemAbelian₀.isPGroup]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hV0
      _ = 4 := by norm_num
  exact r113_holds D V₀ V (Hyp125.hyp11 h127 h.hyp125) hcard v hv hv0

private theorem s15_Three_pRank_centralizer_eq (h : Hyp151 D V₀ V L) (h127 : R127 D)
    (hV0 : mSub V₀ ≤ 2) {v : G} (hv : v ∈ V) (hv0 : v ∉ V₀) :
    CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) =
      CFSG.Open.pRank 3 (F11.CElt D.M V₀ v) := by
  obtain ⟨n, -, hrel⟩ := s15_Three_R113_apply h h127 hV0 hv hv0
  have hKH : D.M ⊓ centralizer ({v} : Set G) ≤ F11.CElt D.M V₀ v := by
    intro m hm
    obtain ⟨hmM, hmC⟩ := Subgroup.mem_inf.1 hm
    refine ⟨hmM, h.hyp125.pairFacts.le_normalizer₀ hmM, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hmC
    have h1 : m * v * m⁻¹ * v⁻¹ = 1 := by rw [hmC]; group
    rw [h1]
    exact V₀.one_mem
  exact le_antisymm (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hKH)
    (s15_Three_pRank_le_of_relIndex hKH hrel)

private theorem s15_Three_rank_bounds (hAut : RAutRank153) (hAbs : RAbsIrr153) (h127 : R127 D)
    (h115 : F11.R115 D) (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL4 : s15ListFour ↥(lBar V₀ V hV L)) (hsig : D.sig = {3}) (hV0 : mSub V₀ ≤ 2) :
    3 ≤ CFSG.Open.pRank 3 D.M ∧ CFSG.Open.pRank 3 D.M ≤ 4 ∧
      CFSG.Open.pRank 3 D.M - 1 ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) ∧
      CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) ≤ 1 := by
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have hcard : Nat.card V₀ ≤ 4 := by
    rw [card_eq_two_pow_mSub hpf.elemAbelian₀.isPGroup]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hV0
      _ = 4 := by norm_num
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  obtain ⟨hC, hle, hge⟩ := h115 V₀ V hH11 hcard 3 h3
  have hle' : CFSG.Open.pRank 3 D.M - 1 ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := hle
  have h1 := s15_Three_pRank_MBar11 (D := D) hV hMs 3
  have h2 := (s15_Three_rank_ListFour hAut hAbs D h1217 h hV hL hs hperf hL4).2.1
  have hle2 : CFSG.Open.pRank 3 D.M - 1 ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) := by
    rw [← h1]; exact hle'
  exact ⟨by omega, by omega, hle2, hC⟩

private theorem s15_Three_O1a_of_V0 (h : Hyp151 D V₀ V L) (h127 : R127 D) (hV0 : mSub V₀ ≤ 2)
    (h3M : 3 ≤ CFSG.Open.pRank 3 D.M) {v : G} (hv : v ∈ V₀) (hv1 : v ≠ 1) :
    1 < CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
  have hcard : Nat.card V₀ ≤ 4 := by
    rw [card_eq_two_pow_mSub h.hyp125.pairFacts.elemAbelian₀.isPGroup]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hV0
      _ = 4 := by norm_num
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) D.M
  have hDMleE : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.pRank 3 E :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := E) le_rfl hE hEcard
  haveI : IsMulCommutative ↥E := hE.1
  have hcyc : IsCyclic (↥E ⧸ (E ⊓ centralizer (V₀ : Set G)).subgroupOf E) :=
    ElevenFourteen.isCyclic_quotient_of_card_le_four Nat.prime_three (by norm_num)
      hE.isPGroup (hEM.trans h.hyp125.pairFacts.le_normalizer₀) hcard
  have hquot : CFSG.Open.pRank 3
      (⊤ : Subgroup (↥E ⧸ (E ⊓ centralizer (V₀ : Set G)).subgroupOf E)) ≤ 1 :=
    CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three
      (Subgroup.topEquiv.isCyclic.2 hcyc)
  have hadd := s15_Three_pRank_le_add (M := E) (N := E ⊓ centralizer (V₀ : Set G))
    inf_le_left (p := 3) Nat.prime_three
  have h2 : 2 ≤ CFSG.Open.pRank 3 (E ⊓ centralizer (V₀ : Set G)) := by omega
  have hle : E ⊓ centralizer (V₀ : Set G) ≤ D.M ⊓ centralizer ({v} : Set G) := by
    refine le_inf (inf_le_left.trans hEM) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2) v hv).symm
  exact lt_of_lt_of_le (by norm_num : 1 < 2)
    (h2.trans (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle))

theorem s15_Three_k_one (h82 : F08.R82 D) (h880 : F08.R880 D) (hCov : RCover3Rank153)
    (hOm : RRank3Omega153) (hSchur : RSchur153) (hIso : RIso153) (hNotJ2 : RNotJ2)
    (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hrs : s15Rs D V₀ V hV L K₀ = 1) {K : Subgroup G} (hK : s15Covers D V₀ V hV K₀ K)
    (hL4 : s15ListFour ↥(lBar V₀ V hV L)) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  have hLK := s15_Three_lBar_eq hshape hrs
  rw [hLK] at hL4
  rcases hL4 with hΩ | h6 | h7 | h4
  · exact s15_Three_strong_omega h82 hCov hOm hK hΩ
  · exact s15_Three_strong_alt h880 hSchur hIso hNotJ2 hK (Or.inl h6)
  · exact s15_Three_strong_alt h880 hSchur hIso hNotJ2 hK (Or.inr (Or.inl h7))
  · exact s15_Three_strong_alt h880 hSchur hIso hNotJ2 hK (Or.inr (Or.inr (Or.inl h4)))

theorem s15_Three_sig_three (hAut : RAutRank153) (hAbs : RAbsIrr153) (h127 : R127 D)
    (h115 : F11.R115 D) (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL4 : s15ListFour ↥(lBar V₀ V hV L)) (hne : D.sig.Nonempty) (hV0 : mSub V₀ ≤ 2) :
    D.sig = {3} := by
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have hcard : Nat.card V₀ ≤ 4 := by
    rw [card_eq_two_pow_mSub hpf.elemAbelian₀.isPGroup]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hV0
      _ = 4 := by norm_num
  have key : ∀ p ∈ D.sig, p = 3 := by
    intro p hp
    by_contra hp3
    obtain ⟨-, hle, hge⟩ := h115 V₀ V hH11 hcard p hp
    have hle' : CFSG.Open.pRank p D.M - 1 ≤
        CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := hle
    have h1 := s15_Three_pRank_MBar11 (D := D) hV hMs p
    have h2 := (s15_Three_rank_ListFour hAut hAbs D h1217 h hV hL hs hperf hL4).1 p
      (D.sig_prime p hp).1 (D.sig_prime p hp).2 hp3
    omega
  obtain ⟨q, hq⟩ := hne
  have hq3 : q = 3 := key q hq
  subst hq3
  ext p
  simp only [Set.mem_singleton_iff]
  exact ⟨key p, fun hp => hp ▸ hq⟩

theorem s15_Three_rank_three (hAut : RAutRank153) (hAbs : RAbsIrr153) (hT : RTable137)
    (hTor : RTorus3_153) (h127 : R127 D) (h115 : F11.R115 D) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1) (hsig : D.sig = {3}) (hV0 : mSub V₀ ≤ 2)
    (hnot : ¬ s15O1a D V) : CFSG.Open.pRank 3 D.M = 3 := by
  have hL4 : s15ListFour ↥(lBar V₀ V hV L) := Or.inl hΩ
  have hrk := s15_Three_rank_bounds hAut hAbs h127 h115 h1217 h hV hL hs hperf hL4 hsig hV0
  by_contra hne
  have h4 : CFSG.Open.pRank 3 D.M = 4 := by omega
  exact s15_Three_rank_three_core hT hAbs hTor h1217 h127 h115 h hV hL hs hperf hΩ hsig hV0 hnot h4

theorem s15_Three_O1a_of_alt (hAut : RAutRank153) (hAbs : RAbsIrr153) (hT : RTable137)
    (hTor : RTorus3_153) (h127 : R127 D) (h115 : F11.R115 D) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7 ∨
      IsLn ↥(lBar V₀ V hV L) 4 1)
    (hsig : D.sig = {3}) (hV0 : mSub V₀ ≤ 2) : s15O1a D V := by
  have hL4 : s15ListFour ↥(lBar V₀ V hV L) := Or.inr hA
  have hrk := s15_Three_rank_bounds hAut hAbs h127 h115 h1217 h hV hL hs hperf hL4 hsig hV0
  have hcore := s15_Three_O1a_of_alt_core h hV hL hs hperf hA hsig hV0 hT hAbs hTor h1217
    ⟨hrk.1, hrk.2.2.1, hrk.2.2.2⟩
  intro v hv hv1
  by_cases hv0 : v ∈ V₀
  · exact s15_Three_O1a_of_V0 h h127 hV0 hrk.1 hv0 hv1
  · rw [s15_Three_pRank_centralizer_eq h h127 hV0 hv hv0]
    exact hcore v hv hv0

end CaseOne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
