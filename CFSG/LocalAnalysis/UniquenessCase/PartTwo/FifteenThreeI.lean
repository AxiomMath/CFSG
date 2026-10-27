module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeI1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeIE
import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Three_card_alt_five {X : Type} [Group X] (h : UC22.IsAlt X 5) : Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem s15_Three_prime_dvd_168 {q : ℕ} (hq : q.Prime) (h : q ∣ 168) : q = 2 ∨ q = 3 ∨ q = 7 := by
  have hle : q ≤ 168 := Nat.le_of_dvd (by norm_num) h
  interval_cases q <;> first | omega | exact absurd hq (by norm_num)

theorem s15_Three_prime_dvd_60 {q : ℕ} (hq : q.Prime) (h : q ∣ 60) : q = 2 ∨ q = 3 ∨ q = 5 := by
  have hle : q ≤ 60 := Nat.le_of_dvd (by norm_num) h
  interval_cases q <;> first | omega | exact absurd hq (by norm_num)

section Big

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

theorem s15_Three_one_le_rs (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L K₀ : Subgroup G) : 1 ≤ s15Rs D V₀ V hV L K₀ := by
  unfold s15Rs s15
  have hK : barSub V₀ V hV K₀ ∈ conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) :=
    ⟨1, Subgroup.one_mem _, by ext x; simp⟩
  have hL : barSub V₀ V hV L ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
    ⟨1, Subgroup.one_mem _, by ext x; simp⟩
  exact Nat.mul_pos ((Set.ncard_pos (Set.toFinite _)).2 ⟨_, hK⟩)
    ((Set.ncard_pos (Set.toFinite _)).2 ⟨_, hL⟩)

theorem s15_Three_K_two (h82 : F08.R82 D) (h880 : F08.R880 D) (hRk : RRank3List153)
    (hCov : RCover3Rank153) (hSchur : RSchur153) (hIso : RIso153) (hNotJ2 : RNotJ2)
    (hV : IsElemAbelian 2 V) {K : Subgroup G} (hK : s15Covers D V₀ V hV K₀ K)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5 := by
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barSub V₀ V hV K₀)) ≤ 2 := by
    by_contra h
    exact hns (s15_Three_strong_rank h82 hCov hK hperf.shape (by omega))
  rcases (hRk _ _ _ _ hperf).1 h2 with h3 | h4 | h5 | h5a | h6 | h7 | h8
  · exact Or.inl h3
  · exact absurd (s15_Three_strong_alt h880 hSchur hIso hNotJ2 hK
      (Or.inr (Or.inr (Or.inl h4)))) hns
  · exact absurd (s15_Three_strong_alt h880 hSchur hIso hNotJ2 hK
      (Or.inr (Or.inr (Or.inr h5)))) hns
  · exact Or.inr h5a
  · exact absurd (s15_Three_strong_alt h880 hSchur hIso hNotJ2 hK (Or.inl h6)) hns
  · exact absurd (s15_Three_strong_alt h880 hSchur hIso hNotJ2 hK (Or.inr (Or.inl h7))) hns
  · exact absurd (s15_Three_strong_alt h880 hSchur hIso hNotJ2 hK
      (Or.inr (Or.inr (Or.inl ((hIso _).2 h8))))) hns

theorem s15_Three_sig_sub_pi (hgap : S15ThreeSigSubPiGap D) (hx : DataExt D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h82 : F08.R82 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : s15Rs D V₀ V hV L K₀ = 2) (hsig : D.sig ⊆ D.sig1)
    (hSg : UC6S846.SigmaStd D) (h3 : 3 ∉ D.sig)
    (hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    ∀ q ∈ D.sig, q ∣ Nat.card ↥(barSub V₀ V hV K₀) := by
  intro q hq
  by_cases hdvd : q ∣ Nat.card ↥(barSub V₀ V hV K₀)
  · exact hdvd
  · obtain ⟨R, E, hRsyl, hEZ, hEel, hEcard, hqrank⟩ :=
      s15_Three_sig_sub_pi_core hgap hx h614 h76 h82 h hV hshape hperf hL2 hrs hsig hSg h3 hns
        hq hdvd
    have hqprime : q.Prime := (D.sig_prime q hq).1
    have hq2 : q ≠ 2 := (D.sig_prime q hq).2
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M := hSg.sig1_sp q (hsig hq)
    have hEM : E ≤ D.M := fun x hxE => hRsyl.le (hEZ hxE).1
    have hqC : 0 < CFSG.Open.pRank q (D.M ⊓ centralizer (E : Set G)) := by omega
    have hqN : ∀ X : Subgroup G, X ≤ E → Nat.card X = 3 →
        1 < CFSG.Open.pRank q (D.M ⊓ normalizer (X : Set G)) := by
      intro X hXE _
      have hCE : D.M ⊓ centralizer (E : Set G) ≤ D.M ⊓ normalizer (X : Set G) :=
        inf_le_inf_left _ ((Subgroup.centralizer_le hXE).trans
          (Subgroup.centralizer_le_normalizer _))
      have := CFSG.SectionRank.pRank_mono hqprime.one_lt hCE
      omega
    have hG : rankThreeGamma 1 3 E ≤ D.M :=
      h76 q hq hq2 hsp 3 Nat.prime_three E hEM hEel hEcard hqC hqN
    exact absurd (h614 hsig 3 Nat.prime_three (by norm_num) h3 R hRsyl E hEZ hEel hEcard hG) hns

theorem s15_Three_rank_le_three (hgap : S15ThreeRankLeThreeGap D) (hx : DataExt D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h77 : F07.R77E2 D) (h82 : F08.R82 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : s15Rs D V₀ V hV L K₀ = 2) (hsig : D.sig ⊆ D.sig1)
    (hSg : UC6S846.SigmaStd D) (h3 : 3 ∉ D.sig)
    (hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    ∀ q ∈ D.sig, CFSG.Open.pRank q D.M ≤ 3 := by
  intro q hq
  by_contra hlt
  have h4 : 4 ≤ CFSG.Open.pRank q D.M := by omega
  obtain ⟨R, E, hRsyl, hEZ, hEel, hEcard, hG⟩ :=
    s15_Three_rank_le_three_core hgap hx h614 h76 h82 h hV hshape hperf hL2 hrs hsig hSg h3 hns
      hq h4 h77
  exact hns (h614 hsig 3 Nat.prime_three (by norm_num) h3 R hRsyl E hEZ hEel hEcard hG)

theorem s15_Three_sig_big (hgapSig : S15ThreeSigSubPiGap D) (hgapRank : S15ThreeRankLeThreeGap D)
    (hx : DataExt D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h77 : F07.R77E2 D)
    (h82 : F08.R82 D) (h127 : R127 D) (h1111 : R1111_153 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : s15Rs D V₀ V hV L K₀ = 2) (hsig : D.sig ⊆ D.sig1) (hSg : UC6S846.SigmaStd D)
    (hne : D.sig.Nonempty) (h3 : 3 ∉ D.sig)
    (hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    ∃ p : ℕ, ((p = 5 ∧ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5) ∨
        (p = 7 ∧ IsL3 ↥(barSub V₀ V hV K₀) 1)) ∧
      D.sig = {p} ∧ CFSG.Open.pRank p D.M = 3 := by
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have hdvd := s15_Three_sig_sub_pi hgapSig hx h614 h76 h82 h hV hshape hperf hL2 hrs hsig hSg h3
    hns
  have hle3 := s15_Three_rank_le_three hgapRank hx h614 h76 h77 h82 h hV hshape hperf hL2 hrs hsig
    hSg h3 hns
  have hq2 : ∀ r ∈ D.sig, r ≠ 2 := fun r hr => (D.sig_prime r hr).2
  have hq3 : ∀ r ∈ D.sig, r ≠ 3 := fun r hr h3' => h3 (h3' ▸ hr)
  have hrk3 : ∀ r ∈ D.sig, CFSG.Open.pRank r D.M = 3 := by
    intro r hr
    have := (h1111 V₀ V hH11 r hr).2
    have := hle3 r hr
    omega
  obtain ⟨q, hq⟩ := hne
  rcases hL2 with hL3' | hA5'
  · have hr7 : ∀ r ∈ D.sig, r = 7 := by
      intro r hr
      have hd := hdvd r hr
      rw [WeakClosure81.card_eq_of_isL3 hL3'] at hd
      rcases s15_Three_prime_dvd_168 (D.sig_prime r hr).1 hd with h | h | h
      · exact absurd h (hq2 r hr)
      · exact absurd h (hq3 r hr)
      · exact h
    refine ⟨7, Or.inr ⟨rfl, hL3'⟩, ?_, ?_⟩
    · ext r
      simp only [Set.mem_singleton_iff]
      exact ⟨hr7 r, fun hr => by rw [hr]; exact (hr7 q hq) ▸ hq⟩
    · exact hrk3 7 ((hr7 q hq) ▸ hq)
  · have hr5 : ∀ r ∈ D.sig, r = 5 := by
      intro r hr
      have hd := hdvd r hr
      rw [s15_Three_card_alt_five hA5'] at hd
      rcases s15_Three_prime_dvd_60 (D.sig_prime r hr).1 hd with h | h | h
      · exact absurd h (hq2 r hr)
      · exact absurd h (hq3 r hr)
      · exact h
    refine ⟨5, Or.inl ⟨rfl, hA5'⟩, ?_, ?_⟩
    · ext r
      simp only [Set.mem_singleton_iff]
      exact ⟨hr5 r, fun hr => by rw [hr]; exact (hr5 q hq) ▸ hq⟩
    · exact hrk3 5 ((hr5 q hq) ▸ hq)

theorem s15_Three_case_two_big (hgapSig : S15ThreeSigSubPiGap D)
    (hgapRank : S15ThreeRankLeThreeGap D) (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h77 : F07.R77E2 D) (hSimple : RSimple153)
    (hS2 : RSchur2_153) (h127 : R127 D) (h119 : F11.R119 D)
    (h1217 : R1217 D) (h82 : F08.R82 D)
    (h880 : F08.R880 D) (h1111 : R1111_153 D) (hRk : RRank3List153) (hCov : RCover3Rank153)
    (hSchur : RSchur153) (hIso : RIso153) (hNotJ2 : RNotJ2) (hPerfT : RPerfType153)
    (hsig : D.sig ⊆ D.sig1) (hSg : UC6S846.SigmaStd D) (hne : D.sig.Nonempty)
    (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hO1 : s15O1a D V) (hbig : ¬ (s15Rs D V₀ V hV L K₀ = 1 ∧ s15ExcList ↥(lBar V₀ V hV L))) :
    Case153_2 D V₀ V hV L := by
  obtain ⟨hns, h3⟩ := s15_Three_unique_of_O1a h61 h63 h127 h.hyp125 hO1
  obtain ⟨K, hK⟩ := s15_Three_cover_K hSimple h127 h119 h1217 h hV hshape hperf
  have hL2 := s15_Three_K_two h82 h880 hRk hCov hSchur hIso hNotJ2 hV hK hperf hns
  have hle2 := s15_Three_rs_le_two h82 hS2 hSimple h127 h119 h1217 h hV hshape hperf hL2 hns
  have hrs1 : s15Rs D V₀ V hV L K₀ ≠ 1 := by
    intro hrs
    have hLK := s15_Three_lBar_eq hshape hrs
    apply hbig
    refine ⟨hrs, ?_⟩
    rw [hLK]
    rcases hL2 with h3' | h5'
    · exact Or.inl h3'
    · exact Or.inr (Or.inr (Or.inl h5'))
  have hge := s15_Three_one_le_rs D V₀ V hV L K₀
  have hrs2 : s15Rs D V₀ V hV L K₀ = 2 := by omega
  obtain ⟨p, hp, hsigp, hrk⟩ :=
    s15_Three_sig_big hgapSig hgapRank hx h614 h76 h77 h82 h127 h1111 h hV hshape hperf hL2 hrs2
      hsig hSg hne h3 hns
  refine s15_Three_case_two_of p hshape.1 ?_ hshape.2.2.1 hsigp hrk hle2 (fun h1 => absurd h1 hrs1)
  rcases hp with ⟨rfl, hA5⟩ | ⟨rfl, hL3⟩
  · exact Or.inl ⟨rfl, hA5, (hPerfT _ _ _ _ hperf).2.1 hA5⟩
  · exact Or.inr ⟨rfl, hL3, (hPerfT _ _ _ _ hperf).1 hL3⟩

end Big

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
