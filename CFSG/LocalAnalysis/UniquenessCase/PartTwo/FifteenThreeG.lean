module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeC2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeG1
public import CFSG.LocalAnalysis.GL83PartI.I713.Extension

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section CaseTwo

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

theorem s15_Three_case_two_of {hV : IsElemAbelian 2 V} (p : ℕ) (hK₀ : K₀ ≤ L)
    (hK : (p = 5 ∧ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5 ∧
        AlternatingNatural (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
          (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) ⊥ 5) ∨
      (p = 7 ∧ IsL3 ↥(barSub V₀ V hV K₀) 1 ∧
        BinaryNaturalSL (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
          (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) ⊥ 3 1))
    (hprod : IsDirectProdOfConj (lBar V₀ V hV L) (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L))
    (hsig : D.sig = {p}) (hrk : CFSG.Open.pRank p D.M = 3)
    (hrs2 : s15Rs D V₀ V hV L K₀ ≤ 2) (hrs1 : s15Rs D V₀ V hV L K₀ = 1 → 2 < mSub V₀) :
    Case153_2 D V₀ V hV L :=
  ⟨K₀, p, hK₀, hK, hprod, hsig, hrk, hrs2, hrs1⟩

theorem s15_Three_V0_large (hAut : RAutRank153) (hAbs : RAbsIrr153) (h127 : R127 D)
    (h115 : F11.R115 D) (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) (hne : D.sig.Nonempty) : 2 < mSub V₀ := by
  by_contra hV0
  have hV0' : mSub V₀ ≤ 2 := by omega
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have hcard : Nat.card V₀ ≤ 4 := by
    rw [card_eq_two_pow_mSub hpf.elemAbelian₀.isPGroup]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hV0'
      _ = 4 := by norm_num
  obtain ⟨q, hq⟩ := hne
  obtain ⟨-, hle, hge⟩ := h115 V₀ V hH11 hcard q hq
  have hle' : CFSG.Open.pRank q D.M - 1 ≤
      CFSG.Open.pRank q (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := hle
  have h1 := s15_Three_pRank_MBar11 (D := D) hV hMs q
  have h2 := (s15_Three_rank_ListTwo hAut hAbs D h1217 h hV hL hs hperf hL2).1 q
    (D.sig_prime q hq).1 (D.sig_prime q hq).2
  omega

private theorem s15_Three_pRank_le_add {M N : Subgroup G} (hNM : N ≤ M)
    [(N.subgroupOf M).Normal] {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p N +
      CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ N.subgroupOf M)) := by
  have hN : CFSG.Open.pRank p (N.subgroupOf M) = CFSG.Open.pRank p N := by
    calc CFSG.Open.pRank p (N.subgroupOf M)
        = CFSG.Open.pRank p (⊤ : Subgroup ↥(N.subgroupOf M)) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
      _ = CFSG.Open.pRank p (⊤ : Subgroup ↥N) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
            (Subgroup.subgroupOfEquivOfLe hNM)
      _ = CFSG.Open.pRank p N := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup N).symm
  have h1 := GL83.I713.pRank_top_le_add_pRank_quotient (G := ↥M) hp (N.subgroupOf M)
  rw [hN] at h1
  rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup M]

private theorem s15_Three_cTilde_le {D : Data G} {V₀ V : Subgroup G} :
    F11.CTilde D.M V₀ V ≤ D.M := by
  intro x hx
  exact (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx 1) V.one_mem).1

private theorem s15_Three_cyclic_quotient {D : Data G} {V₀ V L : Subgroup G}
    (h61 : UC6.R6_1 D) (h : Hyp151 D V₀ V L) (h127 : R127 D)
    {p : ℕ} (hp : p ∈ D.sig) {X : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p X)
    [((X ⊓ centralizer (V₀ : Set G)).subgroupOf X).Normal] :
    IsCyclic (↥X ⧸ (X ⊓ centralizer (V₀ : Set G)).subgroupOf X) :=
  ElevenFourteen.eleven_four_one_of_sig D h61 (Hyp125.hyp11 h127 h.hyp125) hp hXM hXp

private theorem s15_Three_not_isCyclic_card9 {A : Type*} [Group A] {E : Subgroup A}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 9) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  have h2 : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) h1
  rw [hg, hcard] at h2
  omega

private theorem s15_Three_rank_cTilde {D : Data G} {V₀ V L : Subgroup G}
    (h1111 : R1111_153 D) (hAut : RAutRank153) (hAbs : RAbsIrr153) (h127 : R127 D)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) (h3 : 3 ∈ D.sig) :
    2 ≤ CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) := by
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have h1111' := h1111 V₀ V hH11 3 h3
  have hrank2 := (s15_Three_rank_ListTwo hAut hAbs D h1217 h hV hL hs hperf hL2).1 3
    Nat.prime_three (by norm_num)
  have hMBar := s15_Three_pRank_MBar11 (D := D) hV hMs 3
  have hsplit := s15_Three_pRank_le_add (M := D.M) (N := F11.CTilde D.M V₀ V)
    (s15_Three_cTilde_le (D := D) (V₀ := V₀) (V := V)) (p := 3) Nat.prime_three
  omega

private theorem s15_Three_inf_centralizer_ne_bot {D : Data G} {V₀ V L : Subgroup G}
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (h3 : 3 ∈ D.sig) {E : Subgroup G} (hEM : E ≤ D.M) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2) : E ⊓ centralizer (V₀ : Set G) ≠ ⊥ := by
  intro hbot
  haveI : IsMulCommutative ↥E := hE.1
  have hcyc := s15_Three_cyclic_quotient h61 h h127 h3 hEM hE.isPGroup
  have hbot' : (E ⊓ centralizer (V₀ : Set G)).subgroupOf E = ⊥ := by
    rw [hbot]
    simp
  rw [hbot'] at hcyc
  exact s15_Three_not_isCyclic_card9 hE (by norm_num [hEcard])
    ((QuotientGroup.quotientBot (G := ↥E)).isCyclic.mp hcyc)

private theorem s15_Three_inf_centralizer_le_centralizer {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {E : Subgroup G}
    (hEC : E ≤ F11.CTilde D.M V₀ V) (hE : CFSG.Open.IsElemAbelian 3 E) :
    (E ⊓ centralizer (V₀ : Set G)) ≤ centralizer (V : Set G) := by
  intro e he
  have hpf := h.hyp125.pairFacts
  have heE : e ∈ E := he.1
  have he0 : e ∈ centralizer (V₀ : Set G) := he.2
  rw [Subgroup.mem_centralizer_iff]
  intro v hvV
  have hce : e ∈ F11.CElt D.M V₀ v :=
    (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (hEC heE) v)) hvV
  have hcomm : e * v * e⁻¹ * v⁻¹ ∈ V₀ := hce.2.2
  have hq1 : ∀ w ∈ V₀, e * w * e⁻¹ = w := by
    intro w hw
    have h1 : w * e = e * w := (Subgroup.mem_centralizer_iff.1 he0) w hw
    rw [← h1]
    group
  have hq3 : ∃ n : ℕ, e ^ (3 ^ n) = 1 := ⟨1, by simpa using hE.2 e heE⟩
  have hfix := s15_Three_cocycle_fixes hV hpf.le hq1 hq3 hcomm
  have hev : e * v = v * e := by
    calc e * v = (e * v * e⁻¹) * e := by group
      _ = v * e := by rw [hfix]
  exact hev.symm

private theorem s15_Three_O1a_of_E {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {E : Subgroup G}
    (hEC : E ≤ F11.CTilde D.M V₀ V) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2) (hE0 : E ≤ centralizer (V₀ : Set G)) : s15O1a D V := by
  intro v hvV hv1
  have hpf := h.hyp125.pairFacts
  have hEM : E ≤ D.M := hEC.trans (s15_Three_cTilde_le (D := D) (V₀ := V₀) (V := V))
  have hle : E ≤ D.M ⊓ centralizer ({v} : Set G) := by
    refine le_inf hEM fun e heE => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hce : e ∈ F11.CElt D.M V₀ v :=
      (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (hEC heE) v)) hvV
    have hcomm : e * v * e⁻¹ * v⁻¹ ∈ V₀ := hce.2.2
    have hq1 : ∀ w ∈ V₀, e * w * e⁻¹ = w := by
      intro w hw
      have h1 : w * e = e * w := (Subgroup.mem_centralizer_iff.1 (hE0 heE)) w hw
      rw [← h1]
      group
    have hq3 : ∃ n : ℕ, e ^ (3 ^ n) = 1 := ⟨1, by simpa using hE.2 e heE⟩
    have hfix := s15_Three_cocycle_fixes hV hpf.le hq1 hq3 hcomm
    calc e * v = (e * v * e⁻¹) * e := by group
      _ = v * e := by rw [hfix]
  have := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hle hE hEcard
  omega

theorem s15_Three_not_three_sig (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h127 : R127 D)
    (h1111 : R1111_153 D) (hAut : RAutRank153) (hAbs : RAbsIrr153) (hT : RTable137)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hshape : s15Shape D V₀ V hV L K₀)
    (hrs : s15Rs D V₀ V hV L K₀ = 1) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) (hbig : 2 < mSub V₀) : 3 ∉ D.sig := by
  by_contra h3
  have hO1 : s15O1a D V := by
    obtain ⟨E, hEC, hE, hEcard⟩ :=
      CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank Nat.prime_three
        (k := 2) (s15_Three_rank_cTilde h1111 hAut hAbs h127 h1217 h hV hL hs hperf hL2 h3)
    by_cases hE0 : E ≤ centralizer (V₀ : Set G)
    · exact s15_Three_O1a_of_E h hV hEC hE hEcard hE0
    · exact s15_Three_not_three_sig_core h61 h63 h127 h1111 hAut hAbs hT h1217 h hV hL hshape
        hrs hs hperf hL2 hbig h3 hEC hE hEcard
        (s15_Three_inf_centralizer_ne_bot h61 h127 h hV h3
          (hEC.trans (s15_Three_cTilde_le (D := D) (V₀ := V₀) (V := V))) hE hEcard)
        (s15_Three_inf_centralizer_le_centralizer h hV hEC hE) hE0
  exact (s15_Three_unique_of_O1a h61 h63 h127 h.hyp125 hO1).2 h3

theorem s15_Three_dvd_of_pRank {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) : p ∣ Nat.card X := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup X)
  have hdvd : p ^ CFSG.Open.pRank p (⊤ : Subgroup X) ∣ Nat.card X :=
    hE ▸ Subgroup.card_subgroup_dvd_card E
  exact (dvd_pow_self p (by omega)).trans hdvd

theorem s15_Three_sig_two (hAut : RAutRank153) (hAbs : RAbsIrr153) (h127 : R127 D)
    (h1111 : R1111_153 D) (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) (hne : D.sig.Nonempty) (h3 : 3 ∉ D.sig) :
    ∃ p : ℕ, ((p = 5 ∧ UC22.IsAlt ↥(lBar V₀ V hV L) 5) ∨ (p = 7 ∧ IsL3 ↥(lBar V₀ V hV L) 1)) ∧
      D.sig = {p} ∧ CFSG.Open.pRank p D.M = 3 := by
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  obtain ⟨hr1, hL3, hA5⟩ := s15_Three_rank_ListTwo hAut hAbs D h1217 h hV hL hs hperf hL2
  have key : ∀ r ∈ D.sig, CFSG.Open.pRank r D.M = 3 ∧
      r ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    intro r hr
    obtain ⟨hle, hge⟩ := h1111 V₀ V hH11 r hr
    have h1 := s15_Three_pRank_MBar11 (D := D) hV hMs r
    have h2 := hr1 r (D.sig_prime r hr).1 (D.sig_prime r hr).2
    exact ⟨by omega, s15_Three_dvd_of_pRank (D.sig_prime r hr).1 (by omega)⟩
  have hq2 : ∀ r ∈ D.sig, r ≠ 2 := fun r hr => (D.sig_prime r hr).2
  have hq3 : ∀ r ∈ D.sig, r ≠ 3 := fun r hr h3' => h3 (h3' ▸ hr)
  obtain ⟨q, hq⟩ := hne
  rcases hL2 with hL3' | hA5'
  · have hr7 : ∀ r ∈ D.sig, r = 7 := by
      intro r hr
      rcases hL3 hL3' r (D.sig_prime r hr).1 (key r hr).2 with h | h | h
      · exact absurd h (hq2 r hr)
      · exact absurd h (hq3 r hr)
      · exact h
    refine ⟨7, Or.inr ⟨rfl, hL3'⟩, ?_, ?_⟩
    · ext r
      simp only [Set.mem_singleton_iff]
      exact ⟨hr7 r, fun hr => by rw [hr]; exact (hr7 q hq) ▸ hq⟩
    · exact (hr7 q hq) ▸ (key q hq).1
  · have hr5 : ∀ r ∈ D.sig, r = 5 := by
      intro r hr
      rcases hA5 hA5' r (D.sig_prime r hr).1 (key r hr).2 with h | h | h
      · exact absurd h (hq2 r hr)
      · exact absurd h (hq3 r hr)
      · exact h
    refine ⟨5, Or.inl ⟨rfl, hA5'⟩, ?_, ?_⟩
    · ext r
      simp only [Set.mem_singleton_iff]
      exact ⟨hr5 r, fun hr => by rw [hr]; exact (hr5 q hq) ▸ hq⟩
    · exact (hr5 q hq) ▸ (key q hq).1

theorem s15_Three_case_two_small (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h127 : R127 D)
    (h115 : F11.R115 D) (h1111 : R1111_153 D) (h1217 : R1217 D) (hAut : RAutRank153)
    (hAbs : RAbsIrr153) (hT : RTable137) (hPerfT : RPerfType153) (hne : D.sig.Nonempty)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hshape : s15Shape D V₀ V hV L K₀) (hrs : s15Rs D V₀ V hV L K₀ = 1)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) : Case153_2 D V₀ V hV L := by
  have hs : s15 D.M V₀ V hV L = 1 := ((s15_Three_rs_eq_one_iff D V₀ V hV L K₀).1 hrs).2
  have hperf' := s15_Three_perf_star h1217 h hV hshape hrs hperf
  have hbig := s15_Three_V0_large hAut hAbs h127 h115 h1217 h hV hL hs hperf' hL2 hne
  have h3 := s15_Three_not_three_sig h61 h63 h127 h1111 hAut hAbs hT h1217 h hV hL hshape hrs hs
    hperf' hL2 hbig
  obtain ⟨p, hp, hsig, hrk⟩ :=
    s15_Three_sig_two hAut hAbs h127 h1111 h1217 h hV hL hs hperf' hL2 hne h3
  have hLK := s15_Three_lBar_eq hshape hrs
  refine s15_Three_case_two_of p hshape.1 ?_ hshape.2.2.1 hsig hrk (by rw [hrs]; norm_num)
    (fun _ => hbig)
  rcases hp with ⟨rfl, hA5⟩ | ⟨rfl, hL3⟩
  · rw [hLK] at hA5
    exact Or.inl ⟨rfl, hA5, (hPerfT _ _ _ _ hperf).2.1 hA5⟩
  · rw [hLK] at hL3
    exact Or.inr ⟨rfl, hL3, (hPerfT _ _ _ _ hperf).1 hL3⟩

end CaseTwo

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
