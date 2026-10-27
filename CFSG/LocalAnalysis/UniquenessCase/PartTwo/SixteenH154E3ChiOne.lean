module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ChiOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16h_chione_noncyclic_of_pRank_e3 {H : Subgroup G} {q : ℕ} (hq : q.Prime)
    (h2 : 2 ≤ CFSG.Open.pRank q H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsPGroup q E ∧ ¬ IsCyclic ↥E := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hq.one_lt H
  have hEp : IsPGroup q E := CFSG.Open.IsElemAbelian.isPGroup hE
  refine ⟨E, hEH, hEp, fun hcyc => ?_⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ q :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  rw [hg, hEc] at h1
  have h3 : q ^ 2 ≤ q ^ CFSG.Open.pRank q H := Nat.pow_le_pow_right hq.pos h2
  have h4 : q < q ^ 2 := by nlinarith [hq.one_lt]
  have := Nat.le_of_dvd hq.pos h1
  omega

theorem s16h_condU_of_chiOne_e3 (D : Data G) (hx : DataExt D) (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D)
    (h111 : F11.R111 D) (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h127 : R127 D)
    (hr3 : CFSG.Open.evenRank G = 3) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpσ : p ∉ D.sig) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hU : Nat.card ↥(wTil V₀ V h.hyp151.isElemAbelian L) = p + 1)
    (hχ : ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n)
    (hs : 3 ≤ s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hgood : ∃ q ∈ D.sig, q ≠ 3 ∨ s15 D.M V₀ V h.hyp151.isElemAbelian L ≠ 6) :
    s16h_CondU D V₀ V L h.hyp151.isElemAbelian := by
  have hV := h.hyp151.isElemAbelian
  have hP : PairFacts D.M V₀ V := h.hyp16.hyp125.pairFacts
  obtain ⟨t, -, -, -, -, hW⟩ := hc
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.hyp151.le
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hLp.2]
    exact hp.odd_of_ne_two hp2
  have hfix : commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) = ⊥ :=
    s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd
  obtain ⟨X, n, hXd, hXn, hXe, hXc, hsn⟩ := s16h_closure_inf_commutator hp hLp.2 hLM
    (fun q hq q' hq' hne => (s16h_conj_comm_inf_of_conc hW hq hq' hne).1)
    (s16h_sSupIndep_conj_of_conc hW)
  have hsn' : s15 D.M V₀ V hV L - 1 ≤ n := hsn
  have hn : 1 < n := by omega
  have hr := s16h_halfRank_le_pRank_of_bar D hSig h61 h63 h77 h869 h111 h112 hThin hCyc h127
    h.hyp16 hp hp2 hXn hXe hXd hn hXc
  have h3 : CFSG.Open.pRank p D.M < 4 := by
    have := s16h_pRank_le_evenRank D hp hp2
    omega
  have hs6 : s15 D.M V₀ V hV L ≤ 6 := by omega
  obtain ⟨q, hq, hqgood⟩ := hgood
  have hqp := D.sig_prime q hq
  have hqne : q ≠ p := fun e => hpσ (e ▸ hq)
  have hq3 : 3 ≤ q := by
    have h2 := hqp.1.two_le
    have h5 := hqp.2
    omega
  have hker : ∀ k ∈ Mbar D.M V₀ V hV, (∀ g ∈ Mbar D.M V₀ V hV, k ∈ normalizer
        (((lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom : Subgroup _) : Set _)) →
      (∃ m : ℕ, k ^ (q ^ m) = 1) → k = 1 := by
    rintro k hk hkN ⟨m, hkm⟩
    exact s16h_eq_one_of_normalizes_conj hW.1 hp hLp hU hfix hχ hk hkN
      (((Nat.coprime_primes hqp.1 hp).2 hqne).pow_left m) hkm
  have hrq : CFSG.Open.pRank q (Mbar D.M V₀ V hV) ≤ s15 D.M V₀ V hV L / q :=
    s16h_pRank_le_ncard_div hqp.1 hker
  have hdiv : s15 D.M V₀ V hV L / q ≤ 1 := by
    have hlt : s15 D.M V₀ V hV L < q * 2 := by
      rcases hqgood with h3q | h6
      · have h5 : 5 ≤ q := by
          have h2 := hqp.1.two_le
          have hq2' := hqp.2
          by_contra hlt
          have : q < 5 := by omega
          interval_cases q
          · exact h3q rfl
          · exact absurd hqp.1 (by norm_num)
        omega
      · omega
    have := Nat.div_lt_of_lt_mul hlt
    omega
  have hq3' := hx.three_le q hq
  have hadd := r38m3_pRank_le_add hV hP hqp.1
  have hCt : 2 ≤ CFSG.Open.pRank q (F11.CTilde D.M V₀ V) := by omega
  obtain ⟨E, hEC, hEp, hEnc⟩ := s16h_chione_noncyclic_of_pRank_e3 hqp.1 hCt
  intro x hxM w hw hw0
  have hwV : w ∈ V := preTil_le V₀ V hV _ hw
  exact s16c34_uniqueMax_cent_of_cElt D h61 h127 h.hyp16 hq hEp hEnc hwV hw0
    (hEC.trans (iInf₂_le w hwV))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
