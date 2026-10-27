module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Perm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Good
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38M3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Ten
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16h_chione_noncyclic_of_pRank {H : Subgroup G} {q : ℕ} (hq : q.Prime)
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

private theorem s16h_chione_subgroupOf_commutator_self {X : Type*} [Group X] (H : Subgroup X) :
    (⁅H, H⁆).subgroupOf H = ⁅(⊤ : Subgroup ↥H), ⊤⁆ := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← Subgroup.map_subtype_commutator H, ← _root_.commutator_def,
    Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem s16h_halfRank_le_pRank_of_bar (D : Data G) (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D)
    (h111 : F11.R111 D) (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h127 : R127 D)
    {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))}
    (hXn : ∀ q ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    (hXe : IsElemAbelian p X)
    (hXd : X ≤ ⁅Mbar D.M V₀ V h.hyp125.isElemAbelian, Mbar D.M V₀ V h.hyp125.isElemAbelian⁆)
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card ↥X = p ^ n) :
    n / 2 + 1 ≤ CFSG.Open.pRank p D.M := by
  let hV := h.hyp125.isElemAbelian
  have hXM : X ≤ Mbar D.M V₀ V hV := hXd.trans (Subgroup.commutator_le_self _)
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  haveI hCTilde : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal hV hMs
  obtain ⟨e, -⟩ := s15_Three_barImage_equiv hV hMs
  set Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    (X.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom with hXbar
  have hNnorm : (X.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    refine ⟨fun x hx q => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      hXn (q : MulAut (Vtil V₀ V hV)) q.2 (x : MulAut (Vtil V₀ V hV)) hx
  have hXnorm : Xbar.Normal := by
    rw [hXbar]
    exact hNnorm.map e.symm.toMonoidHom e.symm.surjective
  have hXab : IsElemAbelian p Xbar := by
    rw [hXbar]
    exact (hXe.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom
  have hcardX : Nat.card ↥Xbar = p ^ n := by
    rw [hXbar, Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hcard]
  have hcomm_le : X.subgroupOf (Mbar D.M V₀ V hV) ≤
      (⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf (Mbar D.M V₀ V hV) :=
    fun x hx => hXd (Subgroup.mem_subgroupOf.1 hx)
  have hcommmap : ((⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf
        (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom =
      ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [s16h_chione_subgroupOf_commutator_self, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.symm.surjective]
  have hXc : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [hXbar]
    exact le_trans (Subgroup.map_mono hcomm_le) (le_of_eq hcommmap)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥(F11.O2p p D.M)) := inferInstance
  have hP : CFSG.ABGLocalTools.IsSylowOf p
      ((Q : Subgroup ↥(F11.O2p p D.M)).map (F11.O2p p D.M).subtype) (F11.O2p p D.M) :=
    ⟨Q, rfl⟩
  obtain ⟨-, -, h3⟩ := r1110Core_holds D hSig h61 h63 h77 h869 h111 h112 hThin hCyc V₀ V
    (Hyp125.hyp11 h127 h.hyp125) p hp hp2 _ hP
  obtain ⟨-, -, -, hrk⟩ := h3 n hn Xbar hXnorm hXab hcardX hXc
  refine hrk.trans (CFSG.SectionRank.pRank_mono hp.one_lt ?_)
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  exact Subgroup.commutator_le_self _ hx.1.1.2

theorem s16h_condU_of_chiOne (D : Data G) (hx : DataExt D) (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D)
    (h111 : F11.R111 D) (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h127 : R127 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpσ : p ∉ D.sig) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hU : Nat.card ↥(wTil V₀ V h.hyp151.isElemAbelian L) = p + 1)
    (hχ : ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n)
    (hs : 3 ≤ s15 D.M V₀ V h.hyp151.isElemAbelian L) :
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
    by_contra hcon
    exact hpσ (s16c34_mem_sig_of_four_le D hSig hp hp2 (by omega))
  have hs6 : s15 D.M V₀ V hV L ≤ 6 := by omega
  obtain ⟨q, hq⟩ := hx.sig_nonempty
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
  have hdiv : s15 D.M V₀ V hV L / q ≤ 2 := Nat.div_le_of_le_mul (by omega)
  have hq4 := hx.four_le h4 q hq
  have hadd := r38m3_pRank_le_add hV hP hqp.1
  have hCt : 2 ≤ CFSG.Open.pRank q (F11.CTilde D.M V₀ V) := by omega
  obtain ⟨E, hEC, hEp, hEnc⟩ := s16h_chione_noncyclic_of_pRank hqp.1 hCt
  intro x hxM w hw hw0
  have hwV : w ∈ V := preTil_le V₀ V hV _ hw
  exact s16c34_uniqueMax_cent_of_cElt D h61 h127 h.hyp16 hq hEp hEnc hwV hw0
    (hEC.trans (iInf₂_le w hwV))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
