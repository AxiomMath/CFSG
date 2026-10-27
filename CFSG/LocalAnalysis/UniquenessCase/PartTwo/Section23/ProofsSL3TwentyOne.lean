module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSL3TwentyF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSL3Seventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3Early
public import CFSG.LocalAnalysis.UniquenessCase.UCKSemiregularCommute
public import CFSG.GroupTheory.OddPGroupNoncyclicChar
public import CFSG.GroupTheory.PRankLeNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjointSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3Torus
public import CFSG.LocalAnalysis.UniquenessCase.UCKFixedPointFree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx2311

theorem n_eq_pRank_and_three_le {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h1930 : H1930 D) :
    c.n = CFSG.Open.pRank 2 D.Z ∧ 3 ≤ CFSG.Open.pRank 2 D.Z := by
  have h3n : 3 ≤ c.n :=
    uc22p20g_hn3_of hE D Ch h207 h1930 c.toCtx23L.toCtx23.toCtx21
  rcases h52 h1930 c.toCtx23L with hn | ⟨-, hO, hn2⟩
  · exact ⟨hn, hn ▸ h3n⟩
  · have hm : 1 ≤ CFSG.Open.pRank 2 D.Z := by omega
    exact absurd (isL2_two_mul_of_isOmegaMinus_four hm hO)
      (not_isL2_of_isSLn_three c.hSL3)

theorem isPGroup_E_and_le_M {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) :
    IsPGroup 2 ↥c.E ∧ c.E ≤ D.M ∧ D.M ≤ Subgroup.normalizer (c.E : Set G) := by
  have hN8 := hVK h1930 c
  refine ⟨isPGroup_E c h1930 h4 h12 hN8, ?_, ?_⟩
  · exact (E_le_pCoreOf_M c h1930 h4 h12 hN8).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  · exact uc22p22v_le_normalizer_conjClosure D.M c.V

theorem CME_le_CMETilde {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch) :
    c.CME ≤ c.CMETilde := by
  have hZE : D.Z ≤ c.E :=
    (uc22p22v_le_conjClosure c.N D.Z).trans (uc22p22v_le_conjClosure D.M c.V)
  intro x hx
  rw [Ctx2311.CME, Subgroup.mem_inf] at hx
  obtain ⟨hxM, hxcent⟩ := hx
  rw [Ctx2311.CMETilde, CFSG.Quasithin.mem_centralizerMod]
  refine ⟨hxM, ?_, ?_⟩
  · exact Subgroup.centralizer_le_normalizer (D.Z : Set G)
      ((Subgroup.centralizer_le hZE) hxcent)
  · intro u hu
    have hcomm := (Subgroup.mem_centralizer_iff.1 hxcent) u hu
    have hxu : x * u * x⁻¹ = u := by
      rw [← hcomm]
      group
    rw [hxu]
    simpa using D.Z.one_mem

theorem inf_CME_eq_bot_of_mem_sig {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h201 : S23_20_1 D Ch) (h1930 : H1930 D) {q : ℕ} (hqsig : q ∈ D.sig)
    {Q : Subgroup G} (hQ : IsPGroup q ↥Q) : Q ⊓ c.CME = ⊥ := by
  have hq : q.Prime := (D.sig_prime q hqsig).1
  haveI : Fact q.Prime := ⟨hq⟩
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hxne
  have hQinf : IsPGroup q ↥(Q ⊓ c.CME) := hQ.to_le inf_le_left
  have hxne' : (⟨x, hx⟩ : ↥(Q ⊓ c.CME)) ≠ 1 := fun h => hxne (congrArg Subtype.val h)
  have hdvd : q ∣ Nat.card ↥(Q ⊓ c.CME) :=
    (hQinf.dvd_orderOf hxne').trans (orderOf_dvd_natCard (⟨x, hx⟩ : ↥(Q ⊓ c.CME)))
  have hle : Q ⊓ c.CME ≤ c.CMETilde := inf_le_right.trans c.CME_le_CMETilde
  have hpi : q ∈ piSet c.CMETilde := ⟨hq, hdvd.trans (Subgroup.card_dvd_of_le hle)⟩
  have hmem : q ∈ D.sig ∩ piSet c.CMETilde := ⟨hqsig, hpi⟩
  rw [h201 h1930 c] at hmem
  exact hmem

theorem inf_CME_eq_bot_of_one_lt_pRank {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h202 : S23_20_2F D Ch) (h1930 : H1930 D) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hrk : 1 < CFSG.Open.pRank q (barPreimage D.M (CFSG.pCore q (Bar2 D.M))))
    {Q : Subgroup G} (hQP : Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)))
    (hQ : IsPGroup q ↥Q) : Q ⊓ c.CME = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hxne
  have hQinf : IsPGroup q ↥(Q ⊓ c.CME) := hQ.to_le inf_le_left
  have hxne' : (⟨x, hx⟩ : ↥(Q ⊓ c.CME)) ≠ 1 := fun h => hxne (congrArg Subtype.val h)
  have hdvd : q ∣ Nat.card ↥(Q ⊓ c.CME) :=
    (hQinf.dvd_orderOf hxne').trans (orderOf_dvd_natCard (⟨x, hx⟩ : ↥(Q ⊓ c.CME)))
  have hle : Q ⊓ c.CME ≤ c.CMETilde ⊓ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) :=
    le_inf (inf_le_right.trans c.CME_le_CMETilde) (inf_le_left.trans hQP)
  have hpi : q ∈ piSet (c.CMETilde ⊓ barPreimage D.M (CFSG.pCore q (Bar2 D.M))) :=
    ⟨hq, hdvd.trans (Subgroup.card_dvd_of_le hle)⟩
  exact (h202 h1930 c q hq hq2 hrk) hpi

theorem commute_bar_of_mem_K {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hStepA : S23_9_StepA D Ch) (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {a : G} (ha : a ∈ c.K) (haM : a ∈ D.M) {y : Bar2 D.M}
    (hy : y ∈ CFSG.fittingSubgroup (Bar2 D.M)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩ := by
  have h := hStepA h1930 c.toCtx23L h3
  change ⁅barImage D.M c.K, CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥ at h
  have hbar : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩ ∈ barImage D.M c.K :=
    uc22p21c_mem_barImage.mpr ⟨⟨a, haM⟩, ha, rfl⟩
  have hmem : ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩, y⁆ ∈
      ⁅barImage D.M c.K, CFSG.fittingSubgroup (Bar2 D.M)⁆ :=
    Subgroup.commutator_mem_commutator hbar hy
  rw [h] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)

end Ctx2311

theorem one_lt_pRank_barPreimage_of_not_isCyclic {M : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hnc : ¬ IsCyclic ↥(CFSG.pCore q (Bar2 M))) :
    1 < CFSG.Open.pRank q (barPreimage M (CFSG.pCore q (Bar2 M))) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let P : Subgroup G := barPreimage M (CFSG.pCore q (Bar2 M))
  obtain ⟨Q0, hQ0syl⟩ := CFSG.ABGLocalTools.exists_isSylowOf q P
  have hQ0p : IsPGroup q ↥Q0 := hQ0syl.isPGroup
  have hQ0M : Q0 ≤ M := hQ0syl.le.trans (uc22p21c_barPreimage_le M _)
  obtain ⟨hbar, hO2⟩ := uc22p22u_sylow_barPreimage hq hq2
    (CFSG.pCore_isPGroup (p := q)) hQ0syl
  have hQ0nc : ¬ IsCyclic ↥Q0 :=
    (uc22p22u_lift_props (r := q) hbar hO2 hQ0M).2.2 hnc
  obtain ⟨W, hWQ0, hWne, hWnc, hWexp, -, -⟩ :=
    CFSG.GroupTheory.exists_noncyclic_exponent_classTwo_normalized (p := q) hq2 hQ0p hQ0nc
  have hWp : IsPGroup q ↥W := hQ0p.to_le hWQ0
  obtain ⟨k, hk⟩ := hWp.exists_card_eq
  have hk2 : 2 ≤ k := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with h0 | h1 | h2
    · exfalso
      have hnt : Nontrivial ↥W := Nontrivial.of_not_isCyclic hWnc
      have h1lt : 1 < Nat.card ↥W := Finite.one_lt_card_iff_nontrivial.mpr hnt
      rw [h0, pow_zero] at hk
      omega
    · exfalso
      rw [h1, pow_one] at hk
      exact hWnc (isCyclic_of_prime_card hk)
    · exact h2
  have hcard : q < Nat.card ↥W := by
    rw [hk]
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ k := Nat.pow_lt_pow_right hq.one_lt hk2
  exact CFSG.one_lt_pRank_of_le_of_exp_p hq hWp hWexp hcard (hWQ0.trans hQ0syl.le)

namespace Ctx2311

theorem commute_bar_pCore_of_semiregular {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hE2 : IsPGroup 2 ↥c.E) (hEM : c.E ≤ D.M)
    (hME : D.M ≤ Subgroup.normalizer (c.E : Set G)) (h1930 : H1930 D) {d : G} (hdM : d ∈ D.M)
    {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hdr : orderOf d = r)
    (hdE : c.E ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqr : q ≠ r)
    (hCME : ∀ Q : Subgroup G, Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) →
      IsPGroup q ↥Q → Q ⊓ c.CME = ⊥)
    {y : Bar2 D.M} (hy : y ∈ CFSG.pCore q (Bar2 D.M)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact r.Prime := ⟨hr⟩
  let P : Subgroup G := barPreimage D.M (CFSG.pCore q (Bar2 D.M))
  have hPM : P ≤ D.M := uc22p21c_barPreimage_le D.M _
  have hPnorm : D.M ≤ Subgroup.normalizer (P : Set G) :=
    uc22p22u_barPreimage_normalizes (M := D.M) (D := CFSG.pCore q (Bar2 D.M))
  have hcop : Nat.Coprime r (Nat.card ↥P) :=
    natCard_barPreimage_coprime (CFSG.pCore_isPGroup (p := q)) hr hq hqr.symm hr2
  have hnotdvd : ¬ r ∣ Nat.card ↥P := (Nat.Prime.coprime_iff_not_dvd hr).mp hcop
  let A : Subgroup G := Subgroup.zpowers d
  have hAp : IsPGroup r ↥A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hdr, pow_one])
  have hAK : A ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le.mpr hdM).trans hPnorm
  obtain ⟨Q1, hQ1syl, -, hQ1norm⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime (q := r) (r := q) hr hq
      hAp hAK hnotdvd bot_le IsPGroup.of_bot
      (by
        rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
        exact le_top)
  have hQ1M : Q1 ≤ D.M := hQ1syl.le.trans hPM
  have hbarQ1 : barImage D.M Q1 = CFSG.pCore q (Bar2 D.M) :=
    (uc22p22u_sylow_barPreimage hq hq2 (CFSG.pCore_isPGroup (p := q)) hQ1syl).1
  have hQE : Q1 ⊓ Subgroup.centralizer (c.E : Set G) = ⊥ := by
    have h := hCME Q1 hQ1syl.le hQ1syl.isPGroup
    rw [Ctx2311.CME, ← inf_assoc, inf_eq_left.mpr hQ1M] at h
    exact h
  have hcomm := UCK.commute_of_semiregular_normal_two_of_le hEM hME hE2 hdM hr hr2 hdr
    hdE hq hq2 hqr hQ1M hQ1syl.isPGroup (hQ1norm (Subgroup.mem_zpowers d)) hQE
  have hy' : y ∈ barImage D.M Q1 := by rw [hbarQ1]; exact hy
  obtain ⟨m, hmQ1, hm⟩ := uc22p21c_mem_barImage.mp hy'
  have hm' : (⟨d, hdM⟩ : ↥D.M) * m = m * ⟨d, hdM⟩ := Subtype.ext (hcomm (m : G) hmQ1)
  calc
    QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩ * y =
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨d, hdM⟩ * m) := by
      rw [← hm, ← map_mul]
    _ = QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (m * ⟨d, hdM⟩) := by rw [hm']
    _ = y * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩ := by rw [map_mul, hm]

private theorem commute_bar_pCore_of_factor {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hE2 : IsPGroup 2 ↥c.E) (hEM : c.E ≤ D.M)
    (hME : D.M ≤ Subgroup.normalizer (c.E : Set G)) (hStepA : S23_9_StepA D Ch)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {b d a : G} (hbM : b ∈ D.M)
    (hbd : b = d * a) (haK : a ∈ c.K) (haM : a ∈ D.M) (hdM : d ∈ D.M)
    {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hdr : orderOf d = r)
    (hdE : c.E ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqr : q ≠ r)
    (hCME : ∀ Q : Subgroup G, Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) →
      IsPGroup q ↥Q → Q ⊓ c.CME = ⊥) :
    CFSG.pCore q (Bar2 D.M) ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩} : Set (Bar2 D.M)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have hyF : y ∈ CFSG.fittingSubgroup (Bar2 D.M) := CFSG.pCore_le_fitting (Bar2 D.M) q hy
  have hA := c.commute_bar_of_mem_K hStepA h1930 h3 haK haM hyF
  have hD := c.commute_bar_pCore_of_semiregular hE2 hEM hME h1930 hdM hr hr2 hdr hdE
    hq hq2 hqr hCME hy
  have hb' : (⟨b, hbM⟩ : ↥D.M) = ⟨d, hdM⟩ * ⟨a, haM⟩ := Subtype.ext hbd
  have hbar : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩ := by
    rw [← map_mul, hb']
  calc
    QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩ * y =
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩ * y) := by
      rw [hbar, mul_assoc]
    _ = QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩ *
          (y * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩) := by rw [hA]
    _ = (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩ * y) *
          QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩ := by rw [mul_assoc]
    _ = (y * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩) *
          QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩ := by rw [hD]
    _ = y * (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨d, hdM⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩) := by rw [mul_assoc]
    _ = y * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩ := by rw [hbar]

private theorem exists_semiregular_factor_of_isL2 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch)
    (h53 : S23_5_3 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hL2K : IsL2 (Bar2 c.K) (CFSG.Open.pRank 2 D.Z)) (h17 : S23_17_elt D Ch) :
    ∃ b ∈ c.B0, ∃ d a : G, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ orderOf b = r ∧
      b ∉ Subgroup.centralizer (D.Z : Set G) ∧ b = d * a ∧ a ∈ c.K ∧
      d ∈ D.M ∧ orderOf d = r ∧ c.E ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
  obtain ⟨b, hb, d, a, r, hr, hr2, hr3, hbr, hbZ, hbd, haK, hdML, hdord, hdK⟩ :=
    c.exists_factor_of_mem_B0 hE h207 h52 h53 h4 h1930 h3 hL2K
  have hdL : d ∈ c.L := hdML.2
  have hdM : d ∈ D.M := hdML.1
  have hdodd : Odd (orderOf d) := hdord ▸ hr.odd_of_ne_two hr2
  have hd3 : d ^ 3 ≠ 1 := by
    intro hpow
    have hdvd : orderOf d ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rw [hdord] at hdvd
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp hdvd)
  have hfix := h17 h1930 c d hdL hdodd hd3 hdK
  refine ⟨b, hb, d, a, r, hr, hr2, hr3, hbr, hbZ, hbd, haK, hdM, hdord, ?_⟩
  refine le_antisymm ?_ bot_le
  intro x hx
  have hx' : x ∈ (c.E ⊔ c.S) ⊓ Subgroup.centralizer ({d} : Set G) :=
    ⟨(le_sup_left : c.E ≤ c.E ⊔ c.S) hx.1, hx.2⟩
  rw [hfix] at hx'
  exact Subgroup.mem_bot.mp hx'

theorem pCore_bar_eq_bot_of_mem_sig {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) (h17 : S23_17_elt D Ch)
    (hL2K : IsL2 (Bar2 c.K) (CFSG.Open.pRank 2 D.Z)) (h201 : S23_20_1 D Ch)
    (hStepA : S23_9_StepA D Ch) (h1930 : H1930 D) {q : ℕ} (hqsig : q ∈ D.sig) :
    CFSG.pCore q (Bar2 D.M) = ⊥ := by
  obtain ⟨_, h3⟩ := c.n_eq_pRank_and_three_le hE h207 h52 h1930
  obtain ⟨b, hb, d, a, r, hr, hr2, hr3, hbr, hbZ, hbd, haK, hdM, hdord, hdE⟩ :=
    c.exists_semiregular_factor_of_isL2 hE h207 h52 h53 h4 h1930 h3 hL2K h17
  obtain ⟨hq, hq2⟩ := D.sig_prime q hqsig
  haveI : Fact q.Prime := ⟨hq⟩
  have hbM : b ∈ D.M := c.hBM hb
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have haM : a ∈ D.M := hKM haK
  obtain ⟨hE2, hEM, hME⟩ := c.isPGroup_E_and_le_M h1930 h4 h12 hVK
  let c₀ : Ctx23L D Ch := c.toCtx23L.withB0
  have hb₀ : ((⟨b, hbM⟩ : ↥D.M) : G) ∈ c₀.B := by
    rw [Ctx23L.withB0_B c.toCtx23L]
    exact hb
  have hbar : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩) = r :=
    UCK.orderOf_mk'_pCore_eq_of_prime hr hr2
      ((Subgroup.orderOf_coe ⟨b, hbM⟩).symm.trans hbr)
  by_contra hPne
  have hC := Ctx23L.pCore_inf_centralizer_bar_eq_bot_of_mem_sig c₀ h1930 h54 h6 hb₀ hbZ
    hq hq2 hqsig
  by_cases hqr : q = r
  · have hbnorm : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩ ∈
        Subgroup.normalizer (CFSG.pCore q (Bar2 D.M) : Set (Bar2 D.M)) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal]
      exact Subgroup.mem_top _
    exact (CFSG.GroupTheory.orderOf_ne_of_inf_centralizer_eq_bot
      (hP := CFSG.pCore_isPGroup) hPne hbnorm hC) (hbar.trans hqr.symm)
  · have hCME : ∀ Q : Subgroup G, Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) →
        IsPGroup q ↥Q → Q ⊓ c.CME = ⊥ :=
      fun Q _ hQ => c.inf_CME_eq_bot_of_mem_sig h201 h1930 hqsig hQ
    have hle := c.commute_bar_pCore_of_factor hE2 hEM hME hStepA h1930 h3 hbM hbd haK haM
      hdM hr hr2 hdord hdE hq hq2 hqr hCME
    have hsub : CFSG.pCore q (Bar2 D.M) ≤ CFSG.pCore q (Bar2 D.M) ⊓
        Subgroup.centralizer
          ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩} : Set (Bar2 D.M)) :=
      le_inf le_rfl hle
    rw [hC] at hsub
    exact hPne (le_bot_iff.mp hsub)

private theorem not_isCyclic_pCore_bar_of_noncyclic {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h1930 : H1930 D) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty) (h202 : S23_20_2F D Ch)
    (hStepA : S23_9_StepA D Ch) {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {b d a : G} (hbM : b ∈ D.M) (hbd : b = d * a) (haK : a ∈ c.K) (haM : a ∈ D.M)
    (hdM : d ∈ D.M) (hr : r.Prime) (hr2 : r ≠ 2) (hdord : orderOf d = r)
    (hdE : c.E ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hE2 : IsPGroup 2 ↥c.E) (hEM : c.E ≤ D.M)
    (hME : D.M ≤ Subgroup.normalizer (c.E : Set G)) (c₀ : Ctx23L D Ch)
    (hb₀ : ((⟨b, hbM⟩ : ↥D.M) : G) ∈ c₀.B)
    (hbar : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩) = r)
    (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G))
    (hnc : ¬ IsCyclic ↥(CFSG.pCore q (Bar2 D.M))) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨W, hWle, hWne, hWnc, hWexp, hWcl, hWnorm⟩ :=
    CFSG.GroupTheory.exists_noncyclic_exponent_classTwo_normalized (p := q) hq2
      CFSG.pCore_isPGroup hnc
  have hWq : IsPGroup q ↥W := CFSG.pCore_isPGroup.to_le hWle
  have hWn : W.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_le_iff.mp
      ((Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal).symm.trans_le hWnorm)
  have hrk : 1 < CFSG.Open.pRank q (barPreimage D.M (CFSG.pCore q (Bar2 D.M))) :=
    one_lt_pRank_barPreimage_of_not_isCyclic hq hq2 hnc
  have hCME : ∀ Q : Subgroup G, Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) →
      IsPGroup q ↥Q → Q ⊓ c.CME = ⊥ :=
    fun Q hQ hQp => c.inf_CME_eq_bot_of_one_lt_pRank h202 h1930 hq hq2 hrk hQ hQp
  have hC := Ctx23L.centralizer_bar_inf_eq_bot c₀ h1930 h54 h6 h71 hsig hb₀ hbZ hq hq2
    hWn hWq hWnc hWexp hWcl
  rcases eq_or_ne q r with hqr | hqr
  · have hbnorm : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩ ∈
        Subgroup.normalizer (W : Set (Bar2 D.M)) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hWn]
      exact Subgroup.mem_top _
    exact (CFSG.GroupTheory.orderOf_ne_of_inf_centralizer_eq_bot
      (hP := hWq) hWne hbnorm hC) (hbar.trans hqr.symm)
  · have hle := (c.commute_bar_pCore_of_factor hE2 hEM hME hStepA h1930 h3 hbM hbd haK haM
      hdM hr hr2 hdord hdE hq hq2 hqr hCME)
    have hsub : W ≤ W ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩} : Set (Bar2 D.M)) :=
      le_inf le_rfl (hWle.trans hle)
    rw [hC] at hsub
    exact hWne (le_bot_iff.mp hsub)

theorem isCyclic_pCore_bar {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) (h17 : S23_17_elt D Ch)
    (hL2K : IsL2 (Bar2 c.K) (CFSG.Open.pRank 2 D.Z)) (h202 : S23_20_2F D Ch)
    (hStepA : S23_9_StepA D Ch) (h1930 : H1930 D) {q : ℕ} (hq : q.Prime) :
    IsCyclic ↥(CFSG.pCore q (Bar2 D.M)) := by
  classical
  rcases eq_or_ne q 2 with rfl | hq2
  · have hbot : CFSG.pCore 2 (Bar2 D.M) = ⊥ := by
      simpa [Bar2] using
        (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥D.M) (p := 2))
    rw [hbot]
    infer_instance
  · haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨_, h3⟩ := c.n_eq_pRank_and_three_le hE h207 h52 h1930
    obtain ⟨b, hb, d, a, r, hr, hr2, hr3, hbr, hbZ, hbd, haK, hdM, hdord, hdE⟩ :=
      c.exists_semiregular_factor_of_isL2 hE h207 h52 h53 h4 h1930 h3 hL2K h17
    have hbM : b ∈ D.M := c.hBM hb
    have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
    have haM : a ∈ D.M := hKM haK
    obtain ⟨hE2, hEM, hME⟩ := c.isPGroup_E_and_le_M h1930 h4 h12 hVK
    let c₀ : Ctx23L D Ch := c.toCtx23L.withB0
    have hb₀ : ((⟨b, hbM⟩ : ↥D.M) : G) ∈ c₀.B := by
      rw [Ctx23L.withB0_B c.toCtx23L]
      exact hb
    have hbar : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩) = r :=
      UCK.orderOf_mk'_pCore_eq_of_prime hr hr2
        ((Subgroup.orderOf_coe ⟨b, hbM⟩).symm.trans hbr)
    by_contra hnc
    exact not_isCyclic_pCore_bar_of_noncyclic c h1930 h54 h6 h71 hsig h202 hStepA hq hq2
      hbM hbd haK haM hdM hr hr2 hdord hdE h3 hE2 hEM hME c₀ hb₀ hbar hbZ hnc

end Ctx2311

theorem s23_21_1_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) (h17 : S23_17_elt D Ch)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (hline : S23_5_line D Ch) (hKN : KNshape)
    (hS : KSchurL2) (hS3 : KSchurSL3) (hN1 : S23_9_NotSp4SU4O6m D Ch)
    (hN2 : S23_9_NotO6p D Ch) (hN3 : S23_9_NotLarge D Ch) (hTd : KTab23d)
    (h202 : S23_20_2F D Ch) (hStepA : S23_9_StepA D Ch) : S23_21_1 D Ch := by
  intro h1930 c
  obtain ⟨h3m, hV, hSL, hnatSL, hker⟩ :=
    c.sl3Line_of h1930 hE h207 h2 h3 h4 hline hKN KOrdNat.kOrdNatural_holds hS hS3 hN1 hN2 hN3
  have hL2K := c.isL2_bar2_K h1930 h4 hTd (hV := hV) h3m hSL hnatSL hker
  exact UCK.isCyclic_fittingSubgroup_of_isCyclic_pCore fun q hq =>
    c.isCyclic_pCore_bar hE h207 h52 h53 h54 h6 h71 hsig h4 h12 hVK h17 hL2K h202 hStepA
      h1930 hq

theorem s23_21_2_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch)
    (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) (h17 : S23_17_elt D Ch)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (hline : S23_5_line D Ch) (hKN : KNshape)
    (hS : KSchurL2) (hS3 : KSchurSL3) (hN1 : S23_9_NotSp4SU4O6m D Ch)
    (hN2 : S23_9_NotO6p D Ch) (hN3 : S23_9_NotLarge D Ch) (hTd : KTab23d)
    (h201 : S23_20_1 D Ch) (hStepA : S23_9_StepA D Ch) : S23_21_2 D Ch := by
  intro h1930 c
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hpsig, hppi⟩
  rw [piSet] at hppi
  obtain ⟨hpprime, hpdvd⟩ := hppi
  haveI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨h3m, hV, hSL, hnatSL, hker⟩ :=
    c.sl3Line_of h1930 hE h207 h2 h3 h4 hline hKN KOrdNat.kOrdNatural_holds hS hS3 hN1 hN2 hN3
  have hL2K := c.isL2_bar2_K h1930 h4 hTd (hV := hV) h3m hSL hnatSL hker
  exact (CFSG.Quasithin.A36B.not_dvd_card_fitting_of_pCore_eq_bot (p := p)
    (c.pCore_bar_eq_bot_of_mem_sig hE h207 h52 h53 h54 h6 h4 h12 hVK h17 hL2K h201 hStepA
      h1930 hpsig)) hpdvd

end CFSG.LocalAnalysis.UniquenessCase.UC22
