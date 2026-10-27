module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThreeHyp125
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaBound
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27A
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg
public import CFSG.RankThree.PartTwo.Sec17.G1724J2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem one_le_pRank_five_centralizer_of_hyp125 (D : Data G) {V₀ V : Subgroup G}
    {L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h5rank : 3 ≤ CFSG.Open.pRank 5 D.M) (h26a : mSub V₀ ≤ 4)
    (h26b1 : P17_26b_1 D V₀ V L c.hyp125.isElemAbelian) :
    ∀ v ∈ V, (v : G) ≠ 1 →
      1 ≤ CFSG.Open.pRank 5 (D.M ⊓ Subgroup.centralizer ({(v : G)} : Set G)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpair := c.hyp125.pairFacts
  have h25M : 25 ∣ Nat.card ↥D.M := by
    obtain ⟨E, hEM, _hEel, hEcard⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank
      (M := D.M) Nat.prime_five (k := 3) h5rank
    have h25E : 25 ∣ Nat.card E := by
      rw [hEcard]
      norm_num
    exact h25E.trans (Subgroup.card_dvd_of_le hEM)
  intro v hvV hv1
  by_cases hv0 : v ∈ V₀
  · let : MulAction ↥D.M G :=
      { smul := fun m x => (m : G) * x * (m : G)⁻¹
        one_smul := fun x => by
          show ((1 : ↥D.M) : G) * x * ((1 : ↥D.M) : G)⁻¹ = x
          simp
        mul_smul := fun m n x => by
          show ((m * n : ↥D.M) : G) * x * ((m * n : ↥D.M) : G)⁻¹ =
            (m : G) * ((n : G) * x * (n : G)⁻¹) * (m : G)⁻¹
          rw [Subgroup.coe_mul]
          group }
    have hstab : MulAction.stabilizer D.M v =
        (D.M ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf D.M := by
      ext m
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      show (m : G) * v * (m : G)⁻¹ = v ↔
        ((m : G) ∈ D.M ∧ (m : G) * v = v * (m : G))
      rw [mul_inv_eq_iff_eq_mul]
      exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩
    have hcard : Nat.card ↥D.M = (MulAction.orbit D.M v).ncard *
        Nat.card ↥(MulAction.stabilizer D.M v) := by
      rw [← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
    have hstabcard : Nat.card ↥(MulAction.stabilizer D.M v) =
        Nat.card ↥(D.M ⊓ Subgroup.centralizer ({v} : Set G)) := by
      rw [hstab]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hcard' : Nat.card ↥D.M =
        (MulAction.orbit D.M v).ncard *
          Nat.card ↥(D.M ⊓ Subgroup.centralizer ({v} : Set G)) := by
      calc Nat.card ↥D.M =
          (MulAction.orbit D.M v).ncard * Nat.card ↥(MulAction.stabilizer D.M v) := hcard
        _ = (MulAction.orbit D.M v).ncard *
            Nat.card ↥(D.M ⊓ Subgroup.centralizer ({v} : Set G)) :=
          congrArg (fun n => (MulAction.orbit D.M v).ncard * n) hstabcard
    clear hcard hstabcard
    have hOsub : (MulAction.orbit D.M v : Set G) ⊆ (V₀ : Set G) := by
      rintro w ⟨m, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (hpair.le_normalizer₀ m.2) v).1 hv0
    have hOle16 : (MulAction.orbit D.M v).ncard ≤ 16 := by
      calc (MulAction.orbit D.M v).ncard ≤ (V₀ : Set G).ncard :=
            Set.ncard_le_ncard hOsub (Set.toFinite _)
        _ = Nat.card ↥V₀ := (Nat.card_coe_set_eq (V₀ : Set G)).symm
        _ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hpair.elemAbelian₀.isPGroup
        _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h26a
        _ = 16 := by norm_num
    have hOpos : 0 < (MulAction.orbit D.M v).ncard := by
      refine (Set.ncard_pos (Set.toFinite _)).2 ⟨v, ?_⟩
      exact ⟨1, by show ((1 : ↥D.M) : G) * v * ((1 : ↥D.M) : G)⁻¹ = v; simp⟩
    generalize hO : (MulAction.orbit D.M v).ncard = O at hcard' hOle16 hOpos ⊢
    generalize hC : Nat.card ↥(D.M ⊓ Subgroup.centralizer ({v} : Set G)) = C at hcard' ⊢
    have h25OC : 25 ∣ O * C := by
      rw [hcard'] at h25M
      exact h25M
    have h5C : 5 ∣ C := by
      by_cases h5O : 5 ∣ O
      · obtain ⟨k, hk⟩ := h5O
        have hkpos : 0 < k := by
          by_contra h
          have h0 : k = 0 := Nat.eq_zero_of_not_pos h
          rw [h0, mul_zero] at hk
          omega
        have h5kC : 5 ∣ k * C := by
          have h : 5 * 5 ∣ 5 * (k * C) := by
            have h' := h25OC
            rw [hk] at h'
            rwa [← show (5 : ℕ) * 5 = 25 by norm_num,
              show 5 * k * C = 5 * (k * C) by ring] at h'
          exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5) h
        have hk3 : k ≤ 3 := by
          have h : 5 * k ≤ 16 := by rw [← hk]; exact hOle16
          omega
        have h5k : ¬ 5 ∣ k := fun h => by
          have := Nat.le_of_dvd hkpos h
          omega
        rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5kC with h | h
        · exact absurd h h5k
        · exact h
      · have h5OC : 5 ∣ O * C := (by norm_num : 5 ∣ 25).trans h25OC
        rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5OC with h | h
        · exact absurd h h5O
        · exact h
    rw [← hC] at h5C
    exact s13_one_le_pRank_of_dvd _ Nat.prime_five h5C
  · have h1 : CFSG.Open.pRank 5 ((D.M ⊓ Subgroup.centralizer ({v} : Set G)) ⊓
        F11.CTilde D.M V₀ V) = 1 := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
        ← CFSG.SectionRank.pRank_eq_open_pRank_top (p := 5)]
      exact h26b1 ⟨v, hvV⟩ hv1 hv0
    have hmono := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5)
      (inf_le_left : (D.M ⊓ Subgroup.centralizer ({v} : Set G)) ⊓
        F11.CTilde D.M V₀ V ≤ D.M ⊓ Subgroup.centralizer ({v} : Set G))
    rw [h1] at hmono
    exact hmono

theorem seventeen_twentyseven_step (D : Data G)
    (V₀ V : Subgroup G) (hSg : UC6S846.SigmaStd D) (h17_22 : R17_22At D V₀ V)
    (h17_23 : R17_23At D V₀ V) (L : Subgroup G) (c : Ctx17_17 D V₀ V L)
    (hmBar : mBar D.M V₀ V c.hyp125.isElemAbelian = 4) (hm4 : mSub V₀ ≤ 4)
    (h26b1 : P17_26b_1 D V₀ V L c.hyp125.isElemAbelian)
    (h26b3 : P17_26b_3 D V₀ V L c.hyp125.isElemAbelian)
    (A : Subgroup G) (hA : A ∈ E3.gammaSet V 0 D.T) :
    barSub V₀ V c.hyp125.isElemAbelian A = ⊥ ∨
      barSub V₀ V c.hyp125.isElemAbelian A ∈
        E3.aSet 3 (Mbar D.M V₀ V c.hyp125.isElemAbelian) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hV := c.hyp125.isElemAbelian
  by_cases hA1 : barSub V₀ V hV A = ⊥
  · exact Or.inl hA1
  · right
    have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC c.mem_calC
    have hsig : D.sig = {5} := sig_eq_five_of_J2 h17_22 h17_23 c
    have hsig5 : 5 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 5
    have h5rank : 3 ≤ CFSG.Open.pRank 5 D.M := hSg.three_le 5 hsig5
    have hcent := one_le_pRank_five_centralizer_of_hyp125 D c h5rank hm4 h26b1
    have hsig1 : D.sig = D.sig1 := by
      refine Set.Subset.antisymm (UC6S846.sig_subset_sig1 hSg hns) ?_
      intro q hq
      rw [D.sig_sub]
      exact Or.inl (Or.inl hq)
    have hinf : ∀ g : G, g ∉ D.M → V₀ ⊓ conjSubgroup V g = ⊥ := by
      intro g hg
      have hΓ : rankThreeGamma 1 2 V₀ ≤ D.M :=
        rankThreeGamma_le_of_normalizer_le (M := D.M) (V₀ := V₀) (Z := V₀)
          c.hyp125.hyp62.normalizer_le le_rfl
      have h22 := sixteen_twentyTwo_gen D hSg hsig1 hV (p := 5) hsig5 hcent
      have hginv : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
      have h := h22 g⁻¹ hginv V₀ c.hyp125.pairFacts.le hΓ
      have h' : conjSubgroup (conjSubgroup V₀ g⁻¹ ⊓ V) g = ⊥ := by
        rw [h, E3.conjSubgroup_bot]
      rwa [E3.conjSubgroup_inf, E3.conjSubgroup_inv_conj] at h'
    have hr : (((3 + 0 + mSub V₀ : ℕ)) : ℕ∞) ≤ rMV D.M V := by
      have h1 : (((3 + 0 + mSub V₀ : ℕ)) : ℕ∞) ≤
          (((4 + mSub V₀ : ℕ)) : ℕ∞) := by
        exact_mod_cast (by omega : 3 + 0 + mSub V₀ ≤ 4 + mSub V₀)
      exact h1.trans h26b3
    have hδ : (((3 + 0 : ℕ)) : ℕ∞) ≤ deltaInf D.M V :=
      succ_le_deltaInf_of_mBarGT D c.hyp125 (n := 2)
        ((c.hyp125.mBarGT_iff_lt_mBar 2).2 (by omega))
    exact barSub_mem_calABar_of_gammaSet_gen D hSg hsig1 c.hyp125 (p := 5) hsig5
      hcent hinf (i := 0) (k := 3) hr hδ (E3.gammaSet_mono D.sylowM.le hA) hA1

theorem wClos_zero_le_cTilde_of_gap (D : Data G)
    (V₀ V : Subgroup G) (hSg : UC6S846.SigmaStd D) (h17_22 : R17_22At D V₀ V)
    (h17_23 : R17_23At D V₀ V) (h17_25 : R17_25At D V₀ V) (h26a : R17_26aAt D V₀ V)
    (h26b1 : R17_26b_1At D V₀ V) (h26b3 : R17_26b_3At D V₀ V)
    (L : Subgroup G) (c : Ctx17_17 D V₀ V L) :
    E3.wClos V 0 D.T ≤ F11.CTilde D.M V₀ V := by
  have hpair := c.hyp125.pairFacts
  have hTM : D.T ≤ D.M := D.sylowM.le
  have haBar : E3.aParam (Mbar D.M V₀ V c.hyp125.isElemAbelian) = 2 := (h17_25 L c).2.2.2
  unfold E3.wClos
  refine iSup_le fun A => iSup_le fun hA_mem => ?_
  rcases seventeen_twentyseven_step D V₀ V hSg h17_22 h17_23 L c (h17_25 L c).2.2.1
    (h26a L c) (h26b1 L c) (h26b3 L c) A hA_mem with hbot | hset
  · exact (barSub_eq_bot_iff c.hyp125.isElemAbelian
      hpair.le_normalizer hpair.le_normalizer₀ (hA_mem.1.trans hTM)).mp hbot
  · have h3 : 3 ≤ E3.aParam (Mbar D.M V₀ V c.hyp125.isElemAbelian) :=
      E3.le_aParam_of_mem_aSet (by norm_num) hset
    omega

noncomputable def psiNQ {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    ↥(D.M ⊓ Subgroup.normalizer ((D.T ⊓ F11.CTilde D.M V₀ V : Subgroup G) : Set G)) →*
      ↥(Mbar D.M V₀ V h.isElemAbelian) :=
  ((actTil V₀ V h.isElemAbelian).comp (Subgroup.inclusion (fun _ hx =>
      le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
        (Subgroup.mem_inf.mp hx).1))).codRestrict _
    (fun x => actTil_mem_barSub V₀ V h.isElemAbelian (Subgroup.mem_inf.mp x.2).1
      (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
        (Subgroup.mem_inf.mp x.2).1))

theorem psiNQ_surjective {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    Function.Surjective (psiNQ h) := by
  intro y
  obtain ⟨m, hmM, hmy⟩ :=
    (mem_barSub V₀ V h.isElemAbelian D.M (y : MulAut (Vtil V₀ V h.isElemAbelian))).mp y.2
  obtain ⟨n, hn, c, hc, hmn⟩ :=
    exists_mem_normalizer_mul_of_isSylowIn (cTilde_le_M D.M V₀ V)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M D.M V₀ V)).1
        (cTilde_subgroupOf_normal h.isElemAbelian h.pairFacts.le_normalizer
          h.pairFacts.le_normalizer₀))
      (by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hTsyl : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
          (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
        exact hTsyl.inf_normal (cTilde_le_M D.M V₀ V)
          (cTilde_subgroupOf_normal h.isElemAbelian h.pairFacts.le_normalizer
            h.pairFacts.le_normalizer₀))
      (m : G) hmM
  have hcM : c ∈ D.M := cTilde_le_M D.M V₀ V hc
  have hcS : c ∈ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ hcM
  have hnS : n ∈ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ (Subgroup.mem_inf.mp hn).1
  obtain ⟨-, h', h'1⟩ := (mem_cTilde_iff h.isElemAbelian h.pairFacts.le_normalizer).mp hc
  have hcact : actTil V₀ V h.isElemAbelian ⟨c, hcS⟩ = 1 := by
    rw [show (⟨c, hcS⟩ : stabTil V₀ V) = ⟨c, h'⟩ from rfl, h'1]
  refine ⟨⟨n, hn⟩, ?_⟩
  apply Subtype.ext
  have hpsi : (psiNQ h ⟨n, hn⟩ : MulAut (Vtil V₀ V h.isElemAbelian)) =
      actTil V₀ V h.isElemAbelian ⟨n, hnS⟩ := rfl
  rw [hpsi]
  have heq : (⟨n, hnS⟩ : stabTil V₀ V) = ⟨c, hcS⟩⁻¹ * m := by
    apply Subtype.ext
    show n = c⁻¹ * (m : G)
    rw [hmn]
    group
  rw [heq, map_mul, map_inv, hcact, inv_one, one_mul, hmy]

theorem seventeen_twentyseven
    (D : Data G) (V₀ V : Subgroup G)
    (h17_25 : R17_25At D V₀ V)
    (h26a : R17_26aAt D V₀ V) (h26b1 : R17_26b_1At D V₀ V) (h26b3 : R17_26b_3At D V₀ V)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) :
    R17_27At D V₀ V := by
  intro L c
  have hV := c.hyp125.isElemAbelian
  have hleC : E3.wClos V 0 D.T ≤ F11.CTilde D.M V₀ V :=
    wClos_zero_le_cTilde_of_gap D V₀ V hSg h17_22 h17_23 h17_25 h26a h26b1 h26b3 L c
  refine ⟨?_, ?_⟩
  · rw [Wi_eq_wClos 0 D.T V hV]
    exact hleC
  set K : Subgroup G := F11.CTilde D.M V₀ V with hKdef
  set S : Subgroup G := D.T ⊓ K with hSdef
  have hTsyl : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
  have hWleT : E3.wClos V 0 D.T ≤ D.T := E3.wClos_le 0 D.T
  have hW2 : IsPGroup 2 (E3.wClos V 0 D.T) := hTsyl.2.1.to_le hWleT
  have hWS : E3.wClos V 0 D.T ≤ S := by
    refine E3.wClos_le_of_forall fun A hA => le_inf hA.1 ?_
    exact (E3.le_wClos hA).trans hleC
  have hWne : E3.wClos V 0 D.T ≠ ⊥ := TwelveShort.wClos_zero_ne_bot D c.hyp125.inCalV
  have hTwoLocal : IsTwoLocal (Subgroup.normalizer (E3.wClos V 0 D.T : Set G)) :=
    ⟨E3.wClos V 0 D.T, hWne, hW2, rfl⟩
  have hNMS : D.M ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    inf_le_right.trans
      (E3.e3_15_normalizer hTsyl (inf_le_left.trans D.sylowM.le)
        (hTsyl.2.1.to_le inf_le_left) hWS)
  have hL1 : barSub V₀ V hV L ≠ ⊥ := by
    have hWpow : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
    have hcardW : Nat.card (Vtil V₀ V hV) =
        2 ^ CFSG.Quasithin.rk (⊤ : Subgroup (Vtil V₀ V hV)) := by
      rw [← Subgroup.card_top (G := Vtil V₀ V hV)]
      exact CFSG.Quasithin.card_eq_two_pow hWpow (⊤ : Subgroup (Vtil V₀ V hV))
    have h12 : CFSG.Quasithin.rk (⊤ : Subgroup (Vtil V₀ V hV)) = 12 := by
      rw [CFSG.Quasithin.rk_top]
      exact (h17_25 L c).2.1
    have hcard2 : 2 < Nat.card (Vtil V₀ V hV) := by
      rw [hcardW, h12]
      norm_num
    exact ne_bot_of_isIrrOn_of_two_lt_card hWpow (h17_25 L c).1 hcard2
  have hLbar2 : 2 ≤ CFSG.Open.pRank 5 (barSub V₀ V hV L) := by
    obtain ⟨eJ⟩ := isSpor_barSub_of_J2 c.hyp125 c (h17_23 L c) hL1
    have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
      Finite.of_equiv _ eJ.toEquiv
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barSub V₀ V hV L)]
    calc 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J2)) :=
          CFSG.RankThree.PartTwo.Sec17.G1724.two_le_pRank_five_J2
      _ = CFSG.Open.pRank 5 (⊤ : Subgroup ↥(barSub V₀ V hV L)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eJ).symm
  have hMbar2 : 2 ≤ CFSG.Open.pRank 5 (Mbar D.M V₀ V hV) :=
    hLbar2.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5)
      (barSub_mono V₀ V hV c.mem_calC.1.le))
  have hNbar2 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  have hNS2 : 2 ≤ CFSG.Open.pRank 5 (D.M ⊓ Subgroup.normalizer (S : Set G)) :=
    CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_surjective
      (psiNQ c.hyp125) (psiNQ_surjective c.hyp125) (by norm_num) hNbar2
  obtain ⟨E, hEN, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 5 Nat.prime_five
      (D.M ⊓ Subgroup.normalizer (S : Set G))
  have hEnc : ¬ IsCyclic ↥E :=
    CFSG.Quasithin.H13.NQCore.not_isCyclic_of_card_pow (by omega) hEcard hEel.2
  have hsig : D.sig = {5} := sig_eq_five_of_J2 h17_22 h17_23 c
  have hsig5 : 5 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 5
  have hU : UniqueMax D.M E :=
    h61 5 hsig5 E (hEN.trans inf_le_left) hEel.isPGroup hEnc
  have hENW : E ≤ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) := hEN.trans hNMS
  have hWi : F12.Wi 0 D.T V = E3.wClos V 0 D.T := Wi_eq_wClos 0 D.T V hV
  exact uc22p22p_le_of_uniqueMax hU (hWi ▸ hTwoLocal) (hWi ▸ hENW)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
