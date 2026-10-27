module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ContextFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qy
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qw
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
public import CFSG.GroupTheory.OddOrderSylowThree
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.PGroupFixedPointCongruence
public import CFSG.GroupTheory.WielandtProductAux
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.UEqZ
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sig2_eq_empty_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hstd : Sigma23Std D)
    (hhyp : ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀)
    (h613 : UC6.R6_13 D) (h1930 : H1930 D) (c : Ctx23L D Ch) : D.sig2 = ∅ := by
  classical
  apply Set.eq_empty_of_forall_notMem
  intro p hp2
  have hpσ : p ∈ D.sig := by rw [D.sig_sub]; exact Or.inl (Or.inr hp2)
  obtain ⟨hp, hp2ne⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, P0, hH⟩ := hhyp p hp2
  obtain ⟨hfirst, hsc, hInU, -, -⟩ := h613 p P P0 hH
  obtain ⟨h3p, hMsolv, hwc, hΓ, hLie, hfrob⟩ := hfirst
  obtain ⟨-, -, hP0M, -, -, -, -, hfrob_fix⟩ := hfrob
  obtain ⟨hUZ, hUM, hMN⟩ := h4 h1930 c
  have hMZN : D.M ≤ normalizer (D.Z : Set G) := by simpa [hUZ] using hMN
  have hZel : IsElemAbelian 2 D.Z := c.isElemAbelian_Z h4 h1930
  have hZ_le_O2 : D.Z ≤ CFSG.Open.pCoreOf 2 D.M := c.Z_le_pCoreOf_M h4 h1930
  have hCZ : D.Z ⊓ Subgroup.centralizer (P0 : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro z hz
    obtain ⟨hzZ, hzC⟩ := Subgroup.mem_inf.mp hz
    have hzO : z ∈ CFSG.Open.pCoreOf 2 D.M := hZ_le_O2 hzZ
    have hP0ne : P0 ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card P0 = 1 := by rw [hbot]; simp
      rw [hH.card] at hcard
      exact hp.ne_one hcard
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP0ne
    have hxP0 : (x : G) ∈ P0 := x.2
    have hxL : (x : G) ∈ Subgroup.centralizer
        (UC6.inftyOf (Subgroup.centralizer (P0 : Set G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlC : l ∈ Subgroup.centralizer (P0 : Set G) := Subgroup.map_subtype_le _ hl
      exact (Subgroup.mem_centralizer_iff.mp hlC x hxP0).symm
    have hzx : z * x = x * z :=
      (Subgroup.mem_centralizer_iff.mp hzC x hxP0).symm
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact hfrob_fix (x : G) hxL hx1' z hzO hzx
  have hP0p : IsPGroup p P0 :=
    IsPGroup.of_card (n := 1) (by rw [hH.card, pow_one])
  have hP0N : P0 ≤ normalizer (D.Z : Set G) :=
    (hH.le.trans hH.sylow.le).trans hMZN
  have hZmod : Nat.card D.Z ≡ 1 [MOD p] :=
    CFSG.GroupTheory.card_modEq_one_of_isPGroup_normalizes_of_inf_centralizer_eq_bot
      hP0p hP0N hCZ
  set m : ℕ := CFSG.Open.pRank 2 D.Z with hm
  have hZcard : Nat.card D.Z = 2 ^ m := by
    rw [hm]
    exact CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hZel
  have hpdvd : p ∣ 2 ^ m - 1 := by
    rw [hZcard] at hZmod
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num : 0 < 2))).mp hZmod.symm
  have hmdvd : m ∣ c.n := by
    rcases h52 h1930 c with h | ⟨-, -, h⟩
    · rw [h]
    · rw [h]
      exact dvd_mul_left m 2
  have hpeta : p ∈ etaSet c.n :=
    ⟨hp, hpdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hmdvd)⟩
  have hpB0 : p ∈ piSet c.B0 := by rwa [c.hpi]
  obtain ⟨b, hborder⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) p hpB0.2
  have hbB0 : (b : G) ∈ c.B0 := b.2
  have hbM : (b : G) ∈ D.M := c.hBM hbB0
  have hborder' : orderOf (b : G) = p := by rw [Subgroup.orderOf_coe, hborder]
  let c' : Ctx23L D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hbB' : (b : G) ∈ c'.B := by simpa [c'] using hbB0
  have hbZ : (b : G) ∉ Subgroup.centralizer (D.Z : Set G) := by
    intro hbC
    have h543 := h53 h1930 c' (by simpa [c'] using c.hpi)
    rcases h543 with hbot | ⟨-, hpiC⟩
    · have hbint : (b : G) ∈ c'.B ⊓ Subgroup.centralizer (D.Z : Set G) := ⟨hbB', hbC⟩
      rw [hbot, Subgroup.mem_bot] at hbint
      have h1 : orderOf (b : G) = 1 := by rw [hbint, orderOf_one]
      rw [hborder'] at h1
      exact hp.ne_one h1
    · have hpC : p ∈ piSet (c'.B ⊓ Subgroup.centralizer (D.Z : Set G)) := by
        refine ⟨hp, ?_⟩
        have hbzp : Subgroup.zpowers (b : G) ≤
            c'.B ⊓ Subgroup.centralizer (D.Z : Set G) :=
          le_inf (Subgroup.zpowers_le.mpr hbB') (Subgroup.zpowers_le.mpr hbC)
        have hcard : Nat.card (Subgroup.zpowers (b : G)) = p := by
          rw [Nat.card_zpowers, hborder']
        exact hcard ▸ Subgroup.card_dvd_of_le hbzp
      rw [hpiC, Set.mem_setOf_eq] at hpC
      have hplus : p ∣ 2 ^ m + 1 := hpC.2
      have h2' : p ∣ (2 ^ m + 1) - (2 ^ m - 1) := Nat.dvd_sub hplus hpdvd
      have hsub : (2 ^ m + 1) - (2 ^ m - 1) = 2 := by
        have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
        omega
      have h2 : p ∣ 2 := by rwa [hsub] at h2'
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact hp.ne_one h
      · exact hp2ne h
  have hbp : IsPGroup p (Subgroup.zpowers (b : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hborder', pow_one])
  obtain ⟨k, hkM, hk⟩ := UC6.exists_conj_le_of_isSylowOf hH.sylow
    (Subgroup.zpowers_le.mpr hbM) hbp
  let P' : Subgroup G := P.map (MulAut.conj k).toMonoidHom
  let P0' : Subgroup G := P0.map (MulAut.conj k).toMonoidHom
  have hbP' : (b : G) ∈ P' := by
    refine ⟨k⁻¹ * (b : G) * k, hk (b : G) (Subgroup.mem_zpowers _), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hP'M : P' ≤ D.M := by
    rintro - ⟨x, hx, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hkM (hH.sylow.le hx)) (D.M.inv_mem hkM)
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf p P' D.M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hP'M ?_
    rw [show P' = P.map (MulAut.conj k).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj k).injective, hH.sylow.card_eq]
  have hH' : UC6.Hyp612 D p P' P0' := by
    refine ⟨hH.mem_sig2, hP'syl, Subgroup.map_mono hH.le, ?_, ?_⟩
    · rw [show P0' = P0.map (MulAut.conj k).toMonoidHom from rfl,
        Subgroup.card_map_of_injective (MulAut.conj k).injective, hH.card]
    · intro hle
      apply hH.not_le
      intro c₀ hc₀
      have hc₀' : k * c₀ * k⁻¹ ∈ Subgroup.centralizer (P0' : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hcx : x * c₀ = c₀ * x :=
          Subgroup.mem_centralizer_iff.mp hc₀ x hx
        calc k * x * k⁻¹ * (k * c₀ * k⁻¹) = k * (x * c₀) * k⁻¹ := by group
          _ = k * (c₀ * x) * k⁻¹ := by rw [hcx]
          _ = k * c₀ * k⁻¹ * (k * x * k⁻¹) := by group
      have hcm : k⁻¹ * (k * c₀ * k⁻¹) * k ∈ D.M :=
        D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hkM) (hle hc₀')) hkM
      simpa [mul_assoc] using hcm
  obtain ⟨hfirst', hsc', hInU', -, -⟩ := h613 p P' P0' hH'
  obtain ⟨-, -, hwc', hΓ', hLie', hfrob'⟩ := hfirst'
  let P1' : Subgroup G := P' ⊓ UC6.inftyOf (Subgroup.centralizer (P0' : Set G))
  have hP1'le : P1' ≤ P' := inf_le_left
  have hP1'normal : (P1'.subgroupOf P').Normal := by
    refine ⟨fun a ha p => ?_⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    have ha' : (a : G) ∈ P1' := Subgroup.mem_subgroupOf.mp ha
    have hmem : (p : G) * (a : G) * (p : G)⁻¹ ∈ P' :=
      P'.mul_mem (P'.mul_mem (p : P').2 (hsc'.1 ha')) (P'.inv_mem (p : P').2)
    have hclosed := hsc'.2 (a : G) ha' ((p : G)⁻¹) (by simpa using hmem)
    simpa [P1'] using hclosed
  have hP'normP1 : P' ≤ normalizer (P1' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP1'le).1 hP1'normal
  obtain ⟨n, hn1, hP1'el, hP1'card⟩ :=
    uc22p22q_P1_elem D hstd hH' hwc' hLie' hp2ne
  have hP1'ne : P1' ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card P1' = 1 := by rw [hbot]; simp
    rw [hP1'card] at hcard
    have hgt : 1 < p ^ n := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  obtain ⟨x, hxP1', hx1, hxc⟩ :=
    CFSG.GroupTheory.WielandtProduct.exists_mem_commute_of_le_of_isPGroup
      (p := p) (P := P') (N := P1') hP'syl.isPGroup hP1'le hP'normP1 hP1'ne
  let X : Subgroup G := Subgroup.zpowers x
  have hXleP1 : X ≤ P1' := Subgroup.zpowers_le.mpr hxP1'
  have hXp : IsPGroup p X := hP'syl.isPGroup.to_le (hXleP1.trans hP1'le)
  have hXne : X ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hx1
  have hXM : X ≤ D.M := (hXleP1.trans hP1'le).trans hP'M
  have hXb : X ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hxc (b : G) hbP').zpow_left j
  have hXU : X ∈ uniqueSet D.M := by
    obtain ⟨-, huniq⟩ := hInU' X hXleP1 hXne
    refine ⟨hXM, fun g hg => ?_⟩
    have hg' : X ≤ uniqueFourConj g⁻¹ D.M := by
      simpa [uniqueFourConj, inv_inv] using hg
    have hres := huniq g⁻¹ hg'
    simpa [uniqueFourConj, inv_inv] using hres
  have h54 : S23_5_4 D Ch := s23_5_4_of D Ch h4 hsp
  have hXle : X ≤ D.M ⊓ Subgroup.centralizer ({(b : G)} : Set G) := le_inf hXM hXb
  exact ((h54 h1930 c' (b : G) hbB' hbZ).2 p hp X hXne hXp hXle).1 hXU


theorem sig3_eq_empty_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (hstd : Sigma23Std D) (h611 : UC6.R6_11Used D) (h638 : UC6.R6_38 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 D.Z) (h1930 : H1930 D) (c : Ctx23L D Ch) : D.sig3 = ∅ := by
  classical
  apply Set.eq_empty_of_forall_notMem
  intro q hq3
  have hq3eq : q = 3 := hstd.sig3_sub hq3
  subst q
  have h3sig : 3 ∈ D.sig := by rw [D.sig_sub]; exact Or.inr hq3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hUZ, hUM, hMN⟩ := h4 h1930 c
  have hZM : D.Z ≤ D.M := by simpa [hUZ] using hUM
  have hMZN : D.M ≤ normalizer (D.Z : Set G) := by simpa [hUZ] using hMN
  have hZel : IsElemAbelian 2 D.Z := c.isElemAbelian_Z h4 h1930
  have hZ2 : IsPGroup 2 D.Z := CFSG.Open.IsElemAbelian.isPGroup hZel
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  obtain ⟨hshape, -, -, h5, h4'⟩ := h611 hq3 P hP
  obtain ⟨e⟩ := hshape
  obtain ⟨Q, hQ, hPQ, hZQ⟩ := UC6.uc22p22q_exists_Q
    (P := P) (V := D.Z) hP.isPGroup hP.le hMZN hZM hZ2
  have hZ2P_le_C : (Subgroup.upperCentralSeries ↥P 2).map P.subtype ≤
      Subgroup.centralizer (D.Z : Set G) := by
    rintro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (h5 Q hQ hPQ D.Z hZQ hZel.1 (hP.le.trans hMZN) b hb z hz).symm
  have hZP_le_C : (Subgroup.center ↥P).map P.subtype ≤
      Subgroup.centralizer (D.Z : Set G) := by
    refine (Subgroup.map_mono ?_).trans hZ2P_le_C
    rw [← Subgroup.upperCentralSeries_one]
    exact Subgroup.upperCentralSeries_mono _ (by norm_num : 1 ≤ 2)
  obtain ⟨y, hyP, hy3, hyJ⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_orderOf_eq_three_not_mem_thompsonSubgroup e
  let X : Subgroup G := Subgroup.zpowers y
  have hXleP : X ≤ P := Subgroup.zpowers_le.mpr hyP
  have hXcard : Nat.card X = 3 := by rw [Nat.card_zpowers, hy3]
  have hXJ : ¬ X ≤ thompsonSubgroup P := by
    intro hle
    exact hyJ (hle (Subgroup.mem_zpowers y))
  obtain ⟨-, -, -, -, hcyc, -⟩ := h4' X Q hXleP hXcard hXJ hQ hPQ
  have hyZ : y ∉ Subgroup.centralizer (D.Z : Set G) := by
    intro hyC
    have hXZ : X ≤ Subgroup.centralizer (D.Z : Set G) := Subgroup.zpowers_le.mpr hyC
    have hZleCX : D.Z ≤ Subgroup.centralizer (X : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hXZ hx) z hz).symm
    have hZleCZP : D.Z ≤ Subgroup.centralizer
        (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (hZP_le_C hb) z hz).symm
    let W : Subgroup G := Q ⊓ Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)
    have hZleW : D.Z ≤ W := le_inf (le_inf hZQ hZleCX) hZleCZP
    have hrank : CFSG.Open.pRank 2 D.Z ≤ 1 := by
      refine (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 2) hZleW).trans ?_
      exact CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_two (by simpa [W] using hcyc)
    omega
  let K : Subgroup G := D.M ⊓ Subgroup.centralizer (D.Z : Set G)
  have hK_le_M : K ≤ D.M := inf_le_left
  have hK_T : D.T ≤ K := le_inf D.sylowM.le (uc22main1_T_le_centralizer D)
  have hM_le_NK : D.M ≤ normalizer (K : Set G) := by
    have hM_le_NM : D.M ≤ normalizer (D.M : Set G) := Subgroup.le_normalizer
    have hM_le_NC : D.M ≤ normalizer (Subgroup.centralizer (D.Z : Set G) : Set G) :=
      hMZN.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D.Z)
    exact (le_inf hM_le_NM hM_le_NC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hK_normal : (K.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_M).2 hM_le_NK
  letI : (K.subgroupOf D.M).Normal := hK_normal
  let Mstar := ↥D.M ⧸ K.subgroupOf D.M
  let q : ↥D.M →* Mstar := QuotientGroup.mk' (K.subgroupOf D.M)
  let Pstar : Subgroup Mstar := (P.subgroupOf D.M).map q
  obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
  let PstarSylow : Sylow 3 Mstar := S.mapSurjective (QuotientGroup.mk'_surjective _)
  have hPstar_coe : (PstarSylow : Subgroup Mstar) = Pstar := by
    rw [Sylow.coe_mapSurjective, hS]
  have hPstar_ne : Pstar ≠ ⊥ := by
    have hybar_mem : q ⟨y, hP.le hyP⟩ ∈ Pstar := ⟨⟨y, hP.le hyP⟩, hyP, rfl⟩
    intro hbot
    have hybar1 : q ⟨y, hP.le hyP⟩ = 1 := by
      have : q ⟨y, hP.le hyP⟩ ∈ (⊥ : Subgroup Mstar) := hbot ▸ hybar_mem
      simpa using this
    have hyK : y ∈ K := by
      have h1 := (QuotientGroup.eq_one_iff (N := K.subgroupOf D.M)
        (x := ⟨y, hP.le hyP⟩)).mp hybar1
      exact Subgroup.mem_subgroupOf.mp h1
    exact hyZ hyK.2
  have hPcard81 : Nat.card P = 81 := by
    calc Nat.card P = Nat.card (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) :=
          Nat.card_congr e.toEquiv
      _ = 81 := by
        rw [RegularWreathProduct.card,
          CFSG.LocalAnalysis.RankThreeTheoremC.wreath_card_zmod_three]
        norm_num
  obtain ⟨B, hBZ2, hBp, hBnc⟩ := uc22p22q_wreath_Z2 e
  have hBP : B ≤ P := hBZ2.trans (Subgroup.map_subtype_le _)
  have hBK : B ≤ P ⊓ K := by
    refine le_inf hBP (le_inf (hBP.trans hP.le) ?_)
    exact hBZ2.trans hZ2P_le_C
  have hBcard9 : 9 ≤ Nat.card B := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hBp
    have hj2 : 2 ≤ j := by
      by_contra h
      have hjle : j ≤ 1 := by omega
      interval_cases j
      · have hBbot : B = ⊥ := Subgroup.card_eq_one.mp (by simpa using hj)
        exact hBnc (hBbot ▸ isCyclic_of_subsingleton (α := (⊥ : Subgroup G)))
      · exact hBnc (isCyclic_of_prime_card (by simpa using hj))
    have hpow : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    simpa [hj] using hpow
  have hPK9 : 9 ≤ Nat.card ↥(P ⊓ K) := hBcard9.trans (Subgroup.card_le_of_le hBK)
  have hPstar_card : Nat.card Pstar * Nat.card ↥(P ⊓ K) = 81 := by
    have h := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker q (P.subgroupOf D.M)
    rw [QuotientGroup.ker_mk'] at h
    have hsub : Nat.card (P.subgroupOf D.M) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.le).toEquiv
    have hinf : Nat.card ↥((P.subgroupOf D.M) ⊓ (K.subgroupOf D.M)) = Nat.card ↥(P ⊓ K) := by
      rw [show (P.subgroupOf D.M) ⊓ (K.subgroupOf D.M) = (P ⊓ K).subgroupOf D.M by
        ext x; simp [Subgroup.mem_subgroupOf]]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := P ⊓ K) (K := D.M)
        (inf_le_left.trans hP.le)).toEquiv
    rw [hsub, hinf, hPcard81] at h
    exact h.symm
  have hPstar_le9 : Nat.card Pstar ≤ 9 := by
    have hmul : Nat.card Pstar * 9 ≤ 81 := by
      calc Nat.card Pstar * 9 ≤ Nat.card Pstar * Nat.card ↥(P ⊓ K) :=
            Nat.mul_le_mul_left _ hPK9
        _ = 81 := hPstar_card
    exact Nat.le_of_mul_le_mul_right (by simpa using hmul) (by norm_num)
  have hPstar_dvd9 : Nat.card Pstar ∣ 9 := by
    have hdvd81 : Nat.card Pstar ∣ 81 := by
      rw [← hPstar_card]
      exact dvd_mul_right _ _
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using hdvd81 : Nat.card Pstar ∣ 3 ^ 4)
    have hj2 : j ≤ 2 := by
      have h1 : 3 ^ j ≤ 3 ^ 2 := by simpa [hj] using hPstar_le9
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
    rw [hj]
    exact pow_dvd_pow 3 hj2
  have hMstar_odd : Odd (Nat.card Mstar) := by
    have hcard : Nat.card Mstar = K.relIndex D.M := by
      rw [show Nat.card Mstar = (K.subgroupOf D.M).index from
        (Subgroup.index_eq_card (H := K.subgroupOf D.M)).symm]
      rfl
    rw [hcard]
    have hdvd : K.relIndex D.M ∣ D.T.relIndex D.M :=
      Subgroup.relIndex_dvd_of_le_left D.M hK_T
    have hTodd : Odd (D.T.relIndex D.M) := by
      refine Nat.not_even_iff_odd.mp ?_
      intro heven
      exact (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.2 (even_iff_two_dvd.mp heven)
    exact Odd.of_dvd_nat hTodd hdvd
  obtain ⟨Nstar, hNstar_normal, hNstar_ne, hNstar_p⟩ :=
    CFSG.GroupTheory.exists_normal_isPGroup_quotient_of_odd_order_sylow_three hMstar_odd
      PstarSylow (by simpa [hPstar_coe] using hPstar_dvd9) (by simpa [hPstar_coe] using hPstar_ne)
  letI : Nstar.Normal := hNstar_normal
  let N : Subgroup ↥D.M := Nstar.comap q
  have hKsub_le_N : K.subgroupOf D.M ≤ N := by
    intro x hx
    change x ∈ Nstar.comap q
    rw [Subgroup.mem_comap]
    have hx1 : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact Nstar.one_mem
  have hN_normal : N.Normal := Subgroup.Normal.comap hNstar_normal q
  letI : N.Normal := hN_normal
  have hNmap : N.map q = Nstar := by
    rw [show N = Nstar.comap q from rfl]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Nstar
  have hN_ne : N ≠ ⊤ := by
    intro htop
    apply hNstar_ne
    rw [← hNmap, htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let eN : (↥D.M ⧸ N) ≃* (Mstar ⧸ Nstar) :=
    (QuotientGroup.quotientQuotientEquivQuotient (N := K.subgroupOf D.M) (M := N)
      hKsub_le_N).symm.trans (QuotientGroup.quotientMulEquivOfEq hNmap)
  have hNquot : IsPGroup 3 (↥D.M ⧸ N) := IsPGroup.of_equiv hNstar_p eN.symm
  have hOp : UC22.F10.OpRes 3 D.M = D.M :=
    h638 3 Nat.prime_three (by norm_num) (Or.inl h3sig)
  exact hN_ne (UC6.eq_top_of_isPGroup_quotient_of_opRes_eq_uc6 Nat.prime_three hOp N hNquot)


theorem s23_6_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hstd : Sigma23Std D)
    (hhyp : ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀)
    (h613 : UC6.R6_13 D) (h611 : UC6.R6_11Used D) (h638 : UC6.R6_38 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 D.Z) : S23_6 D Ch := by
  intro h1930 c
  have h2 := sig2_eq_empty_of D Ch h4 h52 h53 hsp hstd hhyp h613 h1930 c
  have h3 := sig3_eq_empty_of D Ch h4 hstd h611 h638 hn h1930 c
  rw [D.sig_sub, h2, h3, Set.union_empty, Set.union_empty]

end CFSG.LocalAnalysis.UniquenessCase.UC22
