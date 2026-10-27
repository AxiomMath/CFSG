module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Common
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R874
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKGammaLemmas
public import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSL3 IsSU3)

private theorem pCoreOf_subgroupOf_le_center_of_quasisimple {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥X) :
    (CFSG.Open.pCoreOf p X).subgroupOf X ≤ Subgroup.center ↥X := by
  have hZle : CFSG.Open.pCoreOf p X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le p X
  have hnorm : ((CFSG.Open.pCoreOf p X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZle).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := p) X)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      ((CFSG.Open.pCoreOf p X).subgroupOf X) with h | h
  · exact h
  · exfalso
    have htop : CFSG.Open.pCoreOf p X = X := by
      refine le_antisymm hZle ?_
      exact Subgroup.subgroupOf_eq_top.1 h
    have hP : IsPGroup p ↥X := by
      have hcore : IsPGroup p ↥(CFSG.Open.pCoreOf p X) :=
        CFSG.LieType.BorelTits.pCoreOf_isPGroup p X
      rwa [htop] at hcore
    have : Nontrivial ↥X := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    have : Group.IsPerfect ↥X := ⟨hq.1⟩
    exact Group.IsPerfect.not_isNilpotent ↥X hP.isNilpotent

private theorem odd_card_center_of_pCoreOf_two_eq_bot {G : Type} [Group G] [Finite G]
    {X : Subgroup G} (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) :
    Odd (Nat.card (Subgroup.center ↥X)) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥X) := even_iff_two_dvd.mp heven
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (G := Subgroup.center ↥X) hdvd
  have hzne : (z : ↥X) ≠ 1 := by
    intro h1
    have hone : orderOf (z : ↥X) = 1 := orderOf_eq_one_iff.mpr h1
    rw [Subgroup.orderOf_coe, hz] at hone
    norm_num at hone
  let zx : Subgroup ↥X := Subgroup.zpowers (z : ↥X)
  have hzxcen : zx ≤ Subgroup.center ↥X := Subgroup.zpowers_le.mpr z.2
  have : zx.Normal := Subgroup.normal_of_le_center hzxcen
  have hzxp : IsPGroup 2 zx := IsPGroup.of_card (n := 1) (by
    rw [show Nat.card ↥zx = orderOf (z : ↥X) from Nat.card_zpowers _, Subgroup.orderOf_coe, hz]
    norm_num)
  have hzxle : zx ≤ CFSG.pCore 2 ↥X :=
    CFSG.LieType.BorelTits.le_pCore 2 (inferInstance : zx.Normal) hzxp
  have hpbot : CFSG.pCore 2 ↥X = ⊥ := by
    have hle : CFSG.pCore 2 ↥X ≤ X.subtype.ker :=
      (Subgroup.map_eq_bot_iff (CFSG.pCore 2 ↥X)).mp (by simpa [CFSG.Open.pCoreOf] using hO2)
    simpa using hle
  have hmem : (z : ↥X) ∈ (⊥ : Subgroup ↥X) :=
    (hzxle.trans (le_of_eq hpbot)) (Subgroup.mem_zpowers (z : ↥X))
  exact hzne (by simpa using hmem)

private theorem one_le_pRank_of_isPGroup_ne_bot {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p ↥H) (hne : H ≠ ⊥) :
    1 ≤ CFSG.Open.pRank p H := by
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥H)
  have hpdvd : p ∣ Nat.card ↥H :=
    (IsPGroup.dvd_orderOf hH hz1).trans (orderOf_dvd_natCard z)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p (G := ↥H) hpdvd
  have hwp : (w : G) ^ p = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, hw]
  have hE : CFSG.Open.IsElemAbelian p (Subgroup.zpowers (w : G)) :=
    CFSG.Open.isElemAbelian_zpowers (p := p) hwp
  refine CFSG.SectionRank.le_pRank (p := p) (Fact.out : p.Prime).one_lt
    (Subgroup.zpowers_le.mpr w.2) hE ?_
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw, pow_one]

private theorem eq_three_of_dvd_fortyEight {m : ℕ} (hdvd : m ∣ 48) (hodd : Odd m) (h3 : 3 ∣ m) :
    m = 3 := by
  have hcop : m.Coprime (2 ^ 4) :=
    (Nat.coprime_pow_right_iff (by norm_num) m 2).mpr (Nat.coprime_two_right.mpr hodd)
  have hm3 : m ∣ 3 := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rwa [show 2 ^ 4 * 3 = 48 by norm_num]
  exact Nat.dvd_antisymm hm3 h3

private theorem natCard_griessHopfMultiplier_psl3_2_2
    (hgr : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .PSL 3 2 2) :
    Nat.card (griessHopfMultiplier Y) = 48 := by
  have hcl : CFSG.Open.StatedClassicalModel Y .PSL 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hY (by decide)
  have hmodel : CFSG.Models.LieModel Y .PSL 3 2 2 := ⟨hcl.1, Or.inl hcl⟩
  obtain ⟨-, ⟨g⟩⟩ := hgr Y .PSL 3 2 2 hmodel
  rw [Nat.card_congr g.toEquiv, Nat.card_prod]
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  simp [CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders]

private theorem isSylowOf_inf_of_isSubnormal {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P K N : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P K)
    (hN : CFSG.Open.IsSubnormal N K) :
    CFSG.ABGLocalTools.IsSylowOf p (P ⊓ N) N := by
  induction hN generalizing P with
  | refl H => simpa [inf_eq_left.mpr hP.le] using hP
  | @step N M K hNM hNorm hMK ih =>
      have hPM : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ M) M := ih hP
      have hMN : M ≤ Subgroup.normalizer (N : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNorm
      have h := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPM hNM hMN
      rwa [inf_assoc, inf_eq_right.mpr hNM] at h

private theorem isComponentOf_subgroupOf_of_le {G : Type} [Group G] {L H K : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L H) (hLK : L ≤ K) :
    CFSG.Open.IsComponentOf (L.subgroupOf K) (H.subgroupOf K) :=
  ⟨Subgroup.comap_mono hL.1, hL.2.1.comap K.subtype,
    hL.2.2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLK)⟩

private theorem centralizer_subgroupOf_eq {G : Type} [Group G] {Z K : Subgroup G} (hZK : Z ≤ K) :
    Subgroup.centralizer ((Z.subgroupOf K : Subgroup K) : Set ↥K) =
      (K ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf K := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    refine ⟨x.2, fun z hz => ?_⟩
    exact congrArg Subtype.val (hx ⟨z, hZK hz⟩ hz)
  · rintro ⟨-, hx⟩ z hz
    exact Subtype.ext (hx (z : G) hz)

private theorem dvd_three_of_dvd_fortyEight_of_odd {m : ℕ} (hdvd : m ∣ 48) (hodd : Odd m) :
    m ∣ 3 := by
  have hcop : m.Coprime (2 ^ 4) :=
    (Nat.coprime_pow_right_iff (by norm_num) m 2).mpr (Nat.coprime_two_right.mpr hodd)
  refine hcop.dvd_of_dvd_mul_left ?_
  rwa [show 2 ^ 4 * 3 = 48 by norm_num]

private theorem genFittingFStar_eq_top_of_isQuasisimple {M : Type} [Group M]
    (hM : CFSG.Open.IsQuasisimple M) : CFSG.Open.genFittingFStar M = ⊤ := by
  have hcomp : CFSG.Open.IsComponentOf (⊤ : Subgroup M) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.refl ⊤, hM.of_mulEquiv Subgroup.topEquiv⟩
  have hlayer : CFSG.Open.genFittingLayer M = ⊤ := by
    rw [CFSG.Open.genFittingLayer.eq_sSup]
    exact eq_top_iff.mpr (le_sSup hcomp)
  rw [CFSG.Open.genFittingFStar.eq_sup, hlayer, sup_top_eq]

private theorem three_dvd_card_center_of_pCoreOf_three_ne_bot {G : Type} [Group G] [Finite G]
    {X : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥X) (hZne : pCoreOf 3 X ≠ ⊥) :
    3 ∣ Nat.card (Subgroup.center ↥X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZleX : pCoreOf 3 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 3 X
  have hZle : (pCoreOf 3 X).subgroupOf X ≤ Subgroup.center ↥X :=
    pCoreOf_subgroupOf_le_center_of_quasisimple (p := 3) hq
  have h3Z : 3 ∣ Nat.card (pCoreOf 3 X) := by
    have hpg : IsPGroup 3 ↥(pCoreOf 3 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 X
    have : Nontrivial ↥(pCoreOf 3 X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZne
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(pCoreOf 3 X))
    exact (IsPGroup.dvd_orderOf hpg hz1).trans (orderOf_dvd_natCard z)
  have hcard : Nat.card ((pCoreOf 3 X).subgroupOf X) = Nat.card (pCoreOf 3 X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleX).toEquiv
  have h3sub : 3 ∣ Nat.card ((pCoreOf 3 X).subgroupOf X) := by
    rw [hcard]; exact h3Z
  have hdvd : Nat.card ((pCoreOf 3 X).subgroupOf X) ∣ Nat.card (Subgroup.center ↥X) := by
    have h := Subgroup.card_subgroup_dvd_card
      (((pCoreOf 3 X).subgroupOf X).subgroupOf (Subgroup.center ↥X))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv] at h
  exact h3sub.trans hdvd

private theorem card_center_eq_three_of_isSL3_or_isSU3 {G : Type} [Group G] [Finite G]
    (hgr : CFSG.Open.GriessAllModelsStatement) {X : Subgroup G}
    (h : IsSL3 ↥X 2 ∨ IsSU3 ↥X 3) (hO2 : pCoreOf 2 X = ⊥) (hZne : pCoreOf 3 X ≠ ⊥) :
    Nat.card (Subgroup.center ↥X) = 3 := by
  have hq : CFSG.Open.IsQuasisimple ↥X := h.elim (fun h => h.1) (fun h => h.1)
  have hodd : Odd (Nat.card (Subgroup.center ↥X)) :=
    odd_card_center_of_pCoreOf_two_eq_bot hO2
  have hdvd3 : Nat.card (Subgroup.center ↥X) ∣ 3 := by
    rcases h with hL | hU
    · have hperf : Group.IsPerfect ↥X := ⟨hL.1.1⟩
      have hdvd48 : Nat.card (Subgroup.center ↥X) ∣ 48 := by
        have h1 := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier
          (Q := ↥X) (S := ↥X ⧸ Subgroup.center ↥X) hperf (MulEquiv.refl _)
        rwa [natCard_griessHopfMultiplier_psl3_2_2 hgr hL.2] at h1
      exact dvd_three_of_dvd_fortyEight_of_odd hdvd48 hodd
    · exact UCK.u3Center_of_griess hgr ↥X 3 hU
  exact Nat.dvd_antisymm hdvd3 (three_dvd_card_center_of_pCoreOf_three_ne_bot hq hZne)

theorem pCoreOf_three_eq_bot_of_component {G : Type} [Group G] [Finite G]
    (D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G)
    (hK328 : K328) (hgr : CFSG.Open.GriessAllModelsStatement) {X H K Q : Subgroup G}
    (h87 : (IsSL3 ↥X 2 ∨ IsSU3 ↥X 3) ∧ pCoreOf 2 X = ⊥)
    (hHne : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKnotM : ¬ K ≤ D.M)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ D.M))
    (hQinf : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ X) X)
    (hGammaM : rankThreeGamma 1 3 (Q ⊓ X) ≤ D.M) : pCoreOf 3 X = ⊥ := by
  by_contra hZne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hqX : CFSG.Open.IsQuasisimple ↥X := h87.1.elim (fun h => h.1) (fun h => h.1)
  have hcenter3 : Nat.card (Subgroup.center ↥X) = 3 :=
    card_center_eq_three_of_isSL3_or_isSU3 hgr h87.1 h87.2 hZne
  have hZleX : pCoreOf 3 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 3 X
  have hZsub : (pCoreOf 3 X).subgroupOf X ≤ Subgroup.center ↥X :=
    pCoreOf_subgroupOf_le_center_of_quasisimple (p := 3) hqX
  have hZdiv : Nat.card (pCoreOf 3 X) ∣ Nat.card (Subgroup.center ↥X) := by
    have h := Subgroup.card_subgroup_dvd_card
      (((pCoreOf 3 X).subgroupOf X).subgroupOf (Subgroup.center ↥X))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZsub).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleX).toEquiv] at h
  have hZcard : Nat.card (pCoreOf 3 X) = 3 := by
    have h3Zp : 3 ∣ Nat.card (pCoreOf 3 X) := by
      have hpg : IsPGroup 3 ↥(pCoreOf 3 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 X
      have : Nontrivial ↥(pCoreOf 3 X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZne
      obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(pCoreOf 3 X))
      exact (IsPGroup.dvd_orderOf hpg hz1).trans (orderOf_dvd_natCard z)
    refine Nat.dvd_antisymm ?_ h3Zp
    rw [hcenter3] at hZdiv
    exact hZdiv
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKH : K ≤ H := hKcomp.1
  have hZleP : pCoreOf 3 X ≤ Q ⊓ X := by
    have hZpg : IsPGroup 3 ↥(pCoreOf 3 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 X
    obtain ⟨S, hS⟩ := hQinf.exists_sylow_eq_subgroupOf
    have : ((pCoreOf 3 X).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZleX).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 3) X)
    have hle : (pCoreOf 3 X).subgroupOf X ≤ (S : Subgroup ↥X) :=
      IsPGroup.le_sylow_of_normal (hZpg.of_equiv (Subgroup.subgroupOfEquivOfLe hZleX).symm) S
    rw [hS] at hle
    have hmap := Subgroup.map_mono (f := X.subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZleX,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right] at hmap
  have hZpg : IsPGroup 3 ↥(pCoreOf 3 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 X
  have hNZleM : Subgroup.normalizer (pCoreOf 3 X : Set G) ≤ D.M := by
    have hle := CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hZleP
      (one_le_pRank_of_isPGroup_ne_bot hZpg hZne)
    exact hle.trans hGammaM
  have hCKleM : K ⊓ Subgroup.centralizer (pCoreOf 3 X : Set G) ≤ D.M :=
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)).trans hNZleM
  have hXcen : X ≤ Subgroup.centralizer (pCoreOf 3 X : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzX : z ∈ X := hZleX hz
    have hcomm : (⟨z, hzX⟩ : ↥X) ∈ (pCoreOf 3 X).subgroupOf X := hz
    have hc := (Subgroup.mem_center_iff.mp (hZsub hcomm)) (⟨x, hx⟩ : ↥X)
    exact (congrArg Subtype.val hc).symm
  have hXcompCK : CFSG.Open.IsComponentOf X
      (K ⊓ Subgroup.centralizer (pCoreOf 3 X : Set G)) := by
    have hA : CFSG.Assembly.IsComponentOf X (H ⊓ D.M) :=
      CFSG.Assembly.isComponentOf_iff_open.mpr hXcomp
    have hB : CFSG.Assembly.IsComponentOf X
        (K ⊓ Subgroup.centralizer (pCoreOf 3 X : Set G)) :=
      CFSG.Assembly.IsComponentOf.of_le_of_le hA (le_inf hXK hXcen)
        (le_inf (inf_le_left.trans hKH) hCKleM)
    exact CFSG.Assembly.isComponentOf_iff_open.mp hB
  let Z' : Subgroup ↥K := (pCoreOf 3 X).subgroupOf K
  let X' : Subgroup ↥K := X.subgroupOf K
  let P' : Subgroup ↥K := (Q ⊓ X).subgroupOf K
  have hZleK : pCoreOf 3 X ≤ K := hZleX.trans hXK
  have hX'compC : CFSG.Open.IsComponentOf X' (Subgroup.centralizer (Z' : Set ↥K)) := by
    have h := isComponentOf_subgroupOf_of_le hXcompCK hXK
    rw [← centralizer_subgroupOf_eq (Z := pCoreOf 3 X) (K := K) hZleK] at h
    exact h
  have hZ'card : Nat.card Z' = 3 := by
    show Nat.card ↥((pCoreOf 3 X).subgroupOf K) = 3
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleK).toEquiv, hZcard]
  have hZ'leX' : Z' ≤ X' := Subgroup.subgroupOf_mono K hZleX
  have hX'center3 : Nat.card (Subgroup.center ↥X') = 3 := by
    show Nat.card (Subgroup.center ↥(X.subgroupOf K)) = 3
    have e : ↥X ≃* ↥(X.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hXK).symm
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective, hcenter3]
  have hX'Lie : CFSG.Blueprint.LieModel (↥X' ⧸ Subgroup.center ↥X') .PSL 3 2 2 ∨
      CFSG.Blueprint.LieModel (↥X' ⧸ Subgroup.center ↥X') .PSU 3 2 3 := by
    rcases h87.1 with hL | hU
    · left
      have e : ↥X' ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXK
      have hq : (↥X' ⧸ Subgroup.center ↥X') ≃* (↥X ⧸ Subgroup.center ↥X) :=
        QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
      exact CFSG.Blueprint.LieModel.of_mulEquiv hq.symm (t := .PSL) (n := 3) (p := 2) (f := 2) hL.2
    · right
      have e : ↥X' ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXK
      have hq : (↥X' ⧸ Subgroup.center ↥X') ≃* (↥X ⧸ Subgroup.center ↥X) :=
        QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
      exact CFSG.Blueprint.LieModel.of_mulEquiv hq.symm (t := .PSU) (n := 3) (p := 2) (f := 3) hU.2
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf 3 P' X' := by
    show CFSG.ABGLocalTools.IsSylowOf 3 ((Q ⊓ X).subgroupOf K) (X.subgroupOf K)
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff K]
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_right.trans hXK),
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXK]
  have hm3K : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) hKH).trans hHr
  have hKne_top : K ≠ ⊤ := fun htop => hHne (top_le_iff.mp (htop ▸ hKH))
  have hFstarK : CFSG.Open.IsQuasisimple ↥(CFSG.Open.genFittingFStar ↥K) := by
    rw [genFittingFStar_eq_top_of_isQuasisimple hKq]
    exact hKq.of_mulEquiv Subgroup.topEquiv
  have hKGroup : CFSG.Open.IsKGroup (↥(CFSG.Open.genFittingFStar ↥K) ⧸
      Subgroup.center ↥(CFSG.Open.genFittingFStar ↥K)) := by
    rw [genFittingFStar_eq_top_of_isQuasisimple hKq]
    have hbase : CFSG.Open.IsKGroup (↥K ⧸ Subgroup.center ↥K) :=
      (CFSG.Open.IsKProper.isKGroup D.standing.kProper K hKne_top).quotient _
    let e : (↥(⊤ : Subgroup ↥K) ⧸ Subgroup.center ↥(⊤ : Subgroup ↥K)) ≃*
        (↥K ⧸ Subgroup.center ↥K) :=
      QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)
    exact CFSG.Open.IsKGroup.of_injective hbase e e.injective
  have hX'le : X' ≤ Subgroup.centralizer (Z' : Set ↥K) ⊓ CFSG.Open.genFittingFStar ↥K := by
    rw [genFittingFStar_eq_top_of_isQuasisimple hKq, inf_top_eq]
    exact hX'compC.1
  have hX'sub : (X'.subgroupOf (Subgroup.centralizer (Z' : Set ↥K) ⊓
      CFSG.Open.genFittingFStar ↥K)).IsSubnormal := by
    rw [genFittingFStar_eq_top_of_isQuasisimple hKq, inf_top_eq]
    exact CFSG.Open.IsSubnormal.subgroupOf hX'compC.2.1
  have hK328res : rankThreeGamma 1 3 P' = ⊤ :=
    hK328 ↥K hFstarK hKGroup hm3K Z' X' P' hZ'card hZ'leX' hX'le hX'sub
      hX'compC.2.2 hX'center3 hX'Lie hP'syl
  have hKleM : K ≤ D.M := by
    have hle : rankThreeGamma 1 3 P' ≤ (D.M ⊓ K).subgroupOf K := by
      refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
      intro Q' hQ'P' hQ'rank x hx
      have hQ''le : Q'.map K.subtype ≤ Q ⊓ X := by
        calc Q'.map K.subtype ≤ P'.map K.subtype := Subgroup.map_mono hQ'P'
          _ = Q ⊓ X := by
              show ((Q ⊓ X).subgroupOf K).map K.subtype = Q ⊓ X
              rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_right.trans hXK)]
      have hQ''rank : 1 ≤ CFSG.Open.pRank 3 (Q'.map K.subtype) :=
        hQ'rank.trans (CFSG.SectionRank.pRank_le_map (by norm_num) K.subtype
          K.subtype_injective Q')
      have hxnorm : x.1 ∈ Subgroup.normalizer (Q'.map K.subtype : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
          rw [← hqy]
          exact Subgroup.mem_map.mpr ⟨x * q * x⁻¹,
            (Subgroup.mem_normalizer_iff.mp hx q).mp hq, rfl⟩
        · intro hy
          obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
          have hxinv : x⁻¹ ∈ Subgroup.normalizer (Q' : Set ↥K) := Subgroup.inv_mem _ hx
          have hq' : x⁻¹ * q * x ∈ Q' := by
            simpa using (Subgroup.mem_normalizer_iff.mp hxinv q).mp hq
          refine Subgroup.mem_map.mpr ⟨x⁻¹ * q * x, hq', ?_⟩
          have h1 : K.subtype (x⁻¹ * q * x) = (↑x)⁻¹ * K.subtype q * ↑x := by
            simp [map_mul, map_inv]
          rw [h1, hqy]
          group
      have hmem : x.1 ∈ D.M :=
        hGammaM (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
          hQ''le hQ''rank hxnorm)
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hmem, x.2⟩
    have htop : (⊤ : Subgroup ↥K) ≤ (D.M ⊓ K).subgroupOf K := hK328res ▸ hle
    intro k hk
    have hk' : (⟨k, hk⟩ : ↥K) ∈ (D.M ⊓ K).subgroupOf K := htop (Subgroup.mem_top _)
    exact (Subgroup.mem_subgroupOf.mp hk').1
  exact hKnotM hKleM

theorem r877_of_inputs {G : Type} [Group G] [Finite G]
    (D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G)
    (hK328 : K328) (hgr : CFSG.Open.GriessAllModelsStatement)
    (hSg : UC6S846.SigmaStd D) (h870 : R870 D) (h873 : R873 D) (h874 : R874 D) (h875 : R875 D)
    (h875c : R875Comp D) : R877 D := by
  intro L X H h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h87 := h873 L X H h
  obtain ⟨K, hKcomp, hXK, hKnotM⟩ := h875 L X H h
  have hXcomp : CFSG.Open.IsComponentOf X (H ⊓ D.M) := h875c L X H h
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 3) (K := H ⊓ D.M)
  have hQinf : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ X) X :=
    isSylowOf_inf_of_isSubnormal hQ hXcomp.2.1
  obtain ⟨hQH, hGammaM⟩ := h874 L X H h Q hQ hQinf
  have hHr : CFSG.Open.pRank 3 H ≤ 3 := by
    have h3X : 1 < CFSG.Open.pRank 3 X := by
      have := two_le_pRank_three_of_isSL3_or_isSU3 h87.1
      omega
    have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
      pRank_le_three_of_minCex hSg h870 h Nat.prime_three (by norm_num) h3X
    calc CFSG.Open.pRank 3 H = CFSG.Open.pRank 3 Q :=
          (CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow
            Nat.prime_three hQH).symm
      _ ≤ CFSG.Open.pRank 3 D.M :=
          CFSG.SectionRank.pRank_mono (by norm_num) (hQ.le.trans inf_le_right)
      _ ≤ 3 := hM3
  exact pCoreOf_three_eq_bot_of_component D hK328 hgr h87 h.mem.1.1 hHr hKcomp hXK hKnotM hXcomp
    hQinf hGammaM

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
