module

public import CFSG.RankThree.PartTwo.Sec16.Item163U35CE
import CFSG.RankThree.PartTwo.Sec16.Item163U35Two
public import CFSG.RankThree.PartTwo.KFacts.KS163U35Klein
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418IndexTwo

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

private theorem isSimpleGroup_card_of_mulEquiv_alt7 {J : Subgroup G}
    (hJ : Nonempty (↥J ≃* alternatingGroup (Fin 7))) :
    IsSimpleGroup ↥J ∧ Nat.card J = 2520 ∧ 3 ∣ Nat.card J := by
  obtain ⟨e⟩ := hJ
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  haveI : IsSimpleGroup ↥J := e.isSimpleGroup
  have hcard : Nat.card J = 2520 := by
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  exact ⟨inferInstance, hcard, by rw [hcard]; norm_num⟩

private theorem pCore_eq_bot_of_mulEquiv_alt7 {J : Subgroup G}
    (hJ : Nonempty (↥J ≃* alternatingGroup (Fin 7))) :
    CFSG.pCore 2 ↥J = ⊥ := by
  obtain ⟨hsimple, hcard, h3⟩ := isSimpleGroup_card_of_mulEquiv_alt7 hJ
  haveI := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥J) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup (p := 2) (G := ↥J)
    rw [h] at hp
    have hJ2 : IsPGroup 2 ↥J := hp.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := hJ2.exists_card_eq
    have hdvd : 3 ∣ 2 ^ n := hn ▸ h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)

theorem mem_scriptY4_of_mulEquiv {A : Subgroup G} {LB : Subgroup G → Subgroup G} {J : Subgroup G}
    (hJ : Nonempty (↥J ≃* alternatingGroup (Fin 7)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hJΔ : J ≤ delta A LB J)
    (htop : J ≠ ⊤) : J ∈ scriptY4 A LB := by
  obtain ⟨e⟩ := hJ
  obtain ⟨hsimple, hcard, h3⟩ := isSimpleGroup_card_of_mulEquiv_alt7 ⟨e⟩
  haveI := hsimple
  have hJres : J ≤ oPrimeResidualOf 3 J := by
    obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hxG3 : (x : G) ^ 3 = 1 := by
      rw [← hx3, ← Subgroup.orderOf_coe x]
      exact pow_orderOf_eq_one (x : G)
    have hxmem : (x : G) ∈ oPrimeResidualOf 3 J :=
      Proof1515Res.mem_oRes3_of_pow x.2 (k := 1) (by simpa using hxG3)
    have hx1 : (x : G) ≠ 1 := by
      intro h1
      have h1' : orderOf x = 1 := by rw [← Subgroup.orderOf_coe x, h1, orderOf_one]
      omega
    haveI : ((oPrimeResidualOf 3 J).subgroupOf J).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (Proof1515Res.le_normalizer_oRes3 Subgroup.le_normalizer)
    have hne : (oPrimeResidualOf 3 J).subgroupOf J ≠ ⊥ := by
      intro hbot
      have hmem : (⟨(x : G), x.2⟩ : ↥J) ∈ (oPrimeResidualOf 3 J).subgroupOf J :=
        Subgroup.mem_subgroupOf.mpr hxmem
      rw [hbot] at hmem
      exact hx1 (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))
    have htop' : (oPrimeResidualOf 3 J).subgroupOf J = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((oPrimeResidualOf 3 J).subgroupOf J) with h | h
      · exact absurd h hne
      · exact h
    intro y hy
    exact Subgroup.mem_subgroupOf.mp (htop' ▸ Subgroup.mem_top (⟨y, hy⟩ : ↥J))
  have hqJ : CFSG.IsQuasisimple ↥J :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      CFSG.Quasithin.EmptyFaithfulMultiple.Insp15418.isQuasisimple_alternating_seven
  have hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv ?_ hqJ
    exact ((QuotientGroup.quotientMulEquivOfEq (pCore_eq_bot_of_mulEquiv_alt7 ⟨e⟩)).trans
      QuotientGroup.quotientBot).symm
  exact ⟨⟨htop, hAJ⟩, le_antisymm hJres (Subgroup.map_subtype_le _),
    le_antisymm hJΔ (delta_le J), hq⟩

private theorem inf_pCoreOf_eq_bot_of_mulEquiv {J X : Subgroup G}
    (hJ : Nonempty (↥J ≃* alternatingGroup (Fin 7))) (hJX : J ≤ X) :
    J ⊓ CFSG.Open.pCoreOf 2 X = ⊥ := by
  obtain ⟨hsimpleJ, hcardJ, h3J⟩ := isSimpleGroup_card_of_mulEquiv_alt7 hJ
  haveI := hsimpleJ
  have hJN : J ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    hJX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have hsubJN : (CFSG.Open.pCoreOf 2 X).subgroupOf J =
      (J ⊓ CFSG.Open.pCoreOf 2 X).subgroupOf J := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  haveI : ((J ⊓ CFSG.Open.pCoreOf 2 X).subgroupOf J).Normal := by
    rw [← hsubJN]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hJN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((J ⊓ CFSG.Open.pCoreOf 2 X).subgroupOf J) with h | h
  · rw [← le_bot_iff]
    intro y hy
    have hy' : (⟨y, hy.1⟩ : ↥J) ∈ (J ⊓ CFSG.Open.pCoreOf 2 X).subgroupOf J :=
      Subgroup.mem_subgroupOf.mpr hy
    rw [h] at hy'
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hy')
  · exfalso
    have hJO : J ≤ CFSG.Open.pCoreOf 2 X := by
      intro y hy
      have hy' : (⟨y, hy⟩ : ↥J) ∈ (J ⊓ CFSG.Open.pCoreOf 2 X).subgroupOf J :=
        h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy')).2
    have hJ2 : IsPGroup 2 J := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hJO
    obtain ⟨n, hn⟩ := hJ2.exists_card_eq
    have hdvd : 3 ∣ 2 ^ n := hn ▸ h3J
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)

private theorem oRes_sup_data {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {J D : Subgroup G} (hJ4 : J ∈ scriptY4 A LB)
    (hJ : Nonempty (↥J ≃* alternatingGroup (Fin 7))) (hDQ : D ∈ scriptQ A LB)
    (hD2 : IsPGroup 2 D) (hJD : J ≤ Subgroup.normalizer (D : Set G)) :
    A ≤ Subgroup.normalizer (oPrimeResidualOf 3 (J ⊔ D) : Set G) ∧
      oPrimeResidualOf 3 (J ⊔ D) = oPrimeResidualOf 3 (oPrimeResidualOf 3 (J ⊔ D)) ∧
      oPrimeResidualOf 3 (J ⊔ D) = delta A LB (oPrimeResidualOf 3 (J ⊔ D)) ∧
      oPrimeResidualOf 3 (J ⊔ D) =
        J ⊔ CFSG.Open.pCoreOf 2 (oPrimeResidualOf 3 (J ⊔ D)) ∧
      J ⊓ CFSG.Open.pCoreOf 2 (oPrimeResidualOf 3 (J ⊔ D)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := J ⊔ D with hY
  set X : Subgroup G := oPrimeResidualOf 3 Y with hX
  have hJY : J ≤ Y := le_sup_left
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := hDQ.1.2.2
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hJ4.1.2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    (le_inf hAJ hAD).trans (Subgroup.inf_normalizer_le_normalizer_sup J D)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := Proof1515Res.le_normalizer_oRes3 hAY
  have hJX : J ≤ X := hJ4.2.1.le.trans (oPrimeResidualOf_mono 3 hJY)
  have hXY : X ≤ Y := Subgroup.map_subtype_le _
  have hXYN : Y ≤ Subgroup.normalizer (D : Set G) := sup_le hJD Subgroup.le_normalizer
  have hXcov : X ≤ J ⊔ (X ⊓ D) := by
    intro x hx
    have hx' : x ∈ ((J ⊔ D : Subgroup G) : Set G) := hXY hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right J D hJD] at hx'
    obtain ⟨j, hj, d, hd, rfl⟩ := hx'
    have hdX : d ∈ X := by
      have := mul_mem (inv_mem (hJX hj)) hx
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right ⟨hdX, hd⟩)
  have hXDQ : X ⊓ D ∈ scriptQ A LB :=
    mem_scriptQ_of_le hDQ inf_le_right (Late.le_normalizer_inf hAX hAD)
  have hXΔ : X = delta A LB X := by
    refine le_antisymm (hXcov.trans (sup_le ?_ ?_)) (delta_le _)
    · exact hJ4.2.2.1.le.trans (delta_mono hJX)
    · exact le_delta hXDQ inf_le_left
  have hXN : X ≤ Subgroup.normalizer ((X ⊓ D : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (hXY.trans hXYN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hinfD : X ⊓ D ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hXN
      (hD2.to_le inf_le_right)
  have hXeq : X = J ⊔ CFSG.Open.pCoreOf 2 X := by
    refine le_antisymm (hXcov.trans (sup_le_sup_left hinfD J)) ?_
    exact sup_le hJX (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have hJinf : J ⊓ CFSG.Open.pCoreOf 2 X = ⊥ := inf_pCoreOf_eq_bot_of_mulEquiv hJ hJX
  exact ⟨hAX, (Proof1515Res.oRes3_idem Y).symm, hXΔ, hXeq, hJinf⟩

theorem mem_scriptY4_oRes_sup_of_mulEquiv {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {J D : Subgroup G} (hJ4 : J ∈ scriptY4 A LB)
    (hJ : Nonempty (↥J ≃* alternatingGroup (Fin 7))) (hDQ : D ∈ scriptQ A LB)
    (hD2 : IsPGroup 2 D) (hJD : J ≤ Subgroup.normalizer (D : Set G)) (htop : J ⊔ D ≠ ⊤) :
    oPrimeResidualOf 3 (J ⊔ D) ∈ scriptY4 A LB ∧
      Nonempty (↥(oPrimeResidualOf 3 (J ⊔ D)) ⧸
        CFSG.pCore 2 ↥(oPrimeResidualOf 3 (J ⊔ D)) ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨e⟩ := hJ
  obtain ⟨hAX, hXres, hXΔ, hXeq, hJinf⟩ := oRes_sup_data hJ4 ⟨e⟩ hDQ hD2 hJD
  set X : Subgroup G := oPrimeResidualOf 3 (J ⊔ D) with hX
  have hJX : J ≤ X := hJ4.2.1.le.trans (oPrimeResidualOf_mono 3 le_sup_left)
  have hXY : X ≤ J ⊔ D := Subgroup.map_subtype_le _
  let N : Subgroup G := CFSG.Open.pCoreOf 2 X
  have hNX : N ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hJN : J ≤ Subgroup.normalizer (N : Set G) :=
    hJX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  haveI : (N.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  let f : ↥J →* ↥X ⧸ N.subgroupOf X :=
    (QuotientGroup.mk' (N.subgroupOf X)).comp (Subgroup.inclusion hJX)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf X) q
    have hx : (x : G) ∈ ((J ⊔ N : Subgroup G) : Set G) := by
      rw [← hXeq]; exact x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right J N hJN] at hx
    obtain ⟨j, hj, n, hn, hjn⟩ := hx
    have hnX : n ∈ X := hNX hn
    refine ⟨⟨j, hj⟩, ?_⟩
    have hf : f ⟨j, hj⟩ = QuotientGroup.mk' (N.subgroupOf X)
        (Subgroup.inclusion hJX ⟨j, hj⟩) := rfl
    rw [hf, QuotientGroup.mk'_eq_mk']
    exact ⟨⟨n, hnX⟩, hn, Subtype.ext (by simpa using hjn)⟩
  have hker : f.ker = ⊥ := by
    refine Subgroup.ext fun y => ?_
    rw [MonoidHom.mem_ker]
    have hfy : f y = QuotientGroup.mk' (N.subgroupOf X) (Subgroup.inclusion hJX y) := rfl
    rw [hfy, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hyN
      have hyInf : (y : G) ∈ J ⊓ N := ⟨y.2, hyN⟩
      rw [hJinf] at hyInf
      exact Subtype.ext (Subgroup.mem_bot.mp hyInf)
    · intro hy
      have hy1 : ((Subgroup.inclusion hJX) y : G) = 1 := by
        rw [Subgroup.mem_bot.mp hy]; rfl
      rw [hy1]
      exact N.one_mem
  have hiso : ↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 7) :=
    ((QuotientGroup.quotientMulEquivOfEq (CFSG.openPCoreOf_subgroupOf 2 X)).symm.trans
      ((QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans
          (QuotientGroup.quotientBot.trans e))))
  have hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv hiso.symm
      CFSG.Quasithin.EmptyFaithfulMultiple.Insp15418.isQuasisimple_alternating_seven
  have hXtop : X ≠ ⊤ := by
    intro hXt
    refine htop (top_le_iff.mp ?_)
    rw [← hXt]
    exact hXY
  exact ⟨⟨⟨hXtop, hAX⟩, hXres, hXΔ, hq⟩, ⟨hiso⟩⟩

theorem exists_mem_scriptY0Star_of_mulEquiv {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h155 : Item155 A LB) {J D : Subgroup G}
    (hJ4 : J ∈ scriptY4 A LB) (hJ : Nonempty (↥J ≃* alternatingGroup (Fin 7)))
    (hDQ : D ∈ scriptQ A LB) (hD2 : IsPGroup 2 D) (hD1 : D ≠ ⊥)
    (hJD : J ≤ Subgroup.normalizer (D : Set G)) (htop : J ⊔ D ≠ ⊤) :
    ∃ K ∈ scriptY0Star A LB, J ≤ K ∧
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (J ⊔ D) : Subgroup G) : Set G),
        delta A LB M ≤ Subgroup.normalizer (K : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y₃ : Subgroup G := J ⊔ D with hY₃
  set X₃ : Subgroup G := oPrimeResidualOf 3 Y₃ with hX₃
  obtain ⟨hX4, ⟨χ⟩⟩ := mem_scriptY4_oRes_sup_of_mulEquiv hJ4 hJ hDQ hD2 hJD htop
  have htopY : Y₃ ≠ ⊤ := by rw [hY₃]; exact htop
  have hAY : A ≤ Subgroup.normalizer (Y₃ : Set G) :=
    (le_inf hJ4.1.2 hDQ.1.2.2).trans
      (Subgroup.inf_normalizer_le_normalizer_sup J D)
  have hDle : D ≤ CFSG.Open.pCoreOf 2 Y₃ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (by rw [hY₃]; exact le_sup_right) (sup_le hJD Subgroup.le_normalizer) hD2
  have hO2ne : CFSG.Open.pCoreOf 2 Y₃ ≠ ⊥ := fun h0 => hD1 (le_bot_iff.mp (h0 ▸ hDle))
  have hY3Δ : Y₃ = delta A LB Y₃ := by
    refine le_antisymm (sup_le ?_ ?_) (delta_le _)
    · exact hJ4.2.2.1.le.trans (delta_mono (by rw [hY₃]; exact le_sup_left))
    · exact le_delta hDQ (by rw [hY₃]; exact le_sup_right)
  have hY3 : Y₃ ∈ scriptY3 A LB := ⟨⟨⟨htopY, hAY⟩, hO2ne⟩, hY3Δ⟩
  have hJX : J ≤ X₃ := hJ4.2.1.le.trans (oPrimeResidualOf_mono 3 (by rw [hY₃]; exact le_sup_left))
  have hY3eq : Y₃ = oPrimeResidualOf 3 Y₃ ⊔ CFSG.Open.pCoreOf 2 Y₃ :=
    le_antisymm (sup_le (hJX.trans le_sup_left) (hDle.trans le_sup_right))
      (sup_le (Subgroup.map_subtype_le _) ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y₃)))
  have hcard7 : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  have hcard5 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have homg : omg155 A X₃ := by
    refine Or.inl ⟨?_, ?_⟩
    · rintro ⟨n, -, hiso⟩
      exact Proof1614.not_isoLThreePi_a7 2 n (Proof169.isoLThreePi_of_mulEquiv χ hiso)
    · refine ⟨fun e5 => ?_⟩
      have h1 : Nat.card (↥X₃ ⧸ CFSG.pCore 2 ↥X₃) = 2520 := by
        rw [Nat.card_congr χ.toEquiv, hcard7]
      have h2 : Nat.card (↥X₃ ⧸ CFSG.pCore 2 ↥X₃) = 60 := by
        rw [Nat.card_congr e5.toEquiv, hcard5]
      exact absurd (h1.symm.trans h2) (by norm_num)
  obtain ⟨hfirst, hsecond⟩ := h155 Y₃ hY3 hX4 hY3eq
  obtain ⟨K, hK⟩ := hfirst homg
  refine ⟨K, hK.1, hJX.trans hK.2.1, ?_⟩
  intro M hM
  exact hsecond K hK (Or.inl homg) M hM

variable {A : Subgroup G} {c : G} {L Y : Subgroup G}

namespace Conf684

private theorem le_normalizer_of_klein {U T V : Subgroup G}
    (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hAc : A ≤ Subgroup.centralizer ({c} : Set G))
    (hV : V = T ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) :
    A ≤ Subgroup.normalizer (V : Set G) := by
  rw [hV]
  have h1 : A ≤ Subgroup.normalizer (T : Set G) ⊓
      Subgroup.normalizer (Subgroup.normalizer (U : Set G) : Set G) :=
    le_inf hAT (hAU.trans Subgroup.le_normalizer)
  exact (le_inf (h1.trans Subgroup.inf_normalizer_le_normalizer_inf)
    (hAc.trans Subgroup.le_normalizer)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem klein_scriptQ (h : Conf684 A c L Y) (hK2 : KFacts.KS163U35KleinGen)
    {K₁ K₂ T₁ T₂ U V₁ V₂ : Subgroup G} (hmax : MaxCE684 A L K₁ K₂ T₁ T₂)
    (hU : U = T₁ ⊓ T₂)
    (hV₁ : V₁ = T₁ ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({c} : Set G))
    (hV₂ : V₂ = T₂ ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({c} : Set G))
    (hc₁ : ¬ V₁ ≤ U) (hc₂ : ¬ V₂ ≤ U) :
    U ∈ scriptQ A (lB A) ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
      V₁ ∈ scriptQ A (lB A) ∧ V₂ ∈ scriptQ A (lB A) ∧
      V₁ ≤ Subgroup.normalizer (U : Set G) ∧ V₂ ≤ Subgroup.normalizer (U : Set G) ∧
      V₁ ≤ L ∧ V₂ ≤ L ∧ V₁ ≤ T₁ ∧ V₂ ≤ T₂ ∧
      A ≤ Subgroup.normalizer (V₁ : Set G) ∧ A ≤ Subgroup.normalizer (V₂ : Set G) ∧
      Nonempty (↥(V₁ ⊔ V₂) ≃* alternatingGroup (Fin 7)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁Q : T₁ ∈ scriptQ A (lB A) := hmax.1.zeta₁.2.2.prop.1.1
  have hT₂Q : T₂ ∈ scriptQ A (lB A) := hmax.1.zeta₂.2.2.prop.1.1
  have hT₁2 : IsPGroup 2 T₁ := isPGroup_of_mem_scriptQPi Nat.prime_two hmax.1.zeta₁.2.2.prop
  have hT₂2 : IsPGroup 2 T₂ := isPGroup_of_mem_scriptQPi Nat.prime_two hmax.1.zeta₂.2.2.prop
  have hAT₁ : A ≤ Subgroup.normalizer (T₁ : Set G) := (mem_scriptQ_iff.mp hT₁Q).2.1
  have hAT₂ : A ≤ Subgroup.normalizer (T₂ : Set G) := (mem_scriptQ_iff.mp hT₂Q).2.1
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    rw [hU]; exact Late.le_normalizer_inf hAT₁ hAT₂
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := h.sec15R.toSec13Data.A_le_centralizer
  have hUQ : U ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hT₁Q (hU ▸ inf_le_left) hAU
  have hU2 : IsPGroup 2 U := by rw [hU]; exact hT₁2.to_le inf_le_left
  have hU1 : U ≠ ⊥ := by rw [hU]; exact hmax.1.ne_bot
  have hV₁T₁ : V₁ ≤ T₁ := by rw [hV₁]; exact inf_le_left.trans inf_le_left
  have hV₂T₂ : V₂ ≤ T₂ := by rw [hV₂]; exact inf_le_left.trans inf_le_left
  have hV₁N : V₁ ≤ Subgroup.normalizer (U : Set G) := by
    rw [hV₁]; exact inf_le_left.trans inf_le_right
  have hV₂N : V₂ ≤ Subgroup.normalizer (U : Set G) := by
    rw [hV₂]; exact inf_le_left.trans inf_le_right
  have hV₁c : V₁ ≤ Subgroup.centralizer ({c} : Set G) := by rw [hV₁]; exact inf_le_right
  have hV₂c : V₂ ≤ Subgroup.centralizer ({c} : Set G) := by rw [hV₂]; exact inf_le_right
  have hAV₁ : A ≤ Subgroup.normalizer (V₁ : Set G) :=
    le_normalizer_of_klein hAT₁ hAU hAc hV₁
  have hAV₂ : A ≤ Subgroup.normalizer (V₂ : Set G) :=
    le_normalizer_of_klein hAT₂ hAU hAc hV₂
  have hV₁Q : V₁ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hT₁Q hV₁T₁ hAV₁
  have hV₂Q : V₂ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hT₂Q hV₂T₂ hAV₂
  have hV₁1 : V₁ ≠ ⊥ := fun hbot => hc₁ (by rw [hbot]; exact bot_le)
  have hV₂1 : V₂ ≠ ⊥ := fun hbot => hc₂ (by rw [hbot]; exact bot_le)
  have hV₁L : V₁ ≤ L :=
    Conf684.le_of_le_centralizer h (hT₁2.to_le hV₁T₁) hV₁c (inf_le_left.trans hAV₁)
  have hV₂L : V₂ ≤ L :=
    Conf684.le_of_le_centralizer h (hT₂2.to_le hV₂T₂) hV₂c (inf_le_left.trans hAV₂)
  have hne : V₁ ≠ V₂ := by
    intro heq
    have hV₁T₂ : V₁ ≤ T₂ := by rw [heq]; exact hV₂T₂
    exact hc₁ (by rw [hU]; exact le_inf hV₁T₁ hV₁T₂)
  have hJ : Nonempty (↥(V₁ ⊔ V₂) ≃* alternatingGroup (Fin 7)) :=
    Conf684.nonempty_sup_mulEquiv h hK2 hV₁L hV₂L (hT₁2.to_le hV₁T₁) (hT₂2.to_le hV₂T₂)
      (inf_le_left.trans hAV₁) (inf_le_left.trans hAV₂) hV₁1 hV₂1 hne
  exact ⟨hUQ, hU2, hU1, hV₁Q, hV₂Q, hV₁N, hV₂N, hV₁L, hV₂L, hV₁T₁, hV₂T₂, hAV₁, hAV₂, hJ⟩

private theorem klein_scriptY4 (h : Conf684 A c L Y) {U V₁ V₂ : Subgroup G}
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hV₁Q : V₁ ∈ scriptQ A (lB A)) (hV₂Q : V₂ ∈ scriptQ A (lB A))
    (hV₁N : V₁ ≤ Subgroup.normalizer (U : Set G))
    (hV₂N : V₂ ≤ Subgroup.normalizer (U : Set G))
    (hV₁L : V₁ ≤ L) (hV₂L : V₂ ≤ L)
    (hAV₁ : A ≤ Subgroup.normalizer (V₁ : Set G))
    (hAV₂ : A ≤ Subgroup.normalizer (V₂ : Set G))
    (hJ : Nonempty (↥(V₁ ⊔ V₂) ≃* alternatingGroup (Fin 7))) :
    V₁ ⊔ V₂ ∈ scriptY4 A (lB A) ∧ V₁ ⊔ V₂ ≤ L ∧
      V₁ ⊔ V₂ ≤ Subgroup.normalizer (U : Set G) ∧ V₁ ⊔ V₂ ⊔ U ≠ ⊤ := by
  have hAJ : A ≤ Subgroup.normalizer ((V₁ ⊔ V₂ : Subgroup G) : Set G) :=
    (le_inf hAV₁ hAV₂).trans (Subgroup.inf_normalizer_le_normalizer_sup V₁ V₂)
  have hJΔ : V₁ ⊔ V₂ ≤ delta A (lB A) (V₁ ⊔ V₂) :=
    sup_le (le_delta hV₁Q le_sup_left) (le_delta hV₂Q le_sup_right)
  have hJN : V₁ ⊔ V₂ ≤ Subgroup.normalizer (U : Set G) := sup_le hV₁N hV₂N
  have hNUt : Subgroup.normalizer (U : Set G) ≠ ⊤ :=
    Sec14.normalizer_ne_top_of_isPGroup h.sec15R.isSimpleGroup h.sec15R.nonabelian hU1 hU2
  have hJUt : V₁ ⊔ V₂ ⊔ U ≠ ⊤ := by
    intro htop
    have h1 : (⊤ : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
      rw [← htop]; exact sup_le hJN Subgroup.le_normalizer
    exact hNUt (top_le_iff.mp h1)
  have hJtop : V₁ ⊔ V₂ ≠ ⊤ := by
    intro htop
    exact hJUt (by rw [htop]; exact top_sup_eq U)
  exact ⟨mem_scriptY4_of_mulEquiv hJ hAJ hJΔ hJtop, sup_le hV₁L hV₂L, hJN, hJUt⟩

private theorem exists_star_of_sup {K U V T M : Subgroup G}
    (hE27 : Late.IsE27 A) (h146 : Item146 A (lB A)) (hK : K ∈ scriptY0Star A (lB A))
    (hMeets : MeetsY4 A (lB A) L K)
    (hΔK : delta A (lB A) M ≤ Subgroup.normalizer (K : Set G))
    (hVQ : V ∈ scriptQ A (lB A)) (hUQ : U ∈ scriptQ A (lB A))
    (hVU : V ≤ Subgroup.normalizer (U : Set G)) (hVM : V ≤ M) (hUM : U ≤ M)
    (hVT : V ≤ T) (hUT : U ≤ T) (hT2 : IsPGroup 2 T) (hlt : V ⊔ U ≠ U) :
    ∃ T₃ : Subgroup G, IsZeta A L T₃ K ∧ V ⊔ U ≤ T₃ ∧
      Nat.card U < Nat.card (T ⊓ T₃ : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNQ : V ⊔ U ∈ scriptQ A (lB A) :=
    sup_mem_scriptQ_of_item146 hE27 h146 hVQ hUQ hVU
  have hNM : V ⊔ U ≤ M := sup_le hVM hUM
  have hNNK : V ⊔ U ≤ Subgroup.normalizer (K : Set G) := (le_delta hNQ hNM).trans hΔK
  have hN2 : IsPGroup 2 (V ⊔ U : Subgroup G) := hT2.to_le (sup_le hVT hUT)
  have hNpi : V ⊔ U ∈ scriptQPi A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2) :=
    ⟨⟨hNQ, hNNK⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hN2⟩
  obtain ⟨T₃, hleT₃, hT₃max⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2)))
    (a := V ⊔ U) hNpi
  refine ⟨T₃, ⟨hK, hMeets, hT₃max⟩, hleT₃, ?_⟩
  have hltU : Nat.card U < Nat.card (V ⊔ U : Subgroup G) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_right (fun heq => hlt heq.symm))
  have hle : V ⊔ U ≤ T ⊓ T₃ := le_inf (sup_le hVT hUT) hleT₃
  exact hltU.trans_le (Subgroup.card_le_of_le hle)

theorem false_of_maxCE684_of_not_le (h : Conf684 A c L Y) (hK2 : KFacts.KS163U35KleinGen)
    {K₁ K₂ T₁ T₂ : Subgroup G} (hmax : MaxCE684 A L K₁ K₂ T₁ T₂)
    (hc₁ : ¬ T₁ ⊓ Subgroup.normalizer ((T₁ ⊓ T₂ : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) ≤ T₁ ⊓ T₂)
    (hc₂ : ¬ T₂ ⊓ Subgroup.normalizer ((T₁ ⊓ T₂ : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) ≤ T₁ ⊓ T₂) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := T₁ ⊓ T₂ with hU
  set V₁ : Subgroup G := T₁ ⊓ Subgroup.normalizer (U : Set G) ⊓
    Subgroup.centralizer ({c} : Set G) with hV₁
  set V₂ : Subgroup G := T₂ ⊓ Subgroup.normalizer (U : Set G) ⊓
    Subgroup.centralizer ({c} : Set G) with hV₂
  obtain ⟨hUQ, hU2, hU1, hV₁Q, hV₂Q, hV₁N, hV₂N, hV₁L, hV₂L, hV₁T₁, hV₂T₂,
    hAV₁, hAV₂, hJ⟩ := klein_scriptQ h hK2 hmax hU hV₁ hV₂ hc₁ hc₂
  obtain ⟨hJ4, hJL, hJN, hJUt⟩ :=
    klein_scriptY4 h hU1 hU2 hV₁Q hV₂Q hV₁N hV₂N hV₁L hV₂L hAV₁ hAV₂ hJ
  have hlt₁ : V₁ ⊔ U ≠ U := by
    intro heq
    exact hc₁ (by rw [← heq]; exact le_sup_left)
  have hlt₂ : V₂ ⊔ U ≠ U := by
    intro heq
    exact hc₂ (by rw [← heq]; exact le_sup_left)
  obtain ⟨K, hK, hJK, hΔK⟩ :=
    exists_mem_scriptY0Star_of_mulEquiv h.item155 hJ4 hJ hUQ hU2 hU1 hJN hJUt
  have hMeets : MeetsY4 A (lB A) L K := ⟨V₁ ⊔ V₂, hJ4, le_inf hJL hJK⟩
  have hAT₁ : A ≤ Subgroup.normalizer (T₁ : Set G) :=
    (mem_scriptQ_iff.mp hmax.1.zeta₁.2.2.prop.1.1).2.1
  have hAT₂ : A ≤ Subgroup.normalizer (T₂ : Set G) :=
    (mem_scriptQ_iff.mp hmax.1.zeta₂.2.2.prop.1.1).2.1
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := Late.le_normalizer_inf hAT₁ hAT₂
  have hNloc : IsPLocal 2 (Subgroup.normalizer (U : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hU2 hU1
  obtain ⟨M, hNM, hMmax⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hNloc
  have hMmem : M ∈ CFSG.maximalTwoLocalsContaining
      ((A ⊔ ((V₁ ⊔ V₂) ⊔ U) : Subgroup G) : Set G) := by
    refine ⟨hMmax, ?_⟩
    intro x hx
    exact sup_le (hAU.trans hNM)
      (sup_le (hJN.trans hNM) (Subgroup.le_normalizer.trans hNM)) hx
  have hE27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.sec15R.toSec13Data.mem_partTwoE
  have hT₁2 : IsPGroup 2 T₁ := isPGroup_of_mem_scriptQPi Nat.prime_two hmax.1.zeta₁.2.2.prop
  have hT₂2 : IsPGroup 2 T₂ := isPGroup_of_mem_scriptQPi Nat.prime_two hmax.1.zeta₂.2.2.prop
  obtain ⟨T₃₁, hT₃₁, hleT₃₁, hcard₁⟩ :=
    exists_star_of_sup hE27 h.item146 hK hMeets (hΔK M hMmem) hV₁Q hUQ hV₁N
      (hV₁N.trans hNM) (Subgroup.le_normalizer.trans hNM) hV₁T₁
      (hU.le.trans inf_le_left) hT₁2 hlt₁
  obtain ⟨T₃₂, hT₃₂, hleT₃₂, hcard₂⟩ :=
    exists_star_of_sup hE27 h.item146 hK hMeets (hΔK M hMmem) hV₂Q hUQ hV₂N
      (hV₂N.trans hNM) (Subgroup.le_normalizer.trans hNM) hV₂T₂
      (hU.le.trans inf_le_right) hT₂2 hlt₂
  obtain ⟨x, hx, hxK⟩ := hmax.exists_conj_of_card_lt hmax.1.zeta₁ hT₃₁ hcard₁
  obtain ⟨y, hy, hyK⟩ := hmax.exists_conj_of_card_lt hmax.1.zeta₂ hT₃₂ hcard₂
  have hsym : ∃ z ∈ xA A, K = K₂.map (MulAut.conj z).toMonoidHom :=
    ⟨y⁻¹, inv_mem hy, by rw [hyK, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]⟩
  obtain ⟨z, hz, hzK⟩ := hsym
  exact hmax.1.not_conj ⟨x * z, mul_mem hx hz, by rw [hxK, hzK, Late.map_conj_map_conj]⟩

end Conf684

end CFSG.RankThree.PartTwo.Sec16.Proof163U35
