module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDn
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.GroupTheory.QuotientCoreFacts
import CFSG.LocalAnalysis.AGLEmbedding.ParabolicTwoTransport
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem inf_pCoreOf_eq_pCoreOf_Dn {N H : Subgroup G} (hDH : t.Dn N ≤ H)
    (hHN : H ≤ N) :
    t.Dn N ⊓ CFSG.Open.pCoreOf 2 H = CFSG.Open.pCoreOf 2 (t.Dn N) := by
  refine le_antisymm (t.inf_pCoreOf_le_pCoreOf_Dn hDH) ?_
  exact le_inf (CFSG.openPCoreOf_le 2 _)
    (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hDH
      (hHN.trans (t.le_normalizer_Dn N)))

private noncomputable def barMDHom {N H : Subgroup G} (hDH : t.Dn N ≤ H) :
    ↥(t.Dn N) →* ↥(CFSG.AGLEmbedding.barM H (t.Dn N)) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hDH)).codRestrict
    (CFSG.AGLEmbedding.barM H (t.Dn N)) fun d =>
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        (Subgroup.mem_subgroupOf.mpr d.2)

private theorem barMDHom_surjective {N H : Subgroup G} (hDH : t.Dn N ≤ H) :
    Function.Surjective (t.barMDHom hDH) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
  exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxy⟩

private theorem barMDHom_ker {N H : Subgroup G} (hDH : t.Dn N ≤ H) :
    (t.barMDHom hDH).ker =
      (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N) := by
  ext d
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : ((QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        (Subgroup.inclusion hDH d)) = 1 := congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (d : G) ∈ CFSG.Open.pCoreOf 2 H :=
      (CFSG.mem_openPCoreOf_iff (⟨(d : G), hDH d.2⟩ : ↥H)).mpr h1
    exact Subgroup.mem_subgroupOf.mpr ⟨d.2, h2⟩
  · intro hd
    have h2 : (d : G) ∈ CFSG.Open.pCoreOf 2 H := (Subgroup.mem_subgroupOf.mp hd).2
    have h1 : (⟨(d : G), hDH d.2⟩ : ↥H) ∈ CFSG.pCore 2 ↥H :=
      (CFSG.mem_openPCoreOf_iff (⟨(d : G), hDH d.2⟩ : ↥H)).mp h2
    apply Subtype.ext
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (Subgroup.inclusion hDH d) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h1

private theorem barMDHom_range {N H : Subgroup G} (hDH : t.Dn N ≤ H) :
    (t.barMDHom hDH).range = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨d, hd⟩ := t.barMDHom_surjective hDH y
  exact ⟨d, hd⟩

private noncomputable def barMDEquiv {N H : Subgroup G} (hDH : t.Dn N ≤ H)
    [hN : ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal] :
    (↥(t.Dn N) ⧸ (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) ≃*
      ↥(CFSG.AGLEmbedding.barM H (t.Dn N)) :=
  (QuotientGroup.quotientMulEquivOfEq (t.barMDHom_ker hDH).symm).trans
    ((QuotientGroup.quotientKerEquivRange (t.barMDHom hDH)).trans
      ((MulEquiv.subgroupCongr (t.barMDHom_range hDH)).trans Subgroup.topEquiv))

private theorem barMDEquiv_apply_mk {N H : Subgroup G} (hDH : t.Dn N ≤ H)
    [hN : ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal]
    (d : ↥(t.Dn N)) :
    t.barMDEquiv hDH (QuotientGroup.mk'
      ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) d) = t.barMDHom hDH d := by
  rfl

private theorem barMDEquiv_symm_apply {N H : Subgroup G} (hDH : t.Dn N ≤ H)
    [hN : ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal]
    (d : ↥(t.Dn N)) :
    (t.barMDEquiv hDH).symm (t.barMDHom hDH d) = QuotientGroup.mk'
      ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) d := by
  rw [← t.barMDEquiv_apply_mk hDH d, MulEquiv.symm_apply_apply]

private theorem nonempty_barM_Dn_mulEquiv_KD {N H : Subgroup G} (hDH : t.Dn N ≤ H)
    [hN : ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal] :
    Nonempty (↥(CFSG.AGLEmbedding.barM H (t.Dn N)) ≃*
      (↥(t.Dn N) ⧸ (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N))) := by
  have hker : (t.barMDHom hDH).ker =
      (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N) := t.barMDHom_ker hDH
  have e1 : (↥(t.Dn N) ⧸ (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) ≃*
      ↥(t.barMDHom hDH).range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange (t.barMDHom hDH))
  exact ⟨(e1.trans ((MulEquiv.subgroupCongr (t.barMDHom_range hDH)).trans
    Subgroup.topEquiv)).symm⟩

private theorem commutator_le_inf_pCoreOf {N H : Subgroup G} (hDH : t.Dn N ≤ H)
    (hHN : H ≤ N) (hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N)) :
    ⁅t.Dn N, t.On N⁆ ≤ t.Dn N ⊓ CFSG.Open.pCoreOf 2 H :=
  hOc.trans (le_inf (CFSG.openPCoreOf_le 2 _)
    (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hDH
      (hHN.trans (t.le_normalizer_Dn N))))

private theorem map_pPrimeCore_le_center_quotient {N H : Subgroup G} (hDH : t.Dn N ≤ H)
    [hN : ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal]
    (hHN : H ≤ N) (hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N)) :
    (CFSG.pPrimeCore 3 ↥(t.Dn N)).map
        (QuotientGroup.mk' ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N))) ≤
      Subgroup.center (↥(t.Dn N) ⧸
        (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) := by
  intro r hr
  obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hr
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hmem : (⁅q, o⁆ : ↥(t.Dn N)) ∈
      (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N) :=
    Subgroup.mem_subgroupOf.mpr (by
      have h := t.commutator_le_inf_pCoreOf hDH hHN hOc
        (Subgroup.commutator_mem_commutator q.2
          (Subgroup.mem_map_of_mem (t.Dn N).subtype ho))
      rw [Subgroup.mem_inf]
      refine ⟨(⁅q, o⁆ : ↥(t.Dn N)).2, ?_⟩
      change ⁅(q : G), (o : G)⁆ ∈ CFSG.Open.pCoreOf 2 H
      exact h.2)
  have h1 : (QuotientGroup.mk'
      ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N))) ⁅q, o⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private theorem center_quotient_eq_map_pPrimeCore
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N H : Subgroup G}
    (hKN : t.Ky ≤ N) (hDH : t.Dn N ≤ H)
    [hN : ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal] (hHN : H ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1)
    (hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N)) :
    Subgroup.center (↥(t.Dn N) ⧸
        (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) =
      (CFSG.pPrimeCore 3 ↥(t.Dn N)).map
        (QuotientGroup.mk' ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZN : t.Z ≤ N := t.Z_le_Ky.trans hKN
  have hKO : (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N) ≤
      CFSG.pPrimeCore 3 ↥(t.Dn N) := t.subgroupOf_inf_pCoreOf_le_pPrimeCore hDH
  have hRnormal : ((CFSG.pPrimeCore 3 ↥(t.Dn N)).map
      (QuotientGroup.mk'
        ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)))).Normal :=
    Subgroup.Normal.map (CFSG.pPrimeCore_normal (p := 3) (G := ↥(t.Dn N))) _
      (QuotientGroup.mk'_surjective _)
  have e2 : ((↥(t.Dn N) ⧸
        (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) ⧸
      (CFSG.pPrimeCore 3 ↥(t.Dn N)).map
        (QuotientGroup.mk'
          ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)))) ≃* t.Dhat N :=
    QuotientGroup.quotientQuotientEquivQuotient _ _ hKO
  haveI : IsSimpleGroup (t.Dhat N) := t.isSimpleGroup_Dhat hZN hrank
  have hsimple : IsSimpleGroup ((↥(t.Dn N) ⧸
        (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) ⧸
      (CFSG.pPrimeCore 3 ↥(t.Dn N)).map
        (QuotientGroup.mk'
          ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)))) :=
    e2.isSimpleGroup
  have hnc : ¬ IsMulCommutative ((↥(t.Dn N) ⧸
        (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) ⧸
      (CFSG.pPrimeCore 3 ↥(t.Dn N)).map
        (QuotientGroup.mk'
          ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)))) := by
    intro h
    obtain ⟨a, b, hab⟩ := t.exists_mul_ne_mul_Dhat hK32 hGA hSp hKN
    refine hab ?_
    have hcomm := isMulCommutative_iff.mp h
    apply e2.symm.injective
    rw [map_mul, map_mul, hcomm]
  exact le_antisymm (CFSG.GroupTheory.center_le_of_quotient_simple _ hsimple hnc)
    (t.map_pPrimeCore_le_center_quotient hDH hHN hOc)

private theorem odd_card_quot_pPrimeCore {N H : Subgroup G} (hDH : t.Dn N ≤ H)
    [hN : ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal]
    (hHN : H ≤ N) (hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N)) :
    Odd (Nat.card ((CFSG.pPrimeCore 3 ↥(t.Dn N)).map
      (QuotientGroup.mk'
        ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N))))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup ↥(t.Dn N) :=
    (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)
  haveI hKNormal : K.Normal := hN
  let R : Subgroup (↥(t.Dn N) ⧸ K) :=
    (CFSG.pPrimeCore 3 ↥(t.Dn N)).map (QuotientGroup.mk' K)
  have hRnormal : R.Normal :=
    Subgroup.Normal.map (CFSG.pPrimeCore_normal (p := 3) (G := ↥(t.Dn N))) _
      (QuotientGroup.mk'_surjective K)
  have hRcomm : IsMulCommutative R := by
    have hZ := t.map_pPrimeCore_le_center_quotient hDH hHN hOc
    rw [isMulCommutative_iff]
    intro a b
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hZ a.2) (b : ↥(t.Dn N) ⧸ K)).symm)
  have hKpc : K = CFSG.pCore 2 ↥(t.Dn N) := by
    rw [show K = ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H)).subgroupOf (t.Dn N) from rfl,
      t.inf_pCoreOf_eq_pCoreOf_Dn hDH hHN,
      CFSG.openPCoreOf_subgroupOf]
  have hcore : CFSG.pCore 2 R = ⊥ := by
    by_contra hne
    let S : Subgroup R := CFSG.pCore 2 R
    have hSne : S ≠ ⊥ := hne
    let S' : Subgroup (↥(t.Dn N) ⧸ K) := S.map R.subtype
    have hS'ne : S' ≠ ⊥ := by
      intro hbot
      exact hSne (Subgroup.map_injective R.subtype_injective (by simpa [S'] using hbot))
    have hS'normal : S'.Normal := by
      haveI : (CFSG.pCore 2 ↥R).Characteristic := inferInstance
      simpa [S', S] using
        (ConjAct.normal_of_characteristic_of_normal (H := R)
          (K := CFSG.pCore 2 ↥R))
    let T : Subgroup ↥(t.Dn N) := S'.comap (QuotientGroup.mk' K)
    have hT2 : IsPGroup 2 T := by
      have hS'2 : IsPGroup 2 S' := (CFSG.pCore_isPGroup (p := 2) (G := R)).map R.subtype
      have hK2 : IsPGroup 2 K := by
        rw [hKpc]
        exact CFSG.pCore_isPGroup (p := 2) (G := ↥(t.Dn N))
      have hK2' : IsPGroup 2 ↥(QuotientGroup.mk' K).ker := by
        rwa [QuotientGroup.ker_mk']
      exact hS'2.comap_of_ker_isPGroup (QuotientGroup.mk' K) hK2'
    have hTnormal : T.Normal := hS'normal.comap (QuotientGroup.mk' K)
    have hTleK : T ≤ K := by
      have h := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 2 T hTnormal hT2
      rwa [hKpc]
    have hmapT : T.map (QuotientGroup.mk' K) = S' := by
      rw [Subgroup.map_comap_eq]
      rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K), top_inf_eq]
    have hbot : T.map (QuotientGroup.mk' K) = ⊥ :=
      (Subgroup.map_eq_bot_iff T).mpr (by rwa [QuotientGroup.ker_mk'])
    exact hS'ne (by rw [← hmapT, hbot])
  haveI := hRcomm
  have htop : CFSG.fittingSubgroup ↥R = ⊤ := CFSG.fitting_eq_top_of_nilpotent ↥R
  have hcard : Nat.card ↥(⊤ : Subgroup ↥R) = Nat.card R :=
    Nat.card_congr (Subgroup.topEquiv (G := ↥R)).toEquiv
  have h := CFSG.Quasithin.B1.fitting_card_odd (G := ↥R) hcore
  rw [htop, hcard] at h
  exact h

theorem nonempty_barM_Dn_mulEquiv (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N H : Subgroup G}
    (hKN : t.Ky ≤ N) (hDH : t.Dn N ≤ H) (hHN : H ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1)
    (hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N)) :
    Nonempty ((↥(CFSG.AGLEmbedding.barM H (t.Dn N)) ⧸
      Subgroup.center ↥(CFSG.AGLEmbedding.barM H (t.Dn N))) ≃* t.Dhat N) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal :=
    t.normal_inf_pCoreOf_subgroupOf hDH
  obtain ⟨e1⟩ := t.nonempty_barM_Dn_mulEquiv_KD hDH
  have hZ := t.center_quotient_eq_map_pPrimeCore hK32 hGA hSp hKN hDH hHN hrank hOc
  have eC : (↥(CFSG.AGLEmbedding.barM H (t.Dn N)) ⧸
        Subgroup.center ↥(CFSG.AGLEmbedding.barM H (t.Dn N))) ≃*
      ((↥(t.Dn N) ⧸ (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) ⧸
        Subgroup.center (↥(t.Dn N) ⧸
          (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N))) :=
    QuotientGroup.congr _ _ e1 (Subgroup.map_center_eq e1)
  have hKO : (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N) ≤
      CFSG.pPrimeCore 3 ↥(t.Dn N) := t.subgroupOf_inf_pCoreOf_le_pPrimeCore hDH
  have e2 : ((↥(t.Dn N) ⧸
        (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) ⧸
      (CFSG.pPrimeCore 3 ↥(t.Dn N)).map
        (QuotientGroup.mk'
          ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)))) ≃* t.Dhat N :=
    QuotientGroup.quotientQuotientEquivQuotient _ _ hKO
  have e3 : ((↥(t.Dn N) ⧸
        (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) ⧸
        Subgroup.center (↥(t.Dn N) ⧸
          (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N))) ≃*
      ((↥(t.Dn N) ⧸
        (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)) ⧸
      (CFSG.pPrimeCore 3 ↥(t.Dn N)).map
        (QuotientGroup.mk'
          ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)))) :=
    QuotientGroup.quotientMulEquivOfEq hZ
  exact ⟨eC.trans (e3.trans e2)⟩

theorem isQuasisimple_barM_Dn (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N H : Subgroup G}
    (hKN : t.Ky ≤ N) (hDH : t.Dn N ≤ H) (hHN : H ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1)
    (hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N)) :
    CFSG.Open.IsQuasisimple ↥(CFSG.AGLEmbedding.barM H (t.Dn N)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZN : t.Z ≤ N := t.Z_le_Ky.trans hKN
  haveI hperf : Group.IsPerfect ↥(t.Dn N) :=
    Subgroup.isPerfect_iff.mpr (t.commutator_Dn hK32 hGA hSp hKN)
  haveI : Group.IsPerfect ↥(CFSG.AGLEmbedding.barM H (t.Dn N)) :=
    Group.IsPerfect.ofSurjective (t.barMDHom_surjective hDH)
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  obtain ⟨e⟩ := t.nonempty_barM_Dn_mulEquiv hK32 hGA hSp hKN hDH hHN hrank hOc
  haveI : IsSimpleGroup (t.Dhat N) := t.isSimpleGroup_Dhat hZN hrank
  exact e.isSimpleGroup

theorem isWeakSBlock_Dn (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N H S : Subgroup G}
    (hKN : t.Ky ≤ N) (hDH : t.Dn N ≤ H) (hHN : H ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1)
    (hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N))
    (hSM : Subgroup.normalizer (S : Set G) ≤ c.S.M) (hDM : ¬ t.Dn N ≤ c.S.M) :
    CFSG.AGLEmbedding.IsWeakSBlock H S (t.Dn N) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDnormal : ((t.Dn N).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDH).mpr
      (hHN.trans (t.le_normalizer_Dn N))
  have hbarNormal : (CFSG.AGLEmbedding.barM H (t.Dn N)).Normal :=
    Subgroup.Normal.map hDnormal (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
      (QuotientGroup.mk'_surjective _)
  refine ⟨⟨hDH, CFSG.Open.IsSubnormal.step hDH hDnormal (CFSG.Open.IsSubnormal.refl H),
    t.commutator_Dn hK32 hGA hSp hKN, ?_⟩, ?_⟩
  · refine ⟨le_top, CFSG.Open.IsSubnormal.step le_top ?_ (CFSG.Open.IsSubnormal.refl ⊤),
      t.isQuasisimple_barM_Dn hK32 hGA hSp hKN hDH hHN hrank hOc⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top,
      Subgroup.normalizer_eq_top_iff.mpr hbarNormal]
  · intro hle
    exact hDM (hle.trans hSM)

theorem not_three_dvd_card_center_barM_Dn (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N H : Subgroup G}
    (hKN : t.Ky ≤ N) (hDH : t.Dn N ≤ H)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥(CFSG.AGLEmbedding.barM H (t.Dn N))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal :=
    t.normal_inf_pCoreOf_subgroupOf hDH
  have hZN : t.Z ≤ N := t.Z_le_Ky.trans hKN
  let K : Subgroup ↥(t.Dn N) :=
    (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)
  let O : Subgroup ↥(t.Dn N) := CFSG.pPrimeCore 3 ↥(t.Dn N)
  let R : Subgroup (↥(t.Dn N) ⧸ K) := O.map (QuotientGroup.mk' K)
  have hKO : K ≤ O := t.subgroupOf_inf_pCoreOf_le_pPrimeCore hDH
  have e2 : (↥(t.Dn N) ⧸ K) ⧸ R ≃* t.Dhat N :=
    QuotientGroup.quotientQuotientEquivQuotient K O hKO
  haveI : IsSimpleGroup (t.Dhat N) := t.isSimpleGroup_Dhat hZN hrank
  have hsimple : IsSimpleGroup ((↥(t.Dn N) ⧸ K) ⧸ R) := e2.isSimpleGroup
  have hnc : ¬ IsMulCommutative ((↥(t.Dn N) ⧸ K) ⧸ R) := by
    intro h
    obtain ⟨a, b, hab⟩ := t.exists_mul_ne_mul_Dhat hK32 hGA hSp hKN
    refine hab ?_
    have hcomm := isMulCommutative_iff.mp h
    apply e2.symm.injective
    rw [map_mul, map_mul, hcomm]
  have hZle : Subgroup.center (↥(t.Dn N) ⧸ K) ≤ R :=
    CFSG.GroupTheory.center_le_of_quotient_simple R hsimple hnc
  obtain ⟨e1⟩ := t.nonempty_barM_Dn_mulEquiv_KD hDH
  have hcard : Nat.card (Subgroup.center ↥(CFSG.AGLEmbedding.barM H (t.Dn N))) =
      Nat.card (Subgroup.center (↥(t.Dn N) ⧸ K)) := by
    rw [← Subgroup.map_center_eq e1]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ e1.toMonoidHom e1.injective).toEquiv
  rw [hcard]
  have hdvd1 : Nat.card (Subgroup.center (↥(t.Dn N) ⧸ K)) ∣ Nat.card R :=
    Subgroup.card_dvd_of_le hZle
  have hdvd2 : Nat.card R ∣ Nat.card O := Subgroup.card_map_dvd O (QuotientGroup.mk' K)
  have hO : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(t.Dn N)))
  exact fun h3 => hO (h3.trans (hdvd1.trans hdvd2))

theorem isCyclic_of_isPGroup_barM_Dn {N H : Subgroup G} (hDH : t.Dn N ≤ H)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1)
    {P : Subgroup ↥(CFSG.AGLEmbedding.barM H (t.Dn N))} (hP : IsPGroup 3 P) : IsCyclic ↥P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDrank : CFSG.pRank 3 ↥(t.Dn N) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact le_of_eq hrank
  have hBrank : CFSG.pRank 3 ↥(CFSG.AGLEmbedding.barM H (t.Dn N)) ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      Nat.prime_three (by norm_num) hDrank (t.barMDHom hDH) (t.barMDHom_surjective hDH)
  have hPrank : CFSG.pRank 3 ↥P ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    calc CFSG.Open.pRank 3 (P : Subgroup ↥(CFSG.AGLEmbedding.barM H (t.Dn N)))
        ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(CFSG.AGLEmbedding.barM H (t.Dn N))) :=
          CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
      _ = CFSG.pRank 3 ↥(CFSG.AGLEmbedding.barM H (t.Dn N)) :=
          (CFSG.SectionRank.pRank_eq_open_pRank_top 3 _).symm
      _ ≤ 1 := hBrank
  exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
    Nat.prime_three (by norm_num) hP hPrank

theorem isParabolicTwo_Dhat_of_barM (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N H : Subgroup G}
    (hKN : t.Ky ≤ N) (hDH : t.Dn N ≤ H) (hHN : H ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1)
    (hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N)) {J : Subgroup G}
    (hJD : J ≤ t.Dn N)
    (hpar : CFSG.AGLEmbedding.IsParabolicTwo (CFSG.AGLEmbedding.barM H (t.Dn N))
      (CFSG.AGLEmbedding.barM H J)) :
    CFSG.AGLEmbedding.IsParabolicTwo (⊤ : Subgroup (t.Dhat N))
      ((J.subgroupOf (t.Dn N)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(t.Dn N)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hKNormal :
      ((t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)).Normal :=
    t.normal_inf_pCoreOf_subgroupOf hDH
  let K : Subgroup ↥(t.Dn N) :=
    (t.Dn N ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf (t.Dn N)
  haveI hKNormal' : K.Normal := hKNormal
  let O : Subgroup ↥(t.Dn N) := CFSG.pPrimeCore 3 ↥(t.Dn N)
  let R : Subgroup (↥(t.Dn N) ⧸ K) := O.map (QuotientGroup.mk' K)
  have hKO : K ≤ O := t.subgroupOf_inf_pCoreOf_le_pPrimeCore hDH
  have hKO' : K ≤ (QuotientGroup.mk' O).ker := by rwa [QuotientGroup.ker_mk']
  let q' : (↥(t.Dn N) ⧸ K) →* t.Dhat N :=
    QuotientGroup.lift K (QuotientGroup.mk' O) hKO' 
  let A : Type := ↥(CFSG.AGLEmbedding.barM H (t.Dn N))
  let Jsub : Subgroup A :=
    (CFSG.AGLEmbedding.barM H J).subgroupOf (CFSG.AGLEmbedding.barM H (t.Dn N))
  let φ : A →* t.Dhat N :=
    q'.comp (t.barMDEquiv hDH).symm.toMonoidHom
  have hpar_top : CFSG.AGLEmbedding.IsParabolicTwo (⊤ : Subgroup A) Jsub :=
    hpar.subgroupOf_top
  have hqsurj : Function.Surjective q' := by
    intro y
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective O y
    exact ⟨QuotientGroup.mk' K d, QuotientGroup.lift_mk' K (φ := QuotientGroup.mk' O) hKO' d⟩
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hqsurj y
    obtain ⟨a, rfl⟩ := (t.barMDEquiv hDH).symm.surjective x
    exact ⟨a, rfl⟩
  have hkerq : q'.ker = R := by
    rw [show q' = QuotientGroup.lift K (QuotientGroup.mk' O) hKO' from rfl,
      QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  have hkerφ : φ.ker = R.comap ((t.barMDEquiv hDH).symm).toMonoidHom := by
    ext a
    show q' ((t.barMDEquiv hDH).symm.toMonoidHom a) = 1 ↔
      (t.barMDEquiv hDH).symm.toMonoidHom a ∈ R
    have hmem : ((t.barMDEquiv hDH).symm.toMonoidHom a ∈ q'.ker) ↔
        ((t.barMDEquiv hDH).symm.toMonoidHom a ∈ R) := by rw [hkerq]
    exact (MonoidHom.mem_ker (f := q')
      (x := (t.barMDEquiv hDH).symm.toMonoidHom a)).trans hmem
  have hRodd : Odd (Nat.card R) := t.odd_card_quot_pPrimeCore hDH hHN hOc
  have hoddφ : Odd (Nat.card φ.ker) := by
    rw [hkerφ]
    let e := ((t.barMDEquiv hDH).symm).toMonoidHom
    have hcard : Nat.card (R.comap e) = Nat.card R := by
      have hmap : (R.comap e).map e = R :=
        Subgroup.map_comap_eq_self_of_surjective (t.barMDEquiv hDH).symm.surjective R
      calc Nat.card (R.comap e) = Nat.card ((R.comap e).map e) :=
            (Subgroup.card_map_of_injective (t.barMDEquiv hDH).symm.injective).symm
        _ = Nat.card R := by rw [hmap]
    rw [hcard]
    exact hRodd
  have hmain : CFSG.AGLEmbedding.IsParabolicTwo (⊤ : Subgroup (t.Dhat N)) (Jsub.map φ) :=
    hpar_top.map_top_of_surjective_of_odd_ker φ hφsurj hoddφ
  have hJmap : Jsub.map φ =
      (J.subgroupOf (t.Dn N)).map (QuotientGroup.mk' O) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyJ : (y : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
          CFSG.AGLEmbedding.barM H J := Subgroup.mem_subgroupOf.mp hy
      obtain ⟨j, hj, hjy⟩ := Subgroup.mem_map.mp hyJ
      have hjg : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
      have hd : (⟨(j : G), hJD hjg⟩ : ↥(t.Dn N)) ∈ J.subgroupOf (t.Dn N) :=
        Subgroup.mem_subgroupOf.mpr hjg
      have hyD : y = t.barMDHom hDH ⟨(j : G), hJD hjg⟩ := by
        apply Subtype.ext
        exact hjy.symm
      rw [hyD]
      change q' ((t.barMDEquiv hDH).symm (t.barMDHom hDH ⟨(j : G), hJD hjg⟩)) ∈
        Subgroup.map (QuotientGroup.mk' O) (J.subgroupOf (t.Dn N))
      rw [t.barMDEquiv_symm_apply hDH]
      exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hd
    · intro hz
      obtain ⟨d, hd, hdz⟩ := Subgroup.mem_map.mp hz
      refine ⟨t.barMDHom hDH d, ?_, ?_⟩
      · refine Subgroup.mem_subgroupOf.mpr ?_
        exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hd))
      · rw [← hdz]
        change q' ((t.barMDEquiv hDH).symm (t.barMDHom hDH d)) = QuotientGroup.mk' O d
        rw [t.barMDEquiv_symm_apply hDH]
        exact QuotientGroup.lift_mk' K (φ := QuotientGroup.mk' O) hKO' d
  rw [hJmap] at hmain
  exact hmain

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
