module

public import CFSG.LocalAnalysis.StandardType.L34SylowOvergroup
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.StandardType

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

namespace L34Sylow

theorem eq_of_order_seven
    {Z : Subgroup (Equiv.Perm (Fin 42))} (hPZ : closureTabs pGens ≤ Z)
    (hZS : Z ≤ closureTabs gensS) (h7 : ∃ x ∈ Z, x ≠ 1 ∧ x ^ 7 = 1) :
    Z = closureTabs gensS :=
  Certificates.certificate465003.seven Z hPZ hZS h7

end L34Sylow

namespace L34Overgroup

open L34Sylow

theorem eq_top_of_le_of_seven_dvd
    {Y : Subgroup ↥S}
    (hPY : (closureTabs pGens).subgroupOf S ≤ Y) (h7 : 7 ∣ Nat.card Y) : Y = ⊤ := by
  have hPS : closureTabs pGens ≤ S := closureTabs_gensS ▸ overgroupFacts.P_le_S
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set Z : Subgroup (Equiv.Perm (Fin 42)) := Y.map S.subtype with hZ
  have hPZ : closureTabs pGens ≤ Z := by
    intro g hg
    exact ⟨⟨g, hPS hg⟩, hPY (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
  have hZS : Z ≤ closureTabs gensS := by
    rw [closureTabs_gensS]
    exact Subgroup.map_subtype_le Y
  have h7Z : 7 ∣ Nat.card Z := by
    rwa [hZ, Subgroup.card_map_of_injective S.subtype_injective]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 7 h7Z
  have hz1 : (z : Equiv.Perm (Fin 42)) ≠ 1 := fun h1 => by
    rw [show z = 1 from Subtype.ext h1, orderOf_one] at hz
    norm_num at hz
  have hz7 : (z : Equiv.Perm (Fin 42)) ^ 7 = 1 := by
    rw [← hz, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
  have hZtop := eq_of_order_seven hPZ hZS ⟨z, z.2, hz1, hz7⟩
  rw [Subgroup.eq_top_iff']
  intro y
  have hy : (y : Equiv.Perm (Fin 42)) ∈ Z := by
    rw [hZtop, closureTabs_gensS]
    exact y.2
  obtain ⟨y', hy', hyy'⟩ := hy
  rwa [show y' = y from Subtype.ext hyy'] at hy'

theorem not_seven_dvd_card_of_not_dvd_index
    {Y : Subgroup ↥S} (hY : Y ≠ ⊤) (h3 : ¬ 3 ∣ Y.index) :
    ¬ 7 ∣ Nat.card Y := by
  classical
  have hF := overgroupFacts
  have hPS : closureTabs pGens ≤ S := closureTabs_gensS ▸ hF.P_le_S
  have hcardS : Nat.card ↥S = 20160 := by
    rw [← closureTabs_gensS]
    exact hF.card_S
  have : Finite ↥S := Nat.finite_of_card_ne_zero (by rw [hcardS]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPcard : Nat.card ↥((closureTabs pGens).subgroupOf S) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
    exact hF.card_P
  have hPgrp : IsPGroup 3 ↥((closureTabs pGens).subgroupOf S) :=
    IsPGroup.of_card (n := 2) (by rw [hPcard]; norm_num)
  have hPidx : ¬ 3 ∣ ((closureTabs pGens).subgroupOf S).index := by
    have h := Subgroup.card_mul_index ((closureTabs pGens).subgroupOf S)
    rw [hPcard, hcardS] at h
    have h2 : ((closureTabs pGens).subgroupOf S).index = 2240 := by omega
    rw [h2]
    norm_num
  let PS : Sylow 3 ↥S := hPgrp.toSylow hPidx
  have hPS' : (PS : Subgroup ↥S) = (closureTabs pGens).subgroupOf S := IsPGroup.toSylow_coe _ _
  refine SylowOvergroup.forall_of_sylow_le PS (fun Y => ¬ 7 ∣ Nat.card Y) ?_ ?_ hY h3
  · intro g Y h
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h
  intro Y hPY hYtop h7
  exact hYtop (eq_top_of_le_of_seven_dvd (by rw [← hPS']; exact hPY) h7)

theorem not_seven_dvd_card_of_lieModel
    {K : Type} [Group K] [Finite K]
    (hK : Blueprint.LieModel K .PSL 3 2 2) {Y : Subgroup K} (hY : Y ≠ ⊤) (h3 : ¬ 3 ∣ Y.index) :
    ¬ 7 ∣ Nat.card Y := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hK
  exact SylowOvergroup.forall_of_mulEquiv e (fun A _ => ¬ 7 ∣ Nat.card A)
    (fun A B _ _ f h => by rwa [← Nat.card_congr f.toEquiv])
    (fun Y hY h3 => not_seven_dvd_card_of_not_dvd_index hY h3) Y hY h3

end L34Overgroup

end CFSG.StandardType

end
