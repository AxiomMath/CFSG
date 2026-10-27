module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCover
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreGriess
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate10010
public import Certificates.Certificate10011
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.TwoBCertBase
public import CFSG.Sporadic.HeldB.OuterFixed
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG.Open

theorem card_hopf_u62
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nat.card (griessHopfMultiplier (StatedProj (StatedSU 6 (2 ^ 1) K))) = 3 * 4 := by
  have hcl : StatedClassicalModel (StatedProj (StatedSU 6 (2 ^ 1) K)) .PSU 6 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, K, inferInstance, inferInstance, hK,
      ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_six_two_row
    (CFSG.LieType.Steinberg.CentralExt.GriessNative.models_lieModel_of_classical hcl)
  rw [Nat.card_congr e.toEquiv, CFSG.ComponentClassification.Foote5.card_generic_prod_exceptional]
  have h1 : CFSG.Blueprint.Multiplier.genericOrders .PSU 6 2 1 = (3, 1) := by decide
  have h2 : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 6 2 1 = (2, 2) := rfl
  simp [h1, h2]

theorem exists_cover_u62
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {Y : Type} [Group Y] [Finite Y] (η : Y →* StatedProj (StatedSU 6 (2 ^ 1) K))
    (hη : Function.Surjective η) (hperf : Group.IsPerfect Y) (hker : η.ker ≤ Subgroup.center Y)
    (hodd : Nat.Coprime (Nat.card η.ker) 4) :
    ∃ ψ : ↥(StatedSU 6 (2 ^ 1) K) →* Y, Function.Surjective ψ ∧
      ∀ s, η (ψ s) =
        QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 1) K)) s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hK
  haveI : Group.IsPerfect ↥(StatedSU 6 (2 ^ 1) K) :=
    CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hK (by norm_num)
  have hβc : (QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf
      (StatedSU 6 (2 ^ 1) K))).ker ≤ Subgroup.center ↥(StatedSU 6 (2 ^ 1) K) := by
    rw [QuotientGroup.ker_mk']
    exact scalars_le_center_statedSU
  have hd : Nat.card (QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf
      (StatedSU 6 (2 ^ 1) K))).ker = 3 := by
    rw [QuotientGroup.ker_mk',
      (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num : 1 ≤ 6)).2.2]
    norm_num
  exact ggExists_cover_of_hopfMultiplier_coprime (QuotientGroup.mk'_surjective _) hη inferInstance
    hperf hβc hker (center_statedProj_statedSU_eq_bot hK (by norm_num)) hd (card_hopf_u62 hK) hodd

theorem card_hopf_u42
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nat.card (griessHopfMultiplier (StatedProj (StatedSU 4 (2 ^ 1) K))) = 1 * 2 := by
  have hcl : StatedClassicalModel (StatedProj (StatedSU 4 (2 ^ 1) K)) .PSU 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, K, inferInstance, inferInstance, hK,
      ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_four_two_row
    (CFSG.LieType.Steinberg.CentralExt.GriessNative.models_lieModel_of_classical hcl)
  rw [Nat.card_congr e.toEquiv, CFSG.ComponentClassification.Foote5.card_generic_prod_exceptional]
  have h1 : CFSG.Blueprint.Multiplier.genericOrders .PSU 4 2 1 = (1, 1) := by decide
  have h2 : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 1 = (2, 1) := rfl
  simp [h1, h2]

theorem exists_cover_u42
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {Y : Type} [Group Y] [Finite Y] (η : Y →* StatedProj (StatedSU 4 (2 ^ 1) K))
    (hη : Function.Surjective η) (hperf : Group.IsPerfect Y) (hker : η.ker ≤ Subgroup.center Y)
    (hodd : Nat.Coprime (Nat.card η.ker) 2) :
    ∃ ψ : ↥(StatedSU 4 (2 ^ 1) K) →* Y, Function.Surjective ψ ∧
      ∀ s, η (ψ s) =
        QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ 1) K)) s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hK
  haveI : Group.IsPerfect ↥(StatedSU 4 (2 ^ 1) K) :=
    CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hK (by norm_num)
  have hβc : (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf
      (StatedSU 4 (2 ^ 1) K))).ker ≤ Subgroup.center ↥(StatedSU 4 (2 ^ 1) K) := by
    rw [QuotientGroup.ker_mk']
    exact scalars_le_center_statedSU
  have hd : Nat.card (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf
      (StatedSU 4 (2 ^ 1) K))).ker = 1 := by
    rw [QuotientGroup.ker_mk',
      (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num : 1 ≤ 4)).2.2]
    norm_num
  exact ggExists_cover_of_hopfMultiplier_coprime (QuotientGroup.mk'_surjective _) hη inferInstance
    hperf hβc hker (center_statedProj_statedSU_eq_bot hK (by norm_num)) hd (card_hopf_u42 hK) hodd

theorem exists_cover_u2
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {n : ℕ} (hn : n = 4 ∨ n = 6)
    {Y : Type} [Group Y] [Finite Y] (η : Y →* StatedProj (StatedSU n (2 ^ 1) K))
    (hη : Function.Surjective η) (hperf : Group.IsPerfect Y) (hker : η.ker ≤ Subgroup.center Y)
    (hodd : Nat.Coprime (Nat.card η.ker) 4) :
    ∃ ψ : ↥(StatedSU n (2 ^ 1) K) →* Y, Function.Surjective ψ ∧
      ∀ s, η (ψ s) =
        QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ 1) K)) s := by
  rcases hn with rfl | rfl
  · exact exists_cover_u42 hK η hη hperf hker (Nat.Coprime.coprime_dvd_right (by norm_num) hodd)
  · exact exists_cover_u62 hK η hη hperf hker hodd

end CFSG.StandardType

end
