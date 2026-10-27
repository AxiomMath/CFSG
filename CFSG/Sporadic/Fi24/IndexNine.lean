module

public import CFSG.Sporadic.Fi24.Setup
public import CFSG.Sporadic.Mathieu.Chain
public import CFSG.Certificates.Kernel.SporLatDcSound
public import Certificates.Data.CFSGNative.SporLat.Build
public import Certificates.Data.CFSGNative.Th.Tables
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.Perm.ChainSift
public import Certificates.Data.CFSGNative.SporadicSchreier.Classes
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import Certificates.Certificate744112
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22SporMid
public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24TJ
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ECode
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Glue1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Hyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesCover
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S153Baum
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1531Close2
public import CFSG.Quasithin.EmptyFaithful.T1531In66b
public import CFSG.Quasithin.Vol2.Ch4Sec1Lem415
public import CFSG.Quasithin.Vol2.Ch4Sec4Lem445
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Sporadic.Schreier.J4SLocalNodes

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native CFSG.Perm CFSG.Perm.Native
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.Schreier.Native CFSG.KC.SLDc
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

private theorem fi24_indexThreePackage_M24 :
    IndexThreePackage ↥CFSG.Blueprint.NativeSporadic.M24 :=
  Certificates.certificate744112.2

private theorem fi24_indexNinePackage_M24 :
    IndexNinePackage ↥CFSG.Blueprint.NativeSporadic.M24 :=
  Certificates.certificate744112.1

open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Fi24K in
theorem fi24_index_nine_package :
    IndexNinePackage ↥CFSG.Sporadic.Fi24.J := by
  have hΔ : IndexNinePackage ↥CFSG.Blueprint.NativeSporadic.M24 :=
    fi24_indexNinePackage_M24
  let C : Subgroup ↥CFSG.Sporadic.Fi24.J := Subgroup.normalizer (fi24E : Set ↥CFSG.Sporadic.Fi24.J)
  let K : Subgroup ↥C := fi24E.subgroupOf C
  let e : ↥C ⧸ K ≃* ↥CFSG.Blueprint.NativeSporadic.M24 :=
    Classical.choice quotient_fi24E
  let π : ↥C →* ↥CFSG.Blueprint.NativeSporadic.M24 :=
    e.toMonoidHom.comp (QuotientGroup.mk' K)
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : π.ker = K := by
    dsimp only [π]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hker2 : IsPGroup 2 π.ker := by
    rw [hker]
    refine IsPGroup.of_card (n := 11) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv,
      card_fi24E]
  refine indexNinePackage_of_char_quotient isSylowTwoOf_fi24T fi24T_le_normalizer π hπ hker2
    ?_ hΔ
  intro α hα
  have hE : fi24E.map α.toMonoidHom = fi24E := by
    have h := CFSG.Quasithin.thompsonJ_map_mulEquiv α fi24T
    rw [thompsonJ_fi24T, hα, thompsonJ_fi24T] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.map_normalizer_eq_of_bijective fi24E α.bijective, hE]
  · rw [hker, Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer, hE]

open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Fi24K in
theorem fi24_index_three_package :
    IndexThreePackage ↥CFSG.Sporadic.Fi24.J := by
  have hΔ : IndexThreePackage ↥CFSG.Blueprint.NativeSporadic.M24 :=
    fi24_indexThreePackage_M24
  let C : Subgroup ↥CFSG.Sporadic.Fi24.J := Subgroup.normalizer (fi24E : Set ↥CFSG.Sporadic.Fi24.J)
  let K : Subgroup ↥C := fi24E.subgroupOf C
  let e : ↥C ⧸ K ≃* ↥CFSG.Blueprint.NativeSporadic.M24 :=
    Classical.choice quotient_fi24E
  let π : ↥C →* ↥CFSG.Blueprint.NativeSporadic.M24 :=
    e.toMonoidHom.comp (QuotientGroup.mk' K)
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : π.ker = K := by
    dsimp only [π]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hker2 : IsPGroup 2 π.ker := by
    rw [hker]
    refine IsPGroup.of_card (n := 11) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv,
      card_fi24E]
  refine indexThreePackage_of_char_quotient isSylowTwoOf_fi24T fi24T_le_normalizer π hπ hker2
    ?_ hΔ
  intro α hα
  have hE : fi24E.map α.toMonoidHom = fi24E := by
    have h := CFSG.Quasithin.thompsonJ_map_mulEquiv α fi24T
    rw [thompsonJ_fi24T, hα, thompsonJ_fi24T] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.map_normalizer_eq_of_bijective fi24E α.bijective, hE]
  · rw [hker, Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer, hE]

end CFSG.Sporadic.Fi24
