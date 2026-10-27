module

public import CFSG.Quasithin.Vol2.F134Overgroup
public import CFSG.Quasithin.Recognition.CertU33DcPG
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Perm
public import CFSG.Timmesfeld.Final.PSU33
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate19953
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.F134

open CFSG.Quasithin CFSG.Quasithin.P134 CFSG.Assembly.LowTwoRank

theorem card_u33_A_le
    : Nat.card u33Data.A ≤ 160 := by
  have key : ∀ z : u33Data.A, ∃ ix : Fin 160,
      permL (u33PresHom (z : U33G)) = u33ABTab.getD ix [] := fun z => by
    obtain ⟨ix, hix, h⟩ := exists_index_AB (Or.inl z.2)
    exact ⟨⟨ix, hix⟩, h⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro z z' h
    have h' := (hf z).trans ((congrArg (fun ix : Fin 160 => u33ABTab.getD ix []) h).trans
      (hf z').symm)
    exact Subtype.ext (u33PresHom_injective (permL_eq_iff.1 h'))
  calc Nat.card u33Data.A ≤ Nat.card (Fin 160) := Nat.card_le_card_of_injective f hinj
    _ = 160 := Nat.card_fin 160

theorem card_u33_B_le
    : Nat.card u33Data.B ≤ 160 := by
  have key : ∀ z : u33Data.B, ∃ ix : Fin 160,
      permL (u33PresHom (z : U33G)) = u33ABTab.getD ix [] := fun z => by
    obtain ⟨ix, hix, h⟩ := exists_index_AB (Or.inr z.2)
    exact ⟨⟨ix, hix⟩, h⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro z z' h
    have h' := (hf z).trans ((congrArg (fun ix : Fin 160 => u33ABTab.getD ix []) h).trans
      (hf z').symm)
    exact Subtype.ext (u33PresHom_injective (permL_eq_iff.1 h'))
  calc Nat.card u33Data.B ≤ Nat.card (Fin 160) := Nat.card_le_card_of_injective f hinj
    _ = 160 := Nat.card_fin 160

theorem noE9Config_psu3_three :
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 3 1 := by
  have : Finite U33G := Nat.finite_of_card_ne_zero (by rw [card_u33Pres]; norm_num)
  obtain ⟨ePres⟩ := u33Pres_mulEquiv_PSU3
  refine noE9Config_of_overgroupData u33Data u33_syl.1 u33_syl.2 ?_ ?_ ?_ fun X _ h => ?_
  · rw [u33_card_T]
    have := card_u33_A_le
    omega
  · rw [u33_card_T]
    have := card_u33_B_le
    omega
  · rw [u33_card_T, card_u33Pres]
    norm_num
  · obtain ⟨e⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel
      (Or.inl ⟨by decide, h⟩ : CFSG.Blueprint.LieModel X .PSU 3 3 1)
    exact ⟨e.trans ePres.symm⟩

end CFSG.Quasithin.F134
