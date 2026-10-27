module

public import CFSG.Quasithin.Background.B1MoreTwelve
public import CFSG.Quasithin.Background.B1MoreTen
public import CFSG.Quasithin.Background.B1MoreSeven
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

@[expose] def IsLieTypeTwoSimple (S : Type) [Group S] : Prop :=
  CFSG.Blueprint.EvenLieType S ∨ IsPSU 3 3 1 S

@[expose] def IsLieChar2Quasi (L : Type) [Group L] : Prop :=
  CFSG.IsQuasisimple L ∧ IsLieTypeTwoSimple (L ⧸ Subgroup.center L)

@[expose] def IsLieAltType (L : Type) [Group L] : Prop :=
  IsLieChar2Quasi L ∨ (∃ m, IsAlt m L) ∨ IsHat L ↥(alternatingGroup (Fin 6))

section Conclusion

variable {V : Type} [CommGroup V]

@[expose] def B113Conclusion (G K : Subgroup (MulAut V)) : Prop :=
  (Nat.card ↥K = 3 ∧ K ≤ fittingOf G ∧ K ≤ Subgroup.centralizer (fittingOf G : Set (MulAut V))) ∨
    (CFSG.Open.IsComponentOf K G ∧
      (IsLieChar2Quasi ↥K ∨ (∃ n, IsAlt n ↥K) ∨ IsHat ↥K ↥(alternatingGroup (Fin 6)))) ∨
    ∃ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L G ∧ K ≤ L ∧
      ∃ m, IsAlt m ↥L ∧ ((∃ n, n ≤ m ∧ IsAlt n ↥K) ∨ (IsPSL 3 2 1 ↥K ∧ m = 7))

end Conclusion

@[expose] def AsB113Det (𝒦 : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G A L : Subgroup (MulAut V)), 𝒦 ↥G → pCoreOf 2 G = ⊥ →
      IsFFStarOffender G A → CFSG.Open.IsComponentOf L G → ⁅L, A⁆ = L → IsLieAltType ↥L

@[expose] def AsLieAltSylowCentralizer : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (L T : Subgroup Ω), CFSG.IsQuasisimple ↥L → IsLieAltType ↥L →
    CFSG.QuasithinUnique.IsSylowTwoOf T L →
    ∀ x : Ω, x ∈ Subgroup.normalizer (L : Set Ω) → x ∈ Subgroup.centralizer (T : Set Ω) →
      Odd (orderOf x) → x ∈ Subgroup.centralizer (L : Set Ω)

@[expose] def AsLieAltOvergroups : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (L T X K : Subgroup Ω), CFSG.IsQuasisimple ↥L →
    IsLieAltType ↥L → CFSG.QuasithinUnique.IsSylowTwoOf T L → T ≤ X → X ≤ L → X ≠ L → K ≤ X →
    CFSG.Open.IsSubnormal K X → (CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) →
    ¬ K ≤ Subgroup.centralizer (L : Set Ω) →
    ∃ m, IsAlt m ↥L ∧ ((∃ n, n ≤ m ∧ IsAlt n ↥K) ∨ (IsPSL 3 2 1 ↥K ∧ m = 7))

structure AsB113Inputs (𝒦 : ∀ (X : Type) [Group X], Prop) : Prop where
  timmesfeld : AsB15Part4
  determination : AsB113Det 𝒦
  sylowCentralizer : AsLieAltSylowCentralizer
  overgroups : AsLieAltOvergroups

end CFSG.Quasithin
