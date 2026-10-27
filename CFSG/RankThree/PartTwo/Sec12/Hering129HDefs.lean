module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HBasic
public import CFSG.RankThree.PartTwo.Sec12.Hering129HNotIii
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Types

variable {G : Type} [Group G] [Finite G]

@[expose] def GTwoType129At (L K : Subgroup G) (q : TauCeti.PrimePower) : Prop :=
  Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card ∧
    (Sec4.IsoGTwo (K ⧸ CFSG.pCore 2 K) q ∨
      ∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid,
        Nonempty (K ⧸ CFSG.pCore 2 K ≃*
          (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group))

theorem gTwoType129_iff {L K : Subgroup G} : GTwoType129 L K ↔ ∃ q, GTwoType129At L K q :=
  Iff.rfl

@[expose] def Typ129IV (q : TauCeti.PrimePower) (Y : Subgroup G) : Prop :=
  (q.card = 4 ∨ q.card = 5) ∧ ∃ r : TauCeti.PrimePower, (r.card = 4 ∨ r.card = 5) ∧
    q.card ≠ r.card ∧ Sec4.IsoGTwo (Y ⧸ CFSG.pCore 2 Y) r

structure SymData129 (A : Subgroup G) (c x : G) (Y : Subgroup G) : Prop where
  quasi : IsQuasisimple (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c))
  mem : c ∈ resCent Y c
  exists_j : ∃ j ∈ A ⊓ resCent Y c, j ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers c
  card_center :
    Nat.card (Subgroup.center (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c))) = 3

end Types

@[expose] def Gap129KFK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → GTwoType129 L K →
    ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      c ∈ resCent K x ∧ S ≤ resCent K x ∧
        IsQuasisimple (↥(resCent K x) ⧸ aschbacherSolvableCore 3 ↥(resCent K x))

@[expose] def Gap129ClaimG2M : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
    GTwoType129At L K q → ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      ∃ Y : Subgroup G, Y ∈ thetaComponentsAt 3 x ∧ ⁅Y, Subgroup.zpowers c⁆ = Y ∧
        (Typ129I K Y ∨ Typ129II K Y ∨ Typ129IV q Y ∨ Typ129IIIcMinus A c L Y x)

@[expose] def KFNonIsoG2D4 : Prop :=
  ∀ (q q' : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hq' : (TauCeti.LieTypeIndex.trialityD4 q').Valid),
    IsEmpty ((TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group ≃*
      (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hq'⟩).Group)

end CFSG.RankThree.PartTwo.Sec12
