module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofOut
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec16.Item16Tail

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1613
  CFSG.RankThree.PartTwo.Sec16.Proof1613Res CFSG.GH74.GLS

@[expose] noncomputable def Step1616OmegaSz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Sec8.IsZ3PGLThreePi ↥(lBarA c L A) → omegaA A = {Subgroup.zpowers c} →
      Odd (Nat.card (thetaCen ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G))) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ∀ b ∈ Subgroup.zpowers c ⊔ (A ⊓ L), b ≠ 1 →
        Odd (Nat.card (thetaCen ({b} : Set G))) → Subgroup.zpowers b ∉ omegaA A →
        ⁅S ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≤
            pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) →
          ⁅S ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≤ thetaCen ({b} : Set G)

end CFSG.RankThree.PartTwo.Sec16
