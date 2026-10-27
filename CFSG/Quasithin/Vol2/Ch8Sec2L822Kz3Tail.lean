module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5
public import CFSG.Quasithin.Vol2.Ch3Sec1L319SevenBlk
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L319 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.EmptyFaithfulMultiple

variable {G : Type} [Group G]

@[expose] def Kz134Tail_kz (Hh S L P : Subgroup G) : Prop :=
  ((∃ t ∈ S ⊓ Subgroup.normalizer (P : Set G), t ∉ Subgroup.normalizer (L : Set G) ∧
      P = (P ⊓ L) ⊔ conjByElt t (P ⊓ L) ∧ (P ⊓ L) ⊓ conjByElt t (P ⊓ L) = ⊥) ∧
    ((∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 q 1)) ∨
  (S ≤ Subgroup.normalizer (L : Set G) ∧
    (StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 3))))) ∨
  (S ≤ Subgroup.normalizer (L : Set G) ∧
    (∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n) ∧
    AutCyclic S P) ∨
  (S ≤ Subgroup.normalizer (L : Set G) ∧
    (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
      StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
      StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1)) ∨
  (Hh ≤ Subgroup.normalizer (L : Set G) ∧
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He))

end CFSG.Quasithin.H13
