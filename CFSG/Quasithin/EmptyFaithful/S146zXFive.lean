module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.H13.NQCoreP134Group

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.H13.NQCore

@[expose] def Prop134Five : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 5 →
  ∀ (G : Type) [Group G] [Finite G] (H S X P : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥H → pCoreOf 2 H ≠ ⊥ → IsSylowTwoOf S H → X ≤ H → IsXi S X →
    (pCoreOf 2 X).relIndex X = p ^ 2 → P ≤ X → IsPGroup p P → Nat.card P = p ^ 2 →
    H ≤ Subgroup.normalizer (X : Set G) ∨
    ∃ L : Subgroup G, L ∈ cComp H ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      X ≤ conjClosure L S ∧
      (
        (¬ S ≤ Subgroup.normalizer (L : Set G) ∧ P ⊓ L ≠ ⊥ ∧
          ((∃ n : ℕ, p ∣ 2 ^ n - 1 ∧
              StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 2 2 n) ∨
            ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
              StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 2 q 1)) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 3 p 1 ∨
            Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod p))))) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧ EmptyFaithfulMultiple.AutCyclic S P))

end CFSG.Quasithin.S146zX
