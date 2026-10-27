module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassicalLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmallLabel
public import CFSG.LocalAnalysis.StandardType.GGOrthNsSgnLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTBTorRowNoFour (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
    GGTBTorRowAt p lab r m N C M ∧ ∀ i, ∃ j, ¬ M i j ∣ 4

@[expose] def GGSecFiveBCoordDExclRestOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → p = 3 →
      ∀ (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n), 4 ≤ n →
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        ∀ (y : G) (K : Subgroup G), K ∈ 𝒦 → GGNbr p B x D J y K →
          ∀ r ∈ ggAutomizer K Bs, GGIsReflection p r →
            (∃ i : Fin n, MulAut.congr eta r = SpCoord.sgnAut i) →
            GGInnerDiagOnLabel S p Bs K →
              (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≠ dCoordinateBlock n p i0

@[expose] def GGSecFiveBCoordDExclSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGLabQFour p lab ∧ ¬ GGTBTorRowNoFour p lab ∧ ¬ GGTableBNbrInnerNineClassicalLabel p lab ∧
    ¬ (GGTableBNbrInnerNineSmallLabel p lab ∨ lab.tag = .triD4 ∨ lab.tag = .twF4)

@[expose] def GGSecFiveBCoordDExclRestInput : Prop :=
  GGSecFiveBCoordDExclRestOn fun p lab => GGSecFiveBCoordDExclSplitLabel p lab ∧ lab.n = 1 ∧
    (lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C)

end CFSG.StandardType

end
