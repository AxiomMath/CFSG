module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs

public section

namespace CFSG.StandardType

@[expose] def BMarkedOriginalPositionAt {G : Type} [Group G] (p n : ℕ) (Bs L : Subgroup G)
    (Kset : Finset (Subgroup G)) : Prop :=
  4 ≤ n ∧ ∃ eta : Bs ≃* (Fin n → Multiplicative (ZMod p)), ∃ i0 : Fin n,
    (ggAutomizerJoin L Bs Kset).map (MulAut.congr eta).toMonoidHom = bSignedFull n p ∧
    ((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 ∨
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p i0 ∨
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)

@[expose] def BOriginalPositionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (Kset : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J Kset →
      ∀ n, 2 ≤ n →
        ∀ e : (CoxeterMatrix.B n).Group ≃* (ggAutomizerJoin L Bs Kset),
          GGCoxeterPres p (ggAutomizerJoin L Bs Kset) (CoxeterMatrix.B n) e →
          BMarkedOriginalPositionAt p n Bs L Kset

@[expose] def BOriginalPositionTheoryInput : Prop :=
  GGTBFixInput → GGNbrInnerWeylInput → GGResXDichotomyInput → GGTCJKnown → GGLabelRigidInput →
    BOriginalPositionInput

@[expose] def GGSecFiveBProperRootInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → B ≠ Bs →
      ∀ (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
          ∃ i j : Fin n, i ≠ j ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = eta b j)

end CFSG.StandardType

end
