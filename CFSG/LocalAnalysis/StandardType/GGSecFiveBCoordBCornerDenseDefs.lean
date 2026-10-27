module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePermNbrLabelOfJDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG.Open

@[expose] def GGSecFiveBCoordBCornerAbsorbInput : Prop :=
  GGResXDichotomyInput → GGTCJKnown → GGLabelRigidInput → GGNbrTablePNbrInputNarrow →
  GGForkA8NotReflInput → GGRawInnFieldInput → GGRawInndiagIsoInput →
  GGResNbrFixCentralizesInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 → B ≠ Bs →
  ∀ (n r : ℕ), 2 ≤ r → ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))),
    (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3 →
    (∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
  ∀ (π : Fin (r + 2) ≃ Fin n) (κ : StatedSp (r + 1) (GaloisField 2 1) →* G)
    (ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)),
    GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ →
    (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 (π 0) →
  ∀ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
    MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)) →
  ∀ K ∈ 𝒦, K ≤ L ⊔ L.map (MulAut.conj g).toMonoidHom ∨ GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K

section Inputs


@[expose] def GGSecFiveBCoordBCornerPlaneFrameInput : Prop :=
  GGInnerDiagMpInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 →
  ∀ (s : ℕ), 2 ≤ s → ∀ (eta : ↥Bs ≃* (Fin (s + 3) → Multiplicative (ZMod 3))) (i0 : Fin (s + 3)),
    (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (s + 3) 3 i0 →
    GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = s + 2 ∧
      lab.n = 1) 3 Bs L →
    ∃ π : Fin (s + 3) ≃ Fin (s + 3), π 0 = i0 ∧
      ∃ (κ : StatedSp (s + 2) (GaloisField 2 1) →* G)
        (ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)),
        GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ

@[expose] def GGSecFiveBCoordBCornerDenseInput : Prop :=
  GGInnerDiagMpInput → GGResXDichotomyInput → GGTCJKnown → GGLabelRigidInput →
  GGNbrTablePNbrInputNarrow → GGForkA8NotReflInput → GGRawInnFieldInput → GGRawInndiagIsoInput →
  GGResNbrFixCentralizesInput → GGSecFivePermNbrLabelOfJInput → GGU62OuterDiagInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ 5 ≤ n ∧
          (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3) p Bs L →
        B ≠ Bs →
        ((∃ i, i ≠ i0 ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = 1)) ∨
          ∃ i j, i ≠ j ∧ i ≠ i0 ∧ j ≠ i0 ∧
            ((∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = eta b j)) ∨
              ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = (eta b j)⁻¹))) →
        GGSecFiveBCoordBCornerRowsRest B Bs x L D J (n - 1) →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
      ∀ (r : ℕ) (π : Fin (r + 2) ≃ Fin n) (κ : StatedSp (r + 1) (GaloisField 2 1) →* G)
        (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)),
        π 0 = i0 → GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ →
      ∀ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)), g ∈ ggG0 p B x L D J →
        MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)) →
      ∀ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K →
        K ≤ L ⊔ L.map (MulAut.conj g).toMonoidHom

end Inputs

end CFSG.StandardType

end
