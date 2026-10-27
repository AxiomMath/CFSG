module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.Sporadic.ThSchreier.GlobalData

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def A1EightInnAutDerived : Prop :=
  ∀ (Q : Type) [Group Q], GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) Q →
    ∀ β ∈ innAutDerived Q, ∃ y : Q, ∀ q : Q, β q = y * q * y⁻¹

@[expose] def ConnectedNativeAction : Prop :=
  ∀ (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (rho : GGK0MarkedKacIface1587.MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin rho.row.D.orbits.length),
    rho.row.D.orbits[j].qs = true →
      ∀ g : rho.setup.D.model,
        (g : ModGL rho.tau Omega) ∈ E6Centralizer1585.connectedCentralizer rho →
        (∀ d ∈ E6Centralizer1585.component rho j,
          rho.modelAction g d ∈ E6Centralizer1585.component rho j) →
        GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
          (↥(E6Centralizer1585.component rho j) ⧸
            Subgroup.center ↥(E6Centralizer1585.component rho j)) →
        ∃ β ∈ innAutDerived
            (↥(E6Centralizer1585.component rho j) ⧸
              Subgroup.center ↥(E6Centralizer1585.component rho j)),
          ∀ d d' : ↥(E6Centralizer1585.component rho j),
            rho.modelAction g (d : R) = (d' : R) →
            (d' : ↥(E6Centralizer1585.component rho j) ⧸
                Subgroup.center ↥(E6Centralizer1585.component rho j)) =
              β (d : ↥(E6Centralizer1585.component rho j) ⧸
                    Subgroup.center ↥(E6Centralizer1585.component rho j))

theorem corner1584_connected_of_pieces (hA : ConnectedNativeAction) (hB : A1EightInnAutDerived) :
    corner1584_connected := by
  intro Omega _ _ _ lab R _ I phi rho j hqs g hg hpres hlab
  obtain ⟨β, hβ, hact⟩ := hA Omega lab R I phi rho j hqs g hg hpres hlab
  obtain ⟨y, hy⟩ := hB _ hlab β hβ
  exact ⟨y, fun d d' h => by rw [hact d d' h, hy]⟩

end CFSG.StandardType.KD2Pieces1615

end
