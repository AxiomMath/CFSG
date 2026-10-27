module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585Defs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585CharCyc
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585Inj

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem isCyclic_fullCentre_of_cyclic_coker
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    [Finite ((Fin ρ.tau.rank → ℤ) ⧸ (kernelLattice ρ ⊔ frobDefect ρ))]
    (h : IsAddCyclic ((Fin ρ.tau.rank → ℤ) ⧸ (kernelLattice ρ ⊔ frobDefect ρ))) :
    IsCyclic (fullCentre ρ) := by
  obtain ⟨f, hf⟩ := fullCentre_injects_chars ρ
  haveI : IsCyclic ↥(charKilled ρ.tau Omega (kernelLattice ρ ⊔ frobDefect ρ)) :=
    isCyclic_charKilled_of_isAddCyclic _ h
  exact isCyclic_of_injective f hf

theorem fullCentreCyclicOn_of_rowCoker
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) (h : E6RowCokerCyclic Omega row) :
    GGE6ThreeFullCentreCyclicOn1585 Omega row := by
  intro lab R _ I phi ρ j hlab hj hqs hrow
  obtain ⟨hfin, hcyc⟩ := h lab R I phi ρ j hlab hj hqs hrow
  haveI := hfin
  exact isCyclic_fullCentre_of_cyclic_coker ρ hcyc

end CFSG.StandardType.E6Centralizer1585

end
