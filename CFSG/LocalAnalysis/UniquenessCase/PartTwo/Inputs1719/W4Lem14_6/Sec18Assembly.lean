module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsXMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

private theorem realizesVia_of_isoMod_of_secIsoOn {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    {D : FFModel} {π : D.Gam →* ↥X} {I J : Subgroup W}
    (hI : D.RealizesVia X I ⊥ π) (h : SecIsoOn X I ⊥ J ⊥) :
    D.RealizesVia X J ⊥ π := by
  obtain ⟨e, he⟩ := iso_of_secIsoOn_bot h
  exact realizesVia_of_isoMod hI
    ⟨e, fun x hx w hw => (he ⟨x, hx⟩ w ⟨x w, hw⟩ rfl).symm⟩

theorem sumOfNatVia_of_secIsoOn {W : Type} [CommGroup W] [Finite W] {X : Subgroup (MulAut W)}
    {D : FFModel} {π : D.Gam →* ↥X} {I : Subgroup W} (hI : D.RealizesVia X I ⊥ π) {k : ℕ}
    (J : Fin k → Subgroup W) (hiso : ∀ i, SecIsoOn X I ⊥ (J i) ⊥)
    (hind : iSupIndep J) (htop : (⨆ i, J i) = ⊤) :
    SumOfNatVia D X ⊤ ⊥ k π := by
  refine ⟨J, fun i => bot_le, fun i => ?_, by simpa using htop,
    fun i => realizesVia_of_isoMod_of_secIsoOn hI (hiso i)⟩
  have hd : Disjoint (J i) (⨆ (j : Fin k) (_ : j ≠ i), J j) := by
    simpa using hind i
  rw [bot_sup_eq]
  exact le_of_eq (disjoint_iff.mp hd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
