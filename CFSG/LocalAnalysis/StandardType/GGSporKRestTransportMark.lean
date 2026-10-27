module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint

theorem ggSporKRest_marking_true_of_marking {L : Type} [Group L] {P : LargeEvenMarkProp L}
    (h : LargeEvenMarking L P) : LargeEvenMarking L (fun _ _ _ _ _ _ => True) := by
  exact largeEvenMarking_congr (MulEquiv.refl L) (fun _ _ _ _ _ _ _ => trivial) h

theorem ggSporKRest_marking_true_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : LargeEvenMarking L (fun _ _ _ _ _ _ => True)) :
    LargeEvenMarking L' (fun _ _ _ _ _ _ => True) := by
  exact largeEvenMarking_congr e.symm (fun _ _ _ _ _ _ _ => trivial) h

theorem SporKRestUnmarked.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : SporKRestUnmarked X) : SporKRestUnmarked X' := by
  intro C' hC' hmark'
  let Q : X ⧸ CFSG.pCore 2 X ≃* X' ⧸ CFSG.pCore 2 X' :=
    QuotientGroup.congr (CFSG.pCore 2 X) (CFSG.pCore 2 X') e (CFSG.pCore_map_iso 2 e)
  let C : Subgroup (X ⧸ CFSG.pCore 2 X) := C'.map Q.symm.toMonoidHom
  have hC : IsComponentOf C ⊤ := by
    have hmap := isComponentOf_map_mulEquiv' Q.symm hC'
    simpa [C, Subgroup.map_equiv_top] using hmap
  have hmarkC : LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) :=
    ggSporKRest_marking_true_of_mulEquiv
      (C'.equivMapOfInjective Q.symm.toMonoidHom Q.symm.injective) hmark'
  exact h C hC hmarkC

end CFSG.StandardType.SporadicShape
