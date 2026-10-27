module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaWeylAux3
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModelAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootRefl

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.StandardType.NoOffRest

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

@[expose] noncomputable def cv (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (v : V) : Fin Tag.E6.rank → ZMod 3 :=
  (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3)

theorem cv_form (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (a b : V) :
    f6 (cv hP hV a) (cv hP hV b) = 2 * B a b := by
  unfold cv
  rw [← e6ModelForm_eq_f6]
  exact e6ModelForm_e6Coord hP hV hB a b

theorem cv_mem_hypE6 (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (v : V) : kDotP 3 (cv hP hV v) = 0 :=
  e6ModelCoordVal_mem hP hV v

theorem exists_cv_eq (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) {c : Fin Tag.E6.rank → ZMod 3} (hc : kDotP 3 c = 0) :
    ∃ v : V, cv hP hV v = c :=
  ⟨(e6ModelCoord hP hV).symm ⟨c, hc⟩, by rw [cv, LinearEquiv.apply_symm_apply]⟩

end CFSG.StandardType.E6QTwo

end
