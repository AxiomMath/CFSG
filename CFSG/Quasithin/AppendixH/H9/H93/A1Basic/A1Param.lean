module

public import CFSG.Quasithin.AppendixH.H9.H93.A1Basic.A1Action

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

@[expose] def A1elt (ε : Fin 4 → ZMod 2) : MulAut (PairN 4) where
  toFun x := pairVec (A1fst ε x.1.toAdd x.2.toAdd) (A1snd ε x.1.toAdd x.2.toAdd)
  invFun x := pairVec (A1fst ε x.1.toAdd x.2.toAdd) (A1snd ε x.1.toAdd x.2.toAdd)
  left_inv x := by
    obtain ⟨a, b, rfl⟩ := pairVec_surj x
    exact congrArg₂ pairVec (A1fst_involutive ε a b) (A1snd_involutive ε a b)
  right_inv x := by
    obtain ⟨a, b, rfl⟩ := pairVec_surj x
    exact congrArg₂ pairVec (A1fst_involutive ε a b) (A1snd_involutive ε a b)
  map_mul' x y := by
    obtain ⟨a, b, rfl⟩ := pairVec_surj x
    obtain ⟨a', b', rfl⟩ := pairVec_surj y
    show pairVec (A1fst ε (a + a') (b + b')) (A1snd ε (a + a') (b + b')) =
      pairVec (A1fst ε a b) (A1snd ε a b) * pairVec (A1fst ε a' b') (A1snd ε a' b')
    rw [pairVec_mul, A1fst_add, A1snd_add]

theorem A1elt_pairVec (ε a b : Fin 4 → ZMod 2) :
    A1elt ε (pairVec a b) = pairVec (A1fst ε a b) (A1snd ε a b) := rfl

theorem A1elt_zero : A1elt 0 = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  exact (A1elt_pairVec 0 a b).trans (congrArg₂ pairVec (A1fst_zero a b) (A1snd_zero a b))

theorem A1elt_add (ε ε' : Fin 4 → ZMod 2) : A1elt (ε + ε') = A1elt ε * A1elt ε' := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  show pairVec (A1fst (ε + ε') a b) (A1snd (ε + ε') a b) =
    pairVec (A1fst ε (A1fst ε' a b) (A1snd ε' a b)) (A1snd ε (A1fst ε' a b) (A1snd ε' a b))
  rw [A1fst_add_left, A1snd_add_left]

@[expose] def A1hom : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4) where
  toFun e := A1elt (Multiplicative.toAdd e)
  map_one' := A1elt_zero
  map_mul' e e' := A1elt_add _ _

theorem A1hom_apply_pairVec (ε a b : Fin 4 → ZMod 2) :
    A1hom (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A1fst ε a b) (A1snd ε a b) := rfl

end CFSG.ASVolI.ChH
