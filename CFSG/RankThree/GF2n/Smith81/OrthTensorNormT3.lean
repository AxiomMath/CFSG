module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormKron

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

open CFSG.RankThree.GF2n.Smith81.Smith23E1

section T3

variable {K : Type} [Field K]

@[expose] def tensor3Cube (K : Type) [Field K] : Tensor3 K ≃ₗ[K] Cube 3 K where
  toFun T x := T (x 0) (x 1) (x 2)
  invFun C a b c := C ![a, b, c]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv T := by
    funext a b c
    simp
  right_inv C := by
    funext x
    have : (![x 0, x 1, x 2] : Fin 3 → Fin 2) = x := by
      funext i
      fin_cases i <;> rfl
    simp [this]

theorem tensor3Cube_apply (T : Tensor3 K) (x : Fin 3 → Fin 2) :
    tensor3Cube K T x = T (x 0) (x 1) (x 2) := rfl

theorem tensor3Cube_act0 (A : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Cube K (tensor3Act0 A T) = actMap 0 A (tensor3Cube K T) := by
  funext x
  rw [actMap_apply, tensor3Cube_apply]
  simp [tensor3Act0, tensor3Cube_apply, Function.update_apply]

theorem tensor3Cube_act1 (A : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Cube K (tensor3Act1 A T) = actMap 1 A (tensor3Cube K T) := by
  funext x
  rw [actMap_apply, tensor3Cube_apply]
  simp [tensor3Act1, tensor3Cube_apply, Function.update_apply]

theorem tensor3Cube_act2 (A : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Cube K (tensor3Act2 A T) = actMap 2 A (tensor3Cube K T) := by
  funext x
  rw [actMap_apply, tensor3Cube_apply]
  simp [tensor3Act2, tensor3Cube_apply, Function.update_apply]

end T3

end CFSG.RankThree.GF2n.Smith81.OrthTN

end
