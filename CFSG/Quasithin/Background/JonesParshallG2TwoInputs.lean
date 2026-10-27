module

public import CFSG.Quasithin.Background.JonesParshallG2

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.Explicit CFSG.Open

open scoped commutatorElement

section Mat

variable {F : Type} [Field F]

@[expose] def zornCoord : quasithinZorn F ≃ₗ[F] (Fin 8 → F) where
  toFun x := ![x.1, x.2.1 0, x.2.1 1, x.2.1 2, x.2.2.1 0, x.2.2.1 1, x.2.2.1 2, x.2.2.2]
  invFun c := zmk (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7)
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' c x := by
    funext i
    fin_cases i <;> rfl
  left_inv x := (zorn_eta x).symm
  right_inv c := by
    funext i
    fin_cases i <;> rfl

@[expose] def zmat (g : quasithinZorn F →ₗ[F] quasithinZorn F) : Matrix (Fin 8) (Fin 8) F :=
  LinearMap.toMatrix' (zornCoord.toLinearMap ∘ₗ g ∘ₗ zornCoord.symm.toLinearMap)

theorem zmat_comp (g h : quasithinZorn F →ₗ[F] quasithinZorn F) :
    zmat (g ∘ₗ h) = zmat g * zmat h := by
  rw [zmat, zmat, zmat, ← LinearMap.toMatrix'_comp]
  congr 1
  refine LinearMap.ext fun c => ?_
  simp

theorem zmat_id : zmat (LinearMap.id : quasithinZorn F →ₗ[F] quasithinZorn F) = 1 := by
  rw [zmat, ← LinearMap.toMatrix'_id]
  congr 1
  refine LinearMap.ext fun c => ?_
  simp

@[expose] def cmat : ↥(cayleyGroup F) →* Matrix (Fin 8) (Fin 8) F where
  toFun g := zmat (g : quasithinZorn F ≃ₗ[F] quasithinZorn F).toLinearMap
  map_one' := zmat_id
  map_mul' _ _ := zmat_comp _ _

end Mat

section Two

@[expose] def matX2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 0, 0, 0;
    1, 1, 0, 0, 1, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 1]

@[expose] def matY2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 1, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 1]

end Two

end CFSG.Quasithin.JonesParshall
