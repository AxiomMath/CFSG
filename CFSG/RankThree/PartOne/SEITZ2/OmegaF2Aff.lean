module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.CTP.Spectrum

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.RankThree.PartOne.CTP

@[ext] structure Aff (K : Type) [Field K] where
  m : SpecialLinearGroup (Fin 2) K
  b : Matrix (Fin 2) (Fin 2) K

namespace Aff

variable {K : Type} [Field K]

instance : Mul (Aff K) := ⟨fun x y => ⟨x.m * y.m, x.b + (x.m : Matrix (Fin 2) (Fin 2) K) * y.b⟩⟩

instance : One (Aff K) := ⟨⟨1, 0⟩⟩

instance : Inv (Aff K) :=
  ⟨fun x => ⟨x.m⁻¹, -((x.m⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x.b⟩⟩

@[simp] theorem mul_m (x y : Aff K) : (x * y).m = x.m * y.m := rfl

@[simp] theorem mul_b (x y : Aff K) :
    (x * y).b = x.b + (x.m : Matrix (Fin 2) (Fin 2) K) * y.b := rfl

@[simp] theorem one_m : (1 : Aff K).m = 1 := rfl

@[simp] theorem one_b : (1 : Aff K).b = 0 := rfl

@[simp] theorem inv_m (x : Aff K) : x⁻¹.m = x.m⁻¹ := rfl

@[simp] theorem inv_b (x : Aff K) :
    x⁻¹.b = -((x.m⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x.b := rfl

instance : Group (Aff K) :=
  Group.ofLeftAxioms
    (fun x y z => by
      ext1
      · simp [mul_assoc]
      · simp [Matrix.mul_add, Matrix.mul_assoc, add_assoc])
    (fun x => by
      ext1
      · simp
      · simp)
    (fun x => by
      ext1
      · simp
      · simp)

@[expose] def proj : Aff K →* SpecialLinearGroup (Fin 2) K where
  toFun x := x.m
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem proj_apply (x : Aff K) : proj x = x.m := rfl

theorem mk_one_mul (b b' : Matrix (Fin 2) (Fin 2) K) :
    (⟨1, b⟩ : Aff K) * ⟨1, b'⟩ = ⟨1, b + b'⟩ := by
  ext1
  · simp
  · simp

theorem conj_translation (n : SpecialLinearGroup (Fin 2) K) (β b : Matrix (Fin 2) (Fin 2) K) :
    (⟨n, β⟩ : Aff K) * ⟨1, b⟩ * (⟨n, β⟩ : Aff K)⁻¹ = ⟨1, (n : Matrix (Fin 2) (Fin 2) K) * b⟩ := by
  ext1
  · simp
  · simp [Matrix.mul_adjugate, ← Matrix.mul_assoc]
    try abel

end Aff

end CFSG.RankThree.PartOne.SEITZ2
