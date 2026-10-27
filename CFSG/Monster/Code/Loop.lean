module

public import CFSG.Monster.Code.Basis
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Monster.Code

@[expose] def supp (d : Fin 24 → ZMod 2) : Finset (Fin 24) := Finset.univ.filter (d · ≠ 0)

@[expose] def P (d : Fin 24 → ZMod 2) : ZMod 2 := ((hammingNorm d / 4 : ℕ) : ZMod 2)

@[expose] def K (d e : Fin 24 → ZMod 2) : ZMod 2 := (((supp d ∩ supp e).card / 2 : ℕ) : ZMod 2)

@[expose] def A (d e f : Fin 24 → ZMod 2) : ZMod 2 := ((supp d ∩ supp e ∩ supp f).card : ZMod 2)

@[expose] def β (i j : Fin 12) : ZMod 2 :=
  if i < j then 0 else if i = j then P (B i) else K (B i) (B j)

@[expose] def θc (μ ν : Fin 12 → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, μ i * ν j * β i j +
    ∑ i, ∑ j, ∑ k, if i < j then μ i * μ j * ν k * A (B i) (B j) (B k) else 0

@[expose] noncomputable def θ (d e : C) : ZMod 2 := θc (basisC.repr d) (basisC.repr e)

@[ext] structure Parker where
  code : C
  sign : ZMod 2

namespace Parker

@[expose] def equivProd : Parker ≃ C × ZMod 2 where
  toFun x := (x.code, x.sign)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Finite Parker := Finite.of_equiv _ equivProd.symm

noncomputable instance : Mul Parker :=
  ⟨fun x y => ⟨x.code + y.code, x.sign + y.sign + θ x.code y.code⟩⟩

instance : One Parker := ⟨⟨0, 0⟩⟩

@[expose] def negOne : Parker := ⟨0, 1⟩

@[expose] def omega : Parker := ⟨⟨Ω, Ω_mem_C⟩, 0⟩

@[expose] def negOmega : Parker := ⟨⟨Ω, Ω_mem_C⟩, 1⟩

theorem mul_def (x y : Parker) :
    x * y = ⟨x.code + y.code, x.sign + y.sign + θ x.code y.code⟩ := rfl

@[simp] theorem mul_code (x y : Parker) : (x * y).code = x.code + y.code := rfl

@[simp] theorem mul_sign (x y : Parker) : (x * y).sign = x.sign + y.sign + θ x.code y.code := rfl

theorem one_def : (1 : Parker) = ⟨0, 0⟩ := rfl

@[simp] theorem one_code : (1 : Parker).code = 0 := rfl

@[simp] theorem one_sign : (1 : Parker).sign = 0 := rfl

end Parker

end CFSG.Monster.Code
