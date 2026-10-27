module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.StandardType

namespace E6Dep

abbrev Vec6 : Type := Fin 6 → ZMod 3

abbrev Mat6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 3)

@[expose] def reflMat (α h : Vec6) : Mat6 := 1 - Matrix.vecMulVec h α

@[expose] def hJ : Fin 5 → Vec6 :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
    ![1, 2, 0, 1, 0, 0]]

@[expose] def aJ : Fin 5 → Vec6 :=
  ![![2, 2, 0, 0, 0, 0], ![2, 2, 2, 0, 0, 0], ![0, 2, 2, 2, 0, 0], ![0, 0, 2, 2, 0, 0],
    ![0, 0, 0, 2, 0, 0]]

@[expose] def h0 : Vec6 := ![2, 1, 0, 0, 0, 0]

@[expose] def a0 : Vec6 := ![0, 0, 2, 0, 0, 0]

@[expose] def xs : Vec6 := ![0, 0, 0, 0, 1, 0]

@[expose] def xx : Vec6 := ![0, 0, 0, 0, 0, 1]

@[expose] def hB : Vec6 := h0 + xs

@[expose] def aB : Vec6 := a0 + (2 : ZMod 3) • xs

@[expose] def hA (s t : ZMod 3) : Vec6 := h0 + s • xs + t • xx

@[expose] def aA (u w : ZMod 3) : Vec6 := a0 + u • xs + w • xx

@[expose] def gensL : Fin 6 → Mat6 :=
  ![reflMat (aJ 0) (hJ 0), reflMat (aJ 1) (hJ 1), reflMat (aJ 2) (hJ 2), reflMat (aJ 3) (hJ 3),
    reflMat (aJ 4) (hJ 4), reflMat aB hB]

@[expose] def gensAll (s t u w : ZMod 3) : Fin 7 → Mat6 :=
  ![reflMat (aJ 0) (hJ 0), reflMat (aJ 1) (hJ 1), reflMat (aJ 2) (hJ 2), reflMat (aJ 3) (hJ 3),
    reflMat (aJ 4) (hJ 4), reflMat aB hB, reflMat (aA u w) (hA s t)]

@[expose] def evalWord {n : ℕ} (g : Fin n → Mat6) : List (Fin n) → Mat6
  | [] => 1
  | i :: l => g i * evalWord g l

@[expose] def closureL : Submonoid Mat6 := Submonoid.closure (Set.range gensL)

@[expose] def IsTv6 (g : Mat6) : Prop :=
  Fintype.card {v : Vec6 // g.mulVec v = v} * 3 = 3 ^ 6 ∧
    ∀ v : Vec6, g.mulVec (g.mulVec v - v) = g.mulVec v - v

instance (g : Mat6) : Decidable (IsTv6 g) := by unfold IsTv6; infer_instance

@[expose] def gram6 : Mat6 :=
  !![1, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def bil6 (u v : Vec6) : ZMod 3 := u ⬝ᵥ gram6.mulVec v

@[expose] def norm6 (v : Vec6) : ZMod 3 := bil6 v v

@[expose] def reflNorm (v : Vec6) : Mat6 := reflMat ((2 : ZMod 3) • gram6.mulVec v) v

end E6Dep

end CFSG.StandardType

end
