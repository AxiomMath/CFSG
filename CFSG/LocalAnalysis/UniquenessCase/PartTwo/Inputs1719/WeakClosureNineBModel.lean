module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open Subgroup CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75

abbrev P16 : Type := Equiv.Perm (Fin 16)

@[expose] def a1 : P16 where
  toFun := ![1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![6, 0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide
  right_inv := by decide

@[expose] def b1 : P16 where
  toFun := ![7, 6, 3, 2, 5, 4, 1, 0, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![7, 6, 3, 2, 5, 4, 1, 0, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide
  right_inv := by decide

@[expose] def d1 : P16 where
  toFun := ![7, 1, 4, 5, 2, 3, 6, 0, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![7, 1, 4, 5, 2, 3, 6, 0, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide
  right_inv := by decide

@[expose] def sig : P16 where
  toFun := ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide
  right_inv := by decide

@[expose] def a2 : P16 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 8, 15]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 14, 8, 9, 10, 11, 12, 13, 15]
  left_inv := by decide
  right_inv := by decide

@[expose] def b2 : P16 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 15, 14, 11, 10, 13, 12, 9, 8]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 15, 14, 11, 10, 13, 12, 9, 8]
  left_inv := by decide
  right_inv := by decide

@[expose] def d2 : P16 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 15, 9, 12, 13, 10, 11, 14, 8]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 15, 9, 12, 13, 10, 11, 14, 8]
  left_inv := by decide
  right_inv := by decide

@[expose] def u1 : P16 where
  toFun := ![2, 5, 4, 1, 7, 6, 3, 0, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![7, 3, 0, 6, 2, 1, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide
  right_inv := by decide

@[expose] def v1 : P16 where
  toFun := ![1, 0, 3, 2, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![1, 0, 3, 2, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide
  right_inv := by decide

@[expose] def u2 : P16 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 10, 13, 12, 9, 15, 14, 11, 8]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 15, 11, 8, 14, 10, 9, 13, 12]
  left_inv := by decide
  right_inv := by decide

@[expose] def v2 : P16 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 14, 15, 12, 13]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 14, 15, 12, 13]
  left_inv := by decide
  right_inv := by decide

theorem a2_eq : a2 = sig * a1 * sig := by decide
theorem b2_eq : b2 = sig * b1 * sig := by decide
theorem d2_eq : d2 = sig * d1 * sig := by decide
@[expose] def L01 : Subgroup P16 := closure {g | g ∈ [a1, b1]}

@[expose] def L02 : Subgroup P16 := closure {g | g ∈ [a2, b2]}

@[expose] def bGens : Fin 4 → List P16
  | 0 => [sig]
  | 1 => [d1 * sig]
  | 2 => [sig, d1 * d2]
  | 3 => [sig, d1]

@[expose] def GB (i : Fin 4) : Subgroup P16 := closure {g | g ∈ [a1, b1, a2, b2] ++ bGens i}

@[expose] def TB (i : Fin 4) : Subgroup P16 := closure {g | g ∈ [u1, v1, u2, v2] ++ bGens i}

@[expose] def ModelFacts915 (i : Fin 4) : Prop :=
  NineFifteenBarFacts ↥(GB i) (L01.subgroupOf (GB i)) (L02.subgroupOf (GB i))
    ((TB i).subgroupOf (GB i))

@[expose] def NGModelFacts : Prop := ∀ i : Fin 4, ModelFacts915 i

@[expose] def NGIdent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L1b L2b Tb : Subgroup X),
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsL3 ↥L1b 1 →
    (∃ t ∈ Tb, L2b = L1b.map (MulAut.conj t).toMonoidHom) → L1b ≠ L2b →
    (∀ t ∈ Tb, L1b.map (MulAut.conj t).toMonoidHom = L1b ∨
      L1b.map (MulAut.conj t).toMonoidHom = L2b) →
    ⁅L1b, L2b⁆ = ⊥ → (L1b ⊔ L2b).Normal →
    centralizer ((L1b ⊔ L2b : Subgroup X) : Set X) = ⊥ → L1b ⊔ L2b ⊔ Tb = ⊤ →
    IsSylowIn 2 Tb ⊤ →
    ∃ (i : Fin 4) (e : X ≃* ↥(GB i)), L1b.map e.toMonoidHom = L01.subgroupOf (GB i) ∧
      L2b.map e.toMonoidHom = L02.subgroupOf (GB i) ∧
      Tb.map e.toMonoidHom = (TB i).subgroupOf (GB i)

end CFSG.LocalAnalysis.WeakClosure81.NGM
