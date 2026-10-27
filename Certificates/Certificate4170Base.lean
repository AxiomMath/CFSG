
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Inputs

@[expose] public section

open scoped Pointwise

namespace CFSG.Quasithin.A312M23

open CFSG.Quasithin.A312Words

variable {G : Type} [Group G]

@[expose] def M22Facts (α : Type) [MulAction G α] (Y : Subgroup G) : Prop :=
  ∃ (pt : Fin 22 → α) (hpt : Function.Injective pt) (hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j)
    (eA eB : G), eA ∈ Y ∧ eB ∈ Y ∧
    (∀ i, (rhoFn Y pt hpt hYp eA i).val = m22TabA.toList.getD i.val 0) ∧
    ∀ i, (rhoFn Y pt hpt hYp eB i).val = m22TabB.toList.getD i.val 0

@[expose] def L34Facts (Y : Subgroup G) : Prop :=
  ∃ (ol : List G) (t : G), IdxTwoData Y ol t ∧
    (∀ v ∈ Subgroup.closure {g | g ∈ ol}, t⁻¹ * v * t ∈ Subgroup.closure {g | g ∈ ol}) ∧
    ∃ u v : G, u ∈ Subgroup.closure {g | g ∈ ol} ∧ v ∈ Subgroup.closure {g | g ∈ ol} ∧
      (∀ w ∈ CFSG.LieType.Multipliers.L34.rels.map (List.map fun l => (l.1.val, l.2)),
        CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 u v) w = 1) ∧
      ∀ g ∈ ol, g ∈ Subgroup.closure ({u, v} : Set G)

@[expose] def E2Facts (α : Type) [MulAction G α] (Y : Subgroup G) (k m r : ℕ) (alt tr : Bool) :
    Prop :=
  ∃ (ol : List G) (t : G), IdxTwoData Y ol t ∧
    (alt = true →
      (∀ v ∈ Subgroup.closure {g | g ∈ ol}, t⁻¹ * v * t ∈ Subgroup.closure {g | g ∈ ol}) ∧
        t ∉ Subgroup.closure {g | g ∈ ol}) ∧
    (alt = false → t = 1) ∧
    ∃ (pt : Fin m → α) (hpt : Function.Injective pt) (hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j)
      (vl : List G), (∀ v ∈ vl, v ∈ Subgroup.closure {g | g ∈ ol}) ∧
      (∀ g ∈ ol ++ [t], ∀ v ∈ Subgroup.closure {v | v ∈ vl},
        g⁻¹ * v * g ∈ Subgroup.closure {v | v ∈ vl}) ∧
      (∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a) ∧ (∀ a ∈ vl, a * a = 1) ∧
      (∀ a ∈ vl, ∀ i, a • pt i = pt i) ∧ Nat.card (Subgroup.closure {v | v ∈ vl}) = 2 ^ k ∧
      Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)}) = r ∧
      (tr = true → ∀ i j : Fin m,
        ∃ e ∈ Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)}, e i = j)

@[expose] def TriFacts (α : Type) [MulAction G α] (Y : Subgroup G) : Prop :=
  ∃ (pt : Fin 3 → α) (_ : Function.Injective pt), (∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) ∧
    ∃ x ∈ Y, ∃ k, k % 2 = 1 ∧ x ^ k = 1 ∧ ∃ i, x • pt i ≠ pt i

end CFSG.Quasithin.A312M23

