module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Uniqueness of a normal order-`p` Sylow subgroup
-/

noncomputable section
namespace CFSG.GorensteinWalter
universe u

/-- Two order-`p` subgroups of a finite group are equal when the first is
normal Sylow and both have `p`-prime, index-free subgroup-of realizations. -/
public theorem secondCase_linear_eq_of_normal_sylow
    {G : Type u} [Group G] [Finite G]
    (D X₁ X₂ : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hX₁le : X₁ ≤ D) (hX₂le : X₂ ≤ D)
    (hX₁card : Nat.card X₁ = p) (hX₂card : Nat.card X₂ = p)
    (hidx₁ : ¬ p ∣ (X₁.subgroupOf D).index)
    (hidx₂ : ¬ p ∣ (X₂.subgroupOf D).index)
    (hDleN₁ : D ≤ Subgroup.normalizer (X₁ : Set G)) : X₁ = X₂ := by
  let X₁D : Subgroup D := X₁.subgroupOf D
  let X₂D : Subgroup D := X₂.subgroupOf D
  have hX₁Dcard : Nat.card X₁D = p := by
    calc
      Nat.card X₁D = Nat.card (X₁D.map D.subtype) :=
        (Subgroup.card_map_of_injective D.subtype_injective).symm
      _ = Nat.card X₁ := by
        rw [show X₁D.map D.subtype = X₁ by
          dsimp [X₁D]
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hX₁le]]
      _ = p := hX₁card
  have hX₂Dcard : Nat.card X₂D = p := by
    calc
      Nat.card X₂D = Nat.card (X₂D.map D.subtype) :=
        (Subgroup.card_map_of_injective D.subtype_injective).symm
      _ = Nat.card X₂ := by
        rw [show X₂D.map D.subtype = X₂ by
          dsimp [X₂D]
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hX₂le]]
      _ = p := hX₂card
  have hX₁p : IsPGroup p X₁D :=
    IsPGroup.of_card (n := 1) (by simpa [hX₁Dcard])
  have hX₂p : IsPGroup p X₂D :=
    IsPGroup.of_card (n := 1) (by simpa [hX₂Dcard])
  let S₁ : Sylow p D := hX₁p.toSylow (by simpa [X₁D] using hidx₁)
  let S₂ : Sylow p D := hX₂p.toSylow (by simpa [X₂D] using hidx₂)
  have hX₁normal : X₁D.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX₁le).2 hDleN₁
  have hS₁normal : (S₁ : Subgroup D).Normal := by
    simpa [S₁] using hX₁normal
  let : Unique (Sylow p D) := Sylow.unique_of_normal S₁ hS₁normal
  have hS : S₁ = S₂ := Subsingleton.elim _ _
  have hsub : X₁D = X₂D := by
    change (S₁ : Subgroup D) = (S₂ : Subgroup D)
    rw [hS]
  have hmap := congrArg (fun H : Subgroup D => H.map D.subtype) hsub
  simpa [X₁D, X₂D, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hX₁le, inf_eq_left.mpr hX₂le] using hmap

end CFSG.GorensteinWalter
