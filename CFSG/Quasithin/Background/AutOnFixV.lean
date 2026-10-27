module

public import CFSG.Quasithin.Background.AutOnBasics

public section

namespace CFSG.Quasithin.AutOn

open CFSG.Open
open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem mem_fixV_autOn_iff {X V : Subgroup G} [IsMulCommutative V]
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (v : V) :
    v ∈ fixV (autOn X V) ↔ (v : G) ∈ Subgroup.centralizer (X : Set G) := by
  rw [fixV_autOn_eq hXV, Subgroup.mem_subgroupOf]

theorem card_fixV_autOn_eq {A W : Subgroup G} [IsMulCommutative ↥W]
    (hA : A ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card (fixV (autOn A W)) = Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := by
  have heq : fixV (autOn A W) = (W ⊓ Subgroup.centralizer (A : Set G)).subgroupOf W := by
    ext w
    rw [mem_fixV, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 := congrArg Subtype.val (h _ ⟨⟨a, hA ha⟩, ha, rfl⟩)
      change a * (w : G) * a⁻¹ = w at h1
      calc a * (w : G) = a * w * a⁻¹ * a := by group
        _ = w * a := by rw [h1]
    · rintro ⟨-, hw⟩ g ⟨x, hx, rfl⟩
      apply Subtype.ext
      change (x : G) * w * (x : G)⁻¹ = w
      rw [Subgroup.mem_centralizer_iff.mp hw x hx]
      group
  rw [heq]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

end CFSG.Quasithin.AutOn
