module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Census

theorem card_centralizer_subgroup {M : Type*} [Group M] (K : Subgroup M) (t : K) :
    Nat.card (Subgroup.centralizer ({t} : Set K)) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({(t : M)} : Set M)) := by
  rw [← Subgroup.card_map_of_injective K.subtype_injective]
  congr 2
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, congrArg Subtype.val hy⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxt, rfl⟩

theorem card_centralizer_mulEquiv {U V : Type*} [Group U] [Group V] (e : U ≃* V) (a : U) :
    Nat.card (Subgroup.centralizer ({a} : Set U)) =
      Nat.card (Subgroup.centralizer ({e a} : Set V)) :=
  Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun g => by
    simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    rw [← map_mul, ← map_mul, e.injective.eq_iff])

theorem card_inf_centralizer_conj {M : Type*} [Group M] (K : Subgroup M) {c : M}
    (hc : ∀ m ∈ K, c * m * c⁻¹ ∈ K) (hc' : ∀ m ∈ K, c⁻¹ * m * c ∈ K) (t : M) :
    Nat.card ↥(K ⊓ Subgroup.centralizer ({c * t * c⁻¹} : Set M)) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({t} : Set M)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨c⁻¹ * x * c, hc' _ x.2.1, ?_⟩
      invFun := fun y => ⟨c * y * c⁻¹, hc _ y.2.1, ?_⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group) }
  · have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc c⁻¹ * x * c * t = c⁻¹ * (x * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * x) * c := by rw [hx]
      _ = t * (c⁻¹ * x * c) := by group
  · have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2.2
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc c * y * c⁻¹ * (c * t * c⁻¹) = c * (y * t) * c⁻¹ := by group
      _ = c * (t * y) * c⁻¹ := by rw [hy]
      _ = c * t * c⁻¹ * (c * y * c⁻¹) := by group

theorem card_centralizer_of_isConj {U : Type*} [Group U] {a b : U} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set U)) =
      Nat.card (Subgroup.centralizer ({b} : Set U)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have e := card_inf_centralizer_conj (⊤ : Subgroup U) (c := c) (fun _ _ => trivial)
    (fun _ _ => trivial) a
  rw [top_inf_eq, top_inf_eq] at e
  exact e.symm

end CFSG.RankThree.PartTwo.Census
