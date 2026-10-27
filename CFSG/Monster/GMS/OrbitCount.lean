module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Monster.GMS

open Subgroup

variable {G : Type*} [Group G]

theorem card_conjClass_mul_card_centralizer (a : G) :
    Nat.card {x : G // IsConj a x} * Nat.card (centralizer ({a} : Set G)) = Nat.card G := by
  have h : Nat.card {x : G // IsConj a x} = (centralizer ({a} : Set G)).index := by
    rw [index_centralizer_eq_ncard, ← Nat.card_coe_set_eq]
    rfl
  rw [h, mul_comm, card_mul_index]

private theorem index_subgroupOf_centralizer_eq_ncard (H : Subgroup G) (x : G) :
    ((centralizer ({x} : Set G)).subgroupOf H).index =
      {y : G | ∃ h ∈ H, h * x * h⁻¹ = y}.ncard := by
  rw [← MulAction.stabilizer_comap_conj_eq_centralizer_singleton, ← relIndex, relIndex_comap,
    relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]
  congr 1
  ext y
  simp [MulAction.mem_orbit_iff, Subgroup.smul_def]

variable [Finite G]

theorem card_conjClass_eq_sum_index (a : G) {n : ℕ} (b : Fin n → G)
    (hb : ∀ i, IsConj a (b i))
    (hcover : ∀ x, IsConj a x → ∃ i, ∃ g ∈ centralizer ({a} : Set G), g * b i * g⁻¹ = x)
    (hdisj : ∀ i j, ∀ g ∈ centralizer ({a} : Set G), g * b i * g⁻¹ = b j → i = j) :
    Nat.card {x : G // IsConj a x} =
      ∑ i, ((centralizer ({b i} : Set G)).subgroupOf (centralizer ({a} : Set G))).index := by
  set C := centralizer ({a} : Set G)
  let O : Fin n → Set G := fun i => {x | ∃ g ∈ C, g * b i * g⁻¹ = x}
  have hunion : {x : G | IsConj a x} = ⋃ i, O i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, g, hg, e⟩ := hcover x hx
      exact Set.mem_iUnion.2 ⟨i, g, hg, e⟩
    · intro hx
      obtain ⟨i, g, hg, rfl⟩ := Set.mem_iUnion.1 hx
      exact (hb i).trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hpair : Pairwise fun i j => Disjoint (O i) (O j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨g, hg, rfl⟩ ⟨h, hh, e⟩
    refine hij (hdisj i j (h⁻¹ * g) (C.mul_mem (C.inv_mem hh) hg) ?_)
    calc (h⁻¹ * g) * b i * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * b i * g⁻¹) * h := by simp [mul_assoc]
      _ = h⁻¹ * (h * b j * h⁻¹) * h := by rw [e]
      _ = b j := by simp [mul_assoc]
  calc Nat.card {x : G // IsConj a x} = Nat.card (⋃ i, O i) := by rw [← hunion]; rfl
    _ = Nat.card (Σ i, O i) := Nat.card_congr (Set.unionEqSigmaOfDisjoint hpair)
    _ = ∑ i, Nat.card (O i) := Nat.card_sigma
    _ = _ := Finset.sum_congr rfl fun i _ =>
        (Nat.card_coe_set_eq (O i)).trans (index_subgroupOf_centralizer_eq_ncard C (b i)).symm

theorem card_eq_card_centralizer_mul_sum (a : G) {n : ℕ} (b : Fin n → G)
    (hb : ∀ i, IsConj a (b i))
    (hcover : ∀ x, IsConj a x → ∃ i, ∃ g ∈ centralizer ({a} : Set G), g * b i * g⁻¹ = x)
    (hdisj : ∀ i j, ∀ g ∈ centralizer ({a} : Set G), g * b i * g⁻¹ = b j → i = j) :
    Nat.card G = Nat.card (centralizer ({a} : Set G)) *
      ∑ i, ((centralizer ({b i} : Set G)).subgroupOf (centralizer ({a} : Set G))).index := by
  rw [← card_conjClass_mul_card_centralizer a, card_conjClass_eq_sum_index a b hb hcover hdisj,
    mul_comm]

end CFSG.Monster.GMS
