module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open

section Transport

variable {G H : Type*} [Group G] [Group H] {A : Subgroup G} {B : Subgroup H}

theorem mem_pCoreOf_iff_of_mulEquiv (e : ↥A ≃* ↥B) (p : ℕ) (a : ↥A) :
    (a : G) ∈ pCoreOf p A ↔ ((e a : ↥B) : H) ∈ pCoreOf p B := by
  rw [pCoreOf, pCoreOf]
  change A.subtype a ∈ _ ↔ B.subtype (e a) ∈ _
  rw [Subgroup.mem_map_iff_mem A.subtype_injective,
    Subgroup.mem_map_iff_mem B.subtype_injective,
    ← CFSG.LieType.BorelTits.map_pCore_mulEquiv p e]
  exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm

noncomputable def pCoreOfMulEquiv (e : ↥A ≃* ↥B) (p : ℕ) :
    ↥(pCoreOf p A) ≃* ↥(pCoreOf p B) :=
  ((pCore p ↥A).equivMapOfInjective A.subtype A.subtype_injective).symm.trans
    ((MulEquiv.subgroupMap e (pCore p ↥A)).trans
      ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.map_pCore_mulEquiv p e)).trans
        ((pCore p ↥B).equivMapOfInjective B.subtype B.subtype_injective)))

theorem card_pCoreOf_of_mulEquiv (e : ↥A ≃* ↥B) (p : ℕ) :
    Nat.card (pCoreOf p A) = Nat.card (pCoreOf p B) :=
  Nat.card_congr (pCoreOfMulEquiv e p).toEquiv

theorem isElemAbelian_pCoreOf_of_mulEquiv (e : ↥A ≃* ↥B) {p : ℕ}
    (h : IsElemAbelian p (pCoreOf p B)) : IsElemAbelian p (pCoreOf p A) := by
  set E := pCoreOfMulEquiv e p
  refine ⟨⟨⟨fun x y => E.injective ?_⟩⟩, fun x hx => ?_⟩
  · rw [map_mul, map_mul]
    exact h.1.is_comm.comm _ _
  · have h1 : (E ⟨x, hx⟩ : H) ^ p = 1 := h.2 _ (E ⟨x, hx⟩).2
    have h2 : E (⟨x, hx⟩ ^ p) = 1 := Subtype.ext (by rw [map_pow]; exact h1)
    have h3 : (⟨x, hx⟩ : ↥(pCoreOf p A)) ^ p = 1 := E.injective (h2.trans (map_one E).symm)
    exact congrArg Subtype.val h3

theorem perfect_of_mulEquiv (e : ↥A ≃* ↥B) (h : ⁅B, B⁆ = B) : ⁅A, A⁆ = A := by
  have hB : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = (⊤ : Subgroup ↥B) := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, h]
  have hA : ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = (⊤ : Subgroup ↥A) := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective,
      hB]
  have := congrArg (Subgroup.map A.subtype) hA
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this

theorem eq_one_of_central_of_mulEquiv (e : ↥A ≃* ↥B)
    (h : ∀ b ∈ B, (∀ k ∈ B, b * k = k * b) → b = 1) {a : G} (ha : a ∈ A)
    (hc : ∀ k ∈ A, a * k = k * a) : a = 1 := by
  have h1 : ((e ⟨a, ha⟩ : ↥B) : H) = 1 := by
    apply h _ (e ⟨a, ha⟩).2
    intro k hk
    obtain ⟨k', hk'⟩ := e.surjective ⟨k, hk⟩
    have : e ⟨a, ha⟩ * e k' = e k' * e ⟨a, ha⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc k' k'.2)
    rw [hk'] at this
    exact congrArg Subtype.val this
  have h2 : e ⟨a, ha⟩ = 1 := Subtype.ext h1
  have := e.injective (h2.trans (map_one e).symm)
  exact congrArg Subtype.val this

theorem exists_three_fix_of_mulEquiv (e : ↥A ≃* ↥B) {p : ℕ}
    (h : ∃ x ∈ B, orderOf x = 3 ∧ ∃ v ∈ pCoreOf p B, v ≠ 1 ∧ v * x = x * v) :
    ∃ x ∈ A, orderOf x = 3 ∧ ∃ v ∈ pCoreOf p A, v ≠ 1 ∧ v * x = x * v := by
  obtain ⟨x, hx, ho, v, hv, hv1, hvx⟩ := h
  obtain ⟨x', hx'⟩ := e.surjective ⟨x, hx⟩
  obtain ⟨v', hv'⟩ := e.surjective ⟨v, (CFSG.LieType.BorelTits.pCoreOf_le p B) hv⟩
  refine ⟨x', x'.2, ?_, v', ?_, ?_, ?_⟩
  · rw [orderOf_submonoid, ← orderOf_injective e.toMonoidHom e.injective]
    change orderOf (e x') = 3
    rw [hx', ← orderOf_submonoid]
    exact ho
  · rw [mem_pCoreOf_iff_of_mulEquiv e p, hv']
    exact hv
  · intro h1
    apply hv1
    have : v' = 1 := Subtype.ext h1
    rw [this, map_one] at hv'
    exact (congrArg Subtype.val hv').symm
  · have : v' * x' = x' * v' := by
      apply e.injective
      rw [map_mul, map_mul, hx', hv']
      exact Subtype.ext hvx
    exact congrArg Subtype.val this

end Transport

end CFSG.Quasithin.F112R
