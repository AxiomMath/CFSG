module

public import CFSG.RankThree.PartOne.S12.InputsTable

public section

namespace CFSG.RankThree.PartOne

open CFSG

variable {G : Type} [Group G]

structure Table123Core [Finite G] (p : ℕ) (L A₀ F : Subgroup G) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  quasisimple : CFSG.IsQuasisimple L
  center_pPrime : ¬ p ∣ Nat.card (Subgroup.center L)
  A₀_le : A₀ ≤ L
  A₀_elem : IsElementaryAbelian p A₀
  A₀_card : Nat.card A₀ = p ^ 2
  A₀_invariant : ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
    A₀ ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A₀⁆
  F_le : F ≤ L
  F_elem : IsElementaryAbelian p F
  A₀_le_F : A₀ ≤ F
  F_le_centralizer : F ≤ Subgroup.centralizer (A₀ : Set G)
  F_max : ∀ F' : Subgroup G, F' ≤ L → IsElementaryAbelian p F' →
    F' ≤ Subgroup.centralizer (A₀ : Set G) → F ≤ F' → F' = F

theorem Table123Generic.toCore [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Generic p L A₀ F) : Table123Core p L A₀ F :=
  { prime := h.prime
    five_le := h.five_le
    quasisimple := h.quasisimple
    center_pPrime := h.center_pPrime
    A₀_le := h.A₀_le
    A₀_elem := h.A₀_elem
    A₀_card := h.A₀_card
    A₀_invariant := h.A₀_invariant
    F_le := h.F_le
    F_elem := h.F_elem
    A₀_le_F := h.A₀_le_F
    F_le_centralizer := h.F_le_centralizer
    F_max := h.F_max }

namespace Table123Core

variable [Finite G] {p : ℕ} {L A₀ F : Subgroup G}

theorem maximal (h : Table123Core p L A₀ F) :
    ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F := by
  intro F' hF'L hexp hcomm hFF'
  have hc : IsMulCommutative F' := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  have hel : IsElementaryAbelian p F' :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g => Subtype.ext (hexp _ g.2)⟩
  refine h.F_max F' hF'L hel ?_ hFF'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact hcomm a (hFF' (h.A₀_le_F ha)) x hx

theorem F_exp (h : Table123Core p L A₀ F) : ∀ f ∈ F, f ^ p = 1 := fun f hf => by
  have := h.F_elem
  exact elemPow_eq_one_of_isElementaryAbelian f hf

theorem F_comm (h : Table123Core p L A₀ F) : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.F_elem.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

end Table123Core

end CFSG.RankThree.PartOne
