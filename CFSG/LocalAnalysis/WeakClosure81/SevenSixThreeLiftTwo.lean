module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeGrp
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem s763T_map_subtype_commutator (Q : Subgroup G) :
    Subgroup.map Q.subtype (commutator ↥Q) = ⁅Q, Q⁆ := by
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

theorem relIndex_commutator_self_eq_index (Q : Subgroup G) :
    (⁅Q, Q⁆ : Subgroup G).relIndex Q = (commutator Q).index := by
  rw [← s763T_map_subtype_commutator Q, Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective Q)]

theorem card_commutator_self_eq (Q : Subgroup G) :
    Nat.card (⁅Q, Q⁆ : Subgroup G) = Nat.card (commutator Q) := by
  rw [← s763T_map_subtype_commutator Q]
  exact Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)

theorem PInvol.eq_bot_of_relIndex [Finite G] {p : ℕ} {Q : Subgroup G} {u : G}
    (h : PInvol p Q u) {N : Subgroup G} (hNQ : N ≤ Q) (hN : ∀ n ∈ N, u * n = n * u)
    (hQN : N.relIndex Q = p ∨ (N.relIndex Q = p ^ 3 ∧ ∃ x ∈ Q, ∃ y ∈ Q, ⁅x, y⁆ ∉ N)) :
    N = ⊥ := by
  set D : Subgroup G := ⁅Q, Q⁆ with hD
  have hNleD : N ≤ D := fun n hn =>
    PInvol.mem_commutator_of_commute h (hNQ hn) (hN n hn)
  have hDleQ : D ≤ Q := by rw [hD]; exact Subgroup.commutator_le_self Q
  have hrel : N.relIndex D * D.relIndex Q = N.relIndex Q :=
    Subgroup.relIndex_mul_relIndex N D Q hNleD hDleQ
  have hDindex : D.relIndex Q = (commutator ↥Q).index := by
    rw [hD]; exact relIndex_commutator_self_eq_index Q
  have hDcard : Nat.card ↥D = Nat.card ↥(commutator ↥Q) := by
    rw [hD]; exact card_commutator_self_eq Q
  have hexp : ∀ x : ↥Q, x ^ p = 1 := fun x =>
    Subtype.ext (by simpa using h.exp (x : G) x.property)
  have hcl : ∀ x y z : ↥Q, ⁅⁅x, y⁆, z⁆ = 1 := fun x y z =>
    Subtype.ext (by
      simpa [commutatorElement_def] using
        h.class_two (x : G) x.property (y : G) y.property (z : G) z.property)
  rcases hQN with hQN | ⟨hQN, x, hx, y, hy, hxy⟩
  · have hdvd : D.relIndex Q ∣ p := ⟨N.relIndex D, by rw [mul_comm, hrel, hQN]⟩
    have hle : (commutator ↥Q).index ≤ p := by
      rw [← hDindex]
      exact Nat.le_of_dvd h.prime.pos hdvd
    have hcomm : commutator ↥Q = ⊥ := commutator_eq_bot_of_index_le h.prime hexp hcl hle
    have hDbot : D = ⊥ := Subgroup.card_eq_one.mp (by rw [hDcard, hcomm, Subgroup.card_bot])
    exact le_bot_iff.mp (hNleD.trans_eq hDbot)
  · have hxyD : ⁅x, y⁆ ∈ D := by
      rw [hD]; exact Subgroup.commutator_mem_commutator hx hy
    have hNotLe : ¬ D ≤ N := fun hDN => hxy (hDN hxyD)
    have hne : N.relIndex D ≠ 1 := fun h1 =>
      hNotLe ((Subgroup.relIndex_eq_one).mp h1)
    have hdvd3 : N.relIndex D ∣ p ^ 3 :=
      ⟨D.relIndex Q, by rw [hrel, hQN]⟩
    obtain ⟨k, _hk3, hk⟩ := (Nat.dvd_prime_pow h.prime).mp hdvd3
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (by rw [hk, pow_zero])
    have hk1 : 1 ≤ k := Nat.pos_iff_ne_zero.mpr hk0
    have hrel3 : p ^ k * D.relIndex Q = p ^ 3 := by rw [← hk, hrel, hQN]
    have hpk : p ≤ p ^ k := by
      simpa using Nat.pow_le_pow_right h.prime.pos hk1
    have hpi : p * D.relIndex Q ≤ p ^ 3 := by
      have := mul_le_mul_left hpk (D.relIndex Q)
      rwa [hrel3] at this
    have hile2 : D.relIndex Q ≤ p ^ 2 :=
      Nat.le_of_mul_le_mul_left (by
        have h3 : p ^ 3 = p * p ^ 2 := by ring
        rwa [h3] at hpi) h.prime.pos
    have hQle : Nat.card ↥Q ≤ p ^ 3 :=
      card_le_of_index_commutator_le h.prime hexp hcl (by rw [← hDindex]; exact hile2)
    have hcardQ : Nat.card ↥Q = p ^ 3 * Nat.card ↥N := by
      have := Subgroup.relIndex_mul_card N Q
      rw [inf_eq_left.2 hNQ, hQN] at this
      exact this.symm
    have hNcardle : Nat.card ↥N ≤ 1 := by
      refine Nat.le_of_mul_le_mul_left ?_ (pow_pos h.prime.pos 3)
      rw [mul_one, ← hcardQ]
      exact hQle
    have hNpos : 0 < Nat.card ↥N := by
      haveI : Nonempty ↥N := ⟨(1 : ↥N)⟩
      exact Nat.card_pos
    exact Subgroup.card_eq_one.mp (le_antisymm hNcardle (Nat.succ_le_of_lt hNpos))

end CFSG.LocalAnalysis.WeakClosure81
