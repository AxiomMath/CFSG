module

public import CFSG.RankThree.PartOne.U5K.Kf.Comb
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

variable {p : ℕ} [Fact p.Prime]

theorem exists_fixed_of_involutive (π : Fin 5 → Fin 5) (hπ : ∀ i, π (π i) = i) :
    ∃ i, π i = i := by
  classical
  let g : Function.End (Fin 5) := π
  have hf : g ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext i
    exact hπ i
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  by_contra hne
  push Not at hne
  have h0 : Fintype.card (Function.fixedPoints π) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => hne x.1 x.2⟩
  rw [h0] at h
  simp [Nat.ModEq] at h

theorem card_le_of_involution {Ã : Subgroup (VM p)} (hp5 : 5 ≤ p)
    (hG : ∀ i j : Fin 5, i ≠ j → ∃ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã ∧ a i ≠ a j)
    (π : Fin 5 → Fin 5) (hπ : ∀ i, π (π i) = i)
    (hrel : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã → ∀ i j,
      a (π i) + a i = a (π j) + a j) : Nat.card Ã ≤ p ^ 3 := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_fixed_of_involutive π hπ
  have hinj : Function.Injective π := fun x y hxy => by rw [← hπ x, hxy, hπ y]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have huniq : ∀ i, π i = i → i = i₀ := by
    intro i hi
    by_contra hne
    obtain ⟨a, haÃ, hai⟩ := hG i i₀ hne
    have := hrel a haÃ i i₀
    rw [hi, hi₀] at this
    apply hai
    have h' : (2 : ZMod p) * (a i - a i₀) = 0 := by linear_combination this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left h2)
  obtain ⟨i, hi⟩ : ∃ i : Fin 5, i ≠ i₀ := exists_ne i₀
  have hii' : π i ≠ i := fun h => hi (huniq i h)
  have hi'i₀ : π i ≠ i₀ := by
    intro h
    apply hi
    rw [← hπ i, h, hi₀]
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (t := (Finset.univ : Finset (Fin 5))) (s := {i₀, i, π i}) (by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt Finset.card_le_three (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  obtain ⟨hj1, hj2, hj3⟩ := hj
  have hjj' : π j ≠ j := fun h => hj1 (huniq j h)
  have hj'i₀ : π j ≠ i₀ := by
    intro h
    apply hj1
    rw [← hπ j, h, hi₀]
  have hj'i : π j ≠ i := by
    intro h
    apply hj3
    rw [← hπ j, h]
  have hj'i' : π j ≠ π i := fun h => hj2 (hinj h)
  have hcov : ∀ t, t = i₀ ∨ t = i ∨ t = π i ∨ t = j ∨ t = π j := by
    have d01 : i₀ ≠ i := hi.symm
    have d02 : i₀ ≠ π i := hi'i₀.symm
    have d03 : i₀ ≠ j := Ne.symm hj1
    have d04 : i₀ ≠ π j := hj'i₀.symm
    have d12 : i ≠ π i := hii'.symm
    have d13 : i ≠ j := Ne.symm hj2
    have d14 : i ≠ π j := hj'i.symm
    have d23 : π i ≠ j := Ne.symm hj3
    have d24 : π i ≠ π j := hj'i'.symm
    have d34 : j ≠ π j := hjj'.symm
    have hS : ({i₀, i, π i, j, π j} : Finset (Fin 5)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin, Finset.card_insert_of_notMem (by simp [d01, d02, d03, d04]),
        Finset.card_insert_of_notMem (by simp [d12, d13, d14]),
        Finset.card_insert_of_notMem (by simp [d23, d24]),
        Finset.card_insert_of_notMem (by simp [d34]), Finset.card_singleton]
    intro t
    have : t ∈ ({i₀, i, π i, j, π j} : Finset (Fin 5)) := by rw [hS]; exact Finset.mem_univ t
    simpa using this
  refine le_trans ?_ (card_le_pow_three' (p := p) (Ã : Set (VM p)) i₀ i (π i) j (π j) hcov ?_)
  · exact le_of_eq (Nat.card_congr (Equiv.refl _))
  · intro a ha
    have e1 := hrel (Multiplicative.toAdd a) (by simpa using ha) i i₀
    have e2 := hrel (Multiplicative.toAdd a) (by simpa using ha) j i₀
    rw [hi₀] at e1 e2
    exact ⟨by linear_combination e1, by linear_combination e2⟩

end CFSG.RankThree.PartOne.U5K.Kf
