module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.Quasithin

open Equiv Equiv.Perm
open scoped Pointwise

theorem not_nine_dvd_card_centralizer_of_sq {z : Perm (Fin 7)} (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    ¬ 9 ∣ Nat.card (Subgroup.centralizer {z}) := by
  have hord : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
  have hmem : ∀ n ∈ z.cycleType, n = 2 := by
    intro n hn
    have h1 : n ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans hord
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2
  have hrep : z.cycleType = Multiset.replicate (Multiset.card z.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hmem
  have hk1 : 1 ≤ Multiset.card z.cycleType := by
    rcases Nat.eq_zero_or_pos (Multiset.card z.cycleType) with h | h
    · exact absurd (Equiv.Perm.card_cycleType_eq_zero.mp h) hz1
    · exact h
  have hsum := Equiv.Perm.sum_cycleType_le z
  rw [hrep] at hsum
  simp only [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  rw [Equiv.Perm.nat_card_centralizer]
  generalize hk : Multiset.card z.cycleType = k at hrep hk1 hsum
  rw [hrep]
  have hk3 : k ≤ 3 := by omega
  interval_cases k <;> decide

theorem false_of_card_nine_centralizes {z : Perm (Fin 7)} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    {E : Subgroup (Perm (Fin 7))} (hE : Nat.card ↥E = 9) (hc : ∀ g ∈ E, g * z = z * g) : False := by
  have hle : E ≤ Subgroup.centralizer {z} := fun g hg => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (hc g hg).symm
  exact not_nine_dvd_card_centralizer_of_sq hz1 hz2 (hE ▸ Subgroup.card_dvd_of_le hle)

theorem smul_pair_mem_of_mem_stabilizer {P : Finset (Finset (Fin 7))} {g : Perm (Fin 7)}
    (hg : g ∈ MulAction.stabilizer (Perm (Fin 7)) P) {x y : Fin 7}
    (h : ({x, y} : Finset (Fin 7)) ∈ P) : ({g x, g y} : Finset (Fin 7)) ∈ P := by
  rw [MulAction.mem_stabilizer_iff] at hg
  have h1 : g • ({x, y} : Finset (Fin 7)) ∈ g • P := Finset.smul_mem_smul_finset h
  rw [hg] at h1
  simpa [Finset.smul_finset_insert, Equiv.Perm.smul_def] using h1

theorem exists_involution_of_two_block {P : Finset (Finset (Fin 7))}
    (hdisj : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B')
    (h2 : ∃ B ∈ P, B.card = 2) :
    ∃ z : Perm (Fin 7), z ≠ 1 ∧ z * z = 1 ∧
      ∀ g ∈ MulAction.stabilizer (Perm (Fin 7)) P, g * z = z * g := by
  classical
  let R : Fin 7 → Fin 7 → Prop := fun x y => y ≠ x ∧ ({x, y} : Finset (Fin 7)) ∈ P
  have R_symm : ∀ {x y}, R x y → R y x := by
    rintro x y ⟨hne, hP⟩
    exact ⟨hne.symm, by rwa [Finset.pair_comm]⟩
  have R_unique : ∀ {x y y'}, R x y → R x y' → y = y' := by
    rintro x y y' ⟨hne, hP⟩ ⟨hne', hP'⟩
    by_cases heq : ({x, y} : Finset (Fin 7)) = {x, y'}
    · have : y ∈ ({x, y'} : Finset (Fin 7)) :=
        heq ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
      rcases Finset.mem_insert.mp this with h | h
      · exact absurd h hne
      · exact Finset.mem_singleton.mp h
    · exfalso
      have hd := hdisj _ hP _ hP' heq
      exact Finset.disjoint_left.mp hd (Finset.mem_insert_self x {y})
        (Finset.mem_insert_self x {y'})
  let f : Fin 7 → Fin 7 := fun x => if h : ∃ y, R x y then Classical.choose h else x
  have f_spec : ∀ x, (∃ y, R x y) → R x (f x) := by
    intro x hx
    have : f x = Classical.choose hx := by simp [f, hx]
    rw [this]
    exact Classical.choose_spec hx
  have f_none : ∀ x, ¬ (∃ y, R x y) → f x = x := by
    intro x hx
    simp [f, hx]
  have f_inv : Function.Involutive f := by
    intro x
    by_cases hx : ∃ y, R x y
    · have h1 := f_spec x hx
      have h2 := R_symm h1
      have h3 := f_spec (f x) ⟨x, h2⟩
      exact (R_unique h2 h3).symm
    · rw [f_none x hx, f_none x hx]
  have f_equiv : ∀ g ∈ MulAction.stabilizer (Perm (Fin 7)) P, ∀ x, f (g x) = g (f x) := by
    intro g hg x
    have hRg : ∀ {x y}, R x y → R (g x) (g y) := by
      rintro x y ⟨hne, hP⟩
      exact ⟨fun h => hne (g.injective h), smul_pair_mem_of_mem_stabilizer hg hP⟩
    by_cases hx : ∃ y, R x y
    · exact R_unique (f_spec (g x) ⟨g (f x), hRg (f_spec x hx)⟩) (hRg (f_spec x hx))
    · have hgx : ¬ ∃ y, R (g x) y := by
        rintro ⟨y, hy⟩
        apply hx
        have hg' : g⁻¹ ∈ MulAction.stabilizer (Perm (Fin 7)) P := inv_mem hg
        have hRg' : ∀ {x y}, R x y → R (g⁻¹ x) (g⁻¹ y) := by
          rintro x y ⟨hne, hP⟩
          exact ⟨fun h => hne (g⁻¹.injective h), smul_pair_mem_of_mem_stabilizer hg' hP⟩
        exact ⟨g⁻¹ y, by simpa using hRg' hy⟩
      rw [f_none x hx, f_none (g x) hgx]
  obtain ⟨B, hB, hcard⟩ := h2
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  refine ⟨f_inv.toPerm f, ?_, ?_, ?_⟩
  · intro h1
    have h3 := f_spec a ⟨b, hab.symm, hB⟩
    have h4 : f a = a := by
      have := congrArg (fun p : Perm (Fin 7) => p a) h1
      simpa using this
    exact h3.1 h4
  · ext x
    simp [f_inv x]
  · intro g hg
    ext x
    simp [f_equiv g hg x]

theorem false_of_card_nine_le_stabilizer {P : Finset (Finset (Fin 7))}
    (hdisj : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B') (h2 : ∃ B ∈ P, B.card = 2)
    {E : Subgroup (Perm (Fin 7))} (hE : Nat.card ↥E = 9)
    (hle : E ≤ MulAction.stabilizer (Perm (Fin 7)) P) : False := by
  obtain ⟨z, hz1, hz2, hz⟩ := exists_involution_of_two_block hdisj h2
  exact false_of_card_nine_centralizes hz1 hz2 hE fun g hg => hz g (hle hg)

end CFSG.Quasithin
