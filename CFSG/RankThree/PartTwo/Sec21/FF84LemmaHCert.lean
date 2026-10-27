module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.LemmaH

open Equiv

abbrev A5 : Type := alternatingGroup (Fin 5)

@[expose] def mk5 (σ : Perm (Fin 5)) (h : Perm.sign σ = 1 := by decide) : A5 :=
  ⟨σ, Perm.mem_alternatingGroup.2 h⟩

@[expose] def ind (c g : A5) : ℤ := if c = g then 1 else 0

@[expose] def cnt (L : List (ℤ × A5 × A5)) (g : A5) : ℤ :=
  (L.map fun t => t.1 * (ind t.2.2 g + ind (t.2.1 * t.2.2) g + ind (t.2.1 * t.2.1 * t.2.2) g)).sum

@[expose] def cert6 : List (ℤ × A5 × A5) := [
  (-5, mk5 (c[2, 3, 4]), mk5 (c[1, 2, 4])),
  (1, mk5 (c[2, 3, 4]), mk5 (c[0, 1, 2, 4, 3])),
  (-1, mk5 (c[2, 3, 4]), mk5 (c[0, 2, 4, 3, 1])),
  (-2, mk5 (c[1, 2, 3]), mk5 (c[0, 1, 4, 3, 2])),
  (-2, mk5 (c[1, 2, 3]), mk5 (c[0, 1, 4])),
  (5, mk5 (c[1, 2, 4]), mk5 (1)),
  (4, mk5 (c[1, 2, 4]), mk5 (c[0, 1, 4, 2, 3])),
  (1, mk5 (c[1, 2, 4]), mk5 (c[0, 3] * c[2, 4])),
  (-1, mk5 (c[1, 3, 4]), mk5 (1)),
  (1, mk5 (c[1, 3, 4]), mk5 (c[0, 1] * c[2, 4])),
  (-5, mk5 (c[1, 3, 4]), mk5 (c[0, 2] * c[3, 4])),
  (-1, mk5 (c[0, 1, 2]), mk5 (c[1, 3, 2])),
  (-3, mk5 (c[0, 1, 2]), mk5 (c[1, 4, 2])),
  (4, mk5 (c[0, 1, 2]), mk5 (c[0, 3, 2, 4, 1])),
  (-1, mk5 (c[0, 1, 2]), mk5 (c[0, 4, 1, 3, 2])),
  (-3, mk5 (c[0, 1, 3]), mk5 (c[1, 4, 2])),
  (-1, mk5 (c[0, 1, 3]), mk5 (c[1, 4] * c[2, 3])),
  (2, mk5 (c[0, 1, 4]), mk5 (1)),
  (-5, mk5 (c[0, 1, 4]), mk5 (c[2, 3, 4])),
  (1, mk5 (c[0, 1, 4]), mk5 (c[1, 3, 2])),
  (-4, mk5 (c[0, 1, 4]), mk5 (c[0, 2, 3, 4, 1])),
  (5, mk5 (c[0, 1, 4]), mk5 (c[0, 3, 2, 4, 1])),
  (1, mk5 (c[0, 1, 4]), mk5 (c[0, 3, 4, 1, 2])),
  (5, mk5 (c[0, 2, 3]), mk5 (c[2, 3, 4])),
  (8, mk5 (c[0, 2, 3]), mk5 (c[1, 3, 4])),
  (-5, mk5 (c[0, 2, 3]), mk5 (c[1, 3] * c[2, 4])),
  (10, mk5 (c[0, 2, 3]), mk5 (c[1, 4] * c[2, 3])),
  (-1, mk5 (c[0, 2, 3]), mk5 (c[0, 1] * c[2, 4])),
  (3, mk5 (c[0, 2, 3]), mk5 (c[0, 1, 4, 3, 2])),
  (-4, mk5 (c[0, 2, 4]), mk5 (c[1, 4] * c[2, 3])),
  (-2, mk5 (c[0, 2, 4]), mk5 (c[0, 3, 4, 2, 1])),
  (-9, mk5 (c[0, 2, 4]), mk5 (c[0, 3, 2, 4, 1])),
  (-5, mk5 (c[0, 2, 4]), mk5 (c[0, 3, 2])),
  (-2, mk5 (c[0, 3, 4]), mk5 (c[1, 3, 4])),
  (5, mk5 (c[0, 3, 4]), mk5 (c[1, 3] * c[2, 4])),
  (1, mk5 (c[0, 3, 4]), mk5 (c[1, 4, 2])),
  (1, mk5 (c[0, 3, 4]), mk5 (c[1, 4, 3])),
  (6, mk5 (c[0, 3, 4]), mk5 (c[0, 2, 4, 3, 1]))
]

@[expose] def cert5 : List (ℤ × A5 × A5) := [
  (1, mk5 (c[2, 3, 4]), mk5 (c[0, 2, 1])),
  (1, mk5 (c[2, 3, 4]), mk5 (c[0, 2] * c[3, 4])),
  (1, mk5 (c[1, 2, 3]), mk5 (1)),
  (1, mk5 (c[1, 2, 3]), mk5 (c[0, 1, 3, 4, 2])),
  (1, mk5 (c[1, 2, 3]), mk5 (c[0, 4] * c[2, 3])),
  (1, mk5 (c[1, 2, 4]), mk5 (c[0, 1, 2, 3, 4])),
  (1, mk5 (c[1, 2, 4]), mk5 (c[0, 3, 2])),
  (1, mk5 (c[1, 3, 4]), mk5 (c[0, 1, 4])),
  (1, mk5 (c[0, 1, 2]), mk5 (c[1, 3, 2])),
  (1, mk5 (c[0, 1, 2]), mk5 (c[1, 3, 4])),
  (1, mk5 (c[0, 1, 3]), mk5 (c[1, 3, 4])),
  (1, mk5 (c[0, 1, 3]), mk5 (c[0, 4, 2, 3, 1])),
  (1, mk5 (c[0, 1, 4]), mk5 (c[0, 2] * c[1, 3])),
  (1, mk5 (c[0, 2, 4]), mk5 (c[1, 2, 3])),
  (1, mk5 (c[0, 2, 4]), mk5 (c[1, 4, 2])),
  (1, mk5 (c[0, 3, 4]), mk5 (c[1, 4, 2])),
  (1, mk5 (c[0, 3, 4]), mk5 (c[0, 1] * c[3, 4]))
]

@[expose] def z5 : A5 := mk5 c[0, 1, 2, 3, 4]

theorem cert6_cnt : ∀ g : A5, cnt cert6 g = if g = 1 then 6 else 0 := by decide +kernel

theorem cert5_cnt : ∀ g : A5, cnt cert5 g % 2 =
    if g = 1 ∨ g = z5 ∨ g = z5 ^ 2 ∨ g = z5 ^ 3 ∨ g = z5 ^ 4 then 1 else 0 := by decide +kernel

theorem cert6_order : ∀ t ∈ cert6, t.2.1 ^ 3 = 1 ∧ t.2.1 ≠ 1 := by decide +kernel

theorem cert5_order : ∀ t ∈ cert5, t.2.1 ^ 3 = 1 ∧ t.2.1 ≠ 1 := by decide +kernel

theorem cnt_cons (t : ℤ × A5 × A5) (L : List (ℤ × A5 × A5)) (g : A5) :
    cnt (t :: L) g = t.1 * (ind t.2.2 g + ind (t.2.1 * t.2.2) g + ind (t.2.1 * t.2.1 * t.2.2) g)
      + cnt L g := by
  simp [cnt]

theorem prod_cert {A : Type*} [CommGroup A] (w : A5 → A) (L : List (ℤ × A5 × A5))
    (h : ∀ t ∈ L, w t.2.2 * w (t.2.1 * t.2.2) * w (t.2.1 * t.2.1 * t.2.2) = 1) :
    ∏ g : A5, w g ^ cnt L g = 1 := by
  induction L with
  | nil => simp [cnt]
  | cons t L ih =>
    have hL : ∀ s ∈ L, w s.2.2 * w (s.2.1 * s.2.2) * w (s.2.1 * s.2.1 * s.2.2) = 1 :=
      fun s hs => h s (List.mem_cons_of_mem _ hs)
    have hind : ∀ c : A5, ∏ g : A5, w g ^ ind c g = w c := by
      intro c
      have : ∀ g : A5, w g ^ ind c g = if c = g then w g else 1 := by
        intro g
        by_cases hcg : c = g <;> simp [ind, hcg]
      simp_rw [this]
      rw [Finset.prod_ite_eq]
      simp
    have hfirst : ∏ g : A5, w g ^ (t.1 * (ind t.2.2 g + ind (t.2.1 * t.2.2) g
        + ind (t.2.1 * t.2.1 * t.2.2) g)) = 1 := by
      have : ∀ g : A5, w g ^ (t.1 * (ind t.2.2 g + ind (t.2.1 * t.2.2) g
          + ind (t.2.1 * t.2.1 * t.2.2) g)) =
          ((w g ^ ind t.2.2 g) * (w g ^ ind (t.2.1 * t.2.2) g) *
            (w g ^ ind (t.2.1 * t.2.1 * t.2.2) g)) ^ t.1 := by
        intro g
        rw [mul_comm, zpow_mul, zpow_add, zpow_add]
      simp_rw [this]
      rw [Finset.prod_zpow, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hind, hind, hind,
        h t List.mem_cons_self, one_zpow]
    have : ∀ g : A5, w g ^ cnt (t :: L) g = w g ^ (t.1 * (ind t.2.2 g + ind (t.2.1 * t.2.2) g
        + ind (t.2.1 * t.2.1 * t.2.2) g)) * w g ^ cnt L g := by
      intro g
      rw [cnt_cons, zpow_add]
    simp_rw [this]
    rw [Finset.prod_mul_distrib, hfirst, ih hL, one_mul]

end CFSG.RankThree.PartTwo.Sec21.FF84.LemmaH
