module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.AutQ8D8

open MulAction

variable {Q : Type*} [Group Q]

def fixSub (g : MulAut Q) : Subgroup Q where
  carrier := {x | g x = x}
  one_mem' := map_one g
  mul_mem' := fun {a b} (ha : g a = a) (hb : g b = b) => by
    show g (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} (ha : g a = a) => by
    show g a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixSub {g : MulAut Q} {x : Q} : x ∈ fixSub g ↔ g x = x := Iff.rfl

theorem fixedPoints_zpowers (g : MulAut Q) :
    fixedPoints (Subgroup.zpowers g) Q = (fixSub g : Set Q) := by
  ext x
  constructor
  · intro hx
    exact hx ⟨g, Subgroup.mem_zpowers g⟩
  · intro hx m
    obtain ⟨m, hm⟩ := m
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact mem_fixedBy_zpow (α := Q) (g := g) (a := x) hx j

theorem card_modEq_fixSub [Finite Q] (g : MulAut Q) {r k : ℕ} [Fact r.Prime]
    (hg : orderOf g = r ^ k) : Nat.card Q ≡ Nat.card (fixSub g) [MOD r] := by
  have hP : IsPGroup r (Subgroup.zpowers g) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hg])
  have h := hP.card_modEq_card_fixedPoints Q
  have e : Nat.card (fixedPoints (Subgroup.zpowers g) Q) = Nat.card (fixSub g) :=
    congrArg (fun s : Set Q => Nat.card s) (fixedPoints_zpowers g)
  rwa [e] at h

theorem fixSub_eq_top {g : MulAut Q} (h : fixSub g = ⊤) : g = 1 := by
  ext x
  have hx : x ∈ fixSub g := by rw [h]; exact Subgroup.mem_top x
  exact hx

theorem card_fixSub_dvd [Finite Q] (g : MulAut Q) : Nat.card (fixSub g) ∣ Nat.card Q :=
  Subgroup.card_subgroup_dvd_card _

theorem card_fixSub_lt [Finite Q] {g : MulAut Q} (hg : g ≠ 1) :
    Nat.card (fixSub g) < Nat.card Q := by
  refine lt_of_le_of_ne (Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective) ?_
  intro h
  exact hg (fixSub_eq_top (Subgroup.eq_top_of_card_eq _ h))

theorem card_fixSub_cases [Finite Q] {n : ℕ} (hQ : Nat.card Q = 2 ^ n) {g : MulAut Q}
    (hg1 : g ≠ 1) {r k : ℕ} [Fact r.Prime] (hg : orderOf g = r ^ k) :
    ∃ j : ℕ, j < n ∧ Nat.card (fixSub g) = 2 ^ j ∧ 2 ^ j ≡ 2 ^ n [MOD r] := by
  have h1 := card_fixSub_dvd g
  have h2 := card_modEq_fixSub g hg
  have h3 := card_fixSub_lt hg1
  rw [hQ] at h1 h2 h3
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  refine ⟨j, ?_, hj', ?_⟩
  · by_contra hcon
    have : j = n := by omega
    subst this
    omega
  · rw [hj'] at h2
    exact h2.symm

theorem not_seventeen_dvd_card_mulAut [Finite Q] (hQ : Nat.card Q = 32) :
    ¬ 17 ∣ Nat.card (MulAut Q) := by
  intro h
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 17 h
  have hg1 : g ≠ 1 := by
    rintro rfl
    simp at hg
  have hQ5 : Nat.card Q = 2 ^ 5 := by rw [hQ]; norm_num
  obtain ⟨j, hj, -, hmod⟩ := card_fixSub_cases hQ5 hg1 (r := 17) (k := 1) (by simpa using hg)
  unfold Nat.ModEq at hmod
  interval_cases j <;> omega

theorem five_le_card_fixSub [Finite Q] (hT : Nat.card {x : Q // x * x = 1} = 12)
    {g : MulAut Q} (hg : orderOf g = 7) : 5 ≤ Nat.card (fixSub g) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP : IsPGroup 7 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg]; simp)
  let Tsub : SubMulAction (Subgroup.zpowers g) Q :=
    { carrier := {x | x * x = 1}
      smul_mem' := fun c x hx => by
        have : (c : MulAut Q) x * (c : MulAut Q) x = 1 := by
          rw [← map_mul, show x * x = 1 from hx, map_one]
        exact this }
  have h := hP.card_modEq_card_fixedPoints Tsub
  have hcard : Nat.card Tsub = 12 := hT
  have hle : Nat.card (fixedPoints (Subgroup.zpowers g) Tsub) ≤ Nat.card (fixSub g) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨x.1.1, ?_⟩ : fixSub g)) ?_
    · have hx := x.2 ⟨g, Subgroup.mem_zpowers g⟩
      have := congrArg Subtype.val hx
      exact this
    · intro x y hxy
      have h2 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h2)
  rw [hcard] at h
  unfold Nat.ModEq at h
  omega

theorem not_seven_dvd_card_mulAut [Finite Q] (hQ : Nat.card Q = 32)
    (hT : Nat.card {x : Q // x * x = 1} = 12) : ¬ 7 ∣ Nat.card (MulAut Q) := by
  intro h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h
  have hg1 : g ≠ 1 := by
    rintro rfl
    simp at hg
  have hQ5 : Nat.card Q = 2 ^ 5 := by rw [hQ]; norm_num
  obtain ⟨j, hj, hcard, hmod⟩ := card_fixSub_cases hQ5 hg1 (r := 7) (k := 1) (by simpa using hg)
  have h5 := five_le_card_fixSub hT hg
  rw [hcard] at h5
  unfold Nat.ModEq at hmod
  interval_cases j <;> omega

theorem card_fixSub_eq_two [Finite Q] (hQ : Nat.card Q = 32) {g : MulAut Q} (hg1 : g ≠ 1)
    (hg : ∃ k : ℕ, orderOf g = 5 ^ k) : Nat.card (fixSub g) = 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := hg
  have hQ5 : Nat.card Q = 2 ^ 5 := by rw [hQ]; norm_num
  obtain ⟨j, hj, hcard, hmod⟩ := card_fixSub_cases hQ5 hg1 hk
  rw [hcard]
  unfold Nat.ModEq at hmod
  interval_cases j <;> omega

theorem not_exists_subgroup_card_twentyFive [Finite Q] (hQ : Nat.card Q = 32) :
    ¬ ∃ E : Subgroup (MulAut Q), Nat.card E = 25 := by
  rintro ⟨E, hE⟩
  classical
  have hfix : ∀ g : E, g ≠ 1 → Nat.card (fixedBy Q g) = 2 := by
    intro g hg1
    have hg1' : (g : MulAut Q) ≠ 1 := fun h => hg1 (Subtype.ext h)
    have hdvd : orderOf (g : MulAut Q) ∣ 5 ^ 2 := by
      rw [Subgroup.orderOf_coe]
      have := orderOf_dvd_natCard g
      rw [hE] at this
      simpa using this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hdvd
    have h2 := card_fixSub_eq_two hQ hg1' ⟨k, hk⟩
    rw [← h2]
    exact congrArg (fun s : Set Q => Nat.card s) rfl
  let : Fintype E := Fintype.ofFinite E
  let : Fintype Q := Fintype.ofFinite Q
  have : ∀ g : E, Fintype (fixedBy Q g) := fun g => Fintype.ofFinite _
  let : Fintype (orbitRel.Quotient E Q) := Fintype.ofFinite _
  have hB := sum_card_fixedBy_eq_card_orbits_mul_card_group E Q
  have hE' : Fintype.card E = 25 := by rw [Fintype.card_eq_nat_card]; exact hE
  have hone : Fintype.card (fixedBy Q (1 : E)) = 32 := by
    rw [Fintype.card_eq_nat_card]
    have : fixedBy Q (1 : E) = Set.univ := fixedBy_one_eq_univ (M := E) (α := Q)
    rw [this, Nat.card_univ]
    exact hQ
  have hsum : ∑ g : E, Fintype.card (fixedBy Q g) = 32 + 24 * 2 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : E))]
    have h1 : ∀ g ∈ Finset.univ.erase (1 : E), Fintype.card (fixedBy Q g) = 2 := by
      intro g hg
      rw [Fintype.card_eq_nat_card]
      exact hfix g (Finset.ne_of_mem_erase hg)
    rw [Finset.sum_congr rfl h1, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hE', hone]
    simp
  rw [hsum, hE'] at hB
  omega

end CFSG.Quasithin.AutQ8D8
