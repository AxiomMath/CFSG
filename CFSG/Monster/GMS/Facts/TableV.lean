module

public import CFSG.Monster.GMS.Facts.Basic

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

@[expose] def tableVOrderB : ℕ := 2 ^ 38 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19

@[expose] def tableVOrderZ : ℕ := 2 ^ 42 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23

@[expose] def tableVOrderU : ℕ := 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7

@[expose] def twoBabyOrder : ℕ :=
  2 ^ 42 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47

@[expose] def TableV (a b z u : G) : Prop :=
  b ∈ Subgroup.centralizer ({a} : Set G) ∧ z ∈ Subgroup.centralizer ({a} : Set G) ∧
    u ∈ Subgroup.centralizer ({a} : Set G) ∧
    orderOf b = 2 ∧ orderOf z = 2 ∧ orderOf u = 2 ∧ b ≠ a ∧ z ≠ a ∧ u ≠ a ∧
    (∀ t ∈ Subgroup.centralizer ({a} : Set G), orderOf t = 2 → t ≠ a →
      ∃ g ∈ Subgroup.centralizer ({a} : Set G),
        g * t * g⁻¹ = b ∨ g * t * g⁻¹ = z ∨ g * t * g⁻¹ = a * z ∨ g * t * g⁻¹ = u) ∧
    Nat.card (Subgroup.centralizer ({a} : Set G)) = twoBabyOrder ∧
    Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {b}) = tableVOrderB ∧
    Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {z}) = tableVOrderZ ∧
    Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {u}) = tableVOrderU ∧
    ∀ T : Subgroup G, T ≤ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {z} →
      Nat.card T = 2 ^ 42 → ∀ x : G,
        (x ∈ T ∧ ∀ s ∈ T, x * s = s * x) ↔ (x = 1 ∨ x = a ∨ x = z ∨ x = a * z)

@[expose] def TableVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a : G), IsTwoBabyCentralizer a → ∃ b z u : G, TableV a b z u

@[expose] def TableVIn (G : Type*) [Group G] : Prop :=
  ∀ a : G, IsTwoBabyCentralizer a → ∃ b z u : G, TableV a b z u

theorem TableVStatement.inG (h : TableVStatement) {G : Type} [Group G] [Finite G] :
    TableVIn G :=
  fun a ha => h G a ha

theorem centralizer_inf_mul_eq (a z : G) :
    Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {a * z} =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {z} := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hga, hgaz⟩
    refine ⟨hga, ?_⟩
    have : g * (a * z) = a * g * z := by rw [← mul_assoc, hga]
    rw [this, mul_assoc, mul_assoc a z g] at hgaz
    exact mul_left_cancel hgaz
  · rintro ⟨hga, hgz⟩
    refine ⟨hga, ?_⟩
    rw [← mul_assoc, hga, mul_assoc, hgz, mul_assoc]

theorem TableV.swap {a b z u : G} (ha : orderOf a = 2) (h : TableV a b z u) :
    TableV a b (a * z) u := by
  obtain ⟨hb, hz, hu, hb2, hz2, hu2, hba, hza, hua, hcov, hcard, hcb, hcz, hcu, hcen⟩ := h
  have haa : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have hcomm : z * a = a * z := (Subgroup.mem_centralizer_singleton_iff.mp hz)
  have haaz : a * (a * z) = z := by rw [← mul_assoc, haa, one_mul]
  have hinf := centralizer_inf_mul_eq a z
  refine ⟨hb, Subgroup.mul_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hz, hu, hb2,
    ?_, hu2, hba, ?_, hua, ?_, hcard, hcb, by rw [hinf]; exact hcz, hcu, ?_⟩
  ·
    have hsq : (a * z) * (a * z) = 1 := by
      calc (a * z) * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [hcomm]
        _ = 1 := by rw [← mul_assoc, haa, one_mul, hzz]
    refine orderOf_eq_prime (by rw [sq]; exact hsq) ?_
    intro h1
    have : z = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [inv_eq_of_mul_eq_one_right haa] at this
    exact hza this
  · intro h1
    have : z = 1 := by
      have := congrArg (a⁻¹ * ·) h1
      simpa using this
    rw [this, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · intro t ht ht2 hta
    obtain ⟨g, hg, hgt⟩ := hcov t ht ht2 hta
    refine ⟨g, hg, ?_⟩
    rcases hgt with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl (by rw [haaz]; exact h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · intro T hT hcardT x
    rw [hinf] at hT
    rw [hcen T hT hcardT x, haaz]
    tauto

end CFSG.Monster.GMS
