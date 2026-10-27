module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S143UA

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

theorem isPGroup_closure_dihedral {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 4 = 1) : IsPGroup 2 (Subgroup.closure {a, b}) := by
  set u : G := a * b with hu
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hau : a * u * a = u⁻¹ := by
    rw [hu, mul_inv_rev, hai, hbi]
    calc a * (a * b) * a = (a * a) * (b * a) := by group
      _ = b * a := by rw [ha, one_mul]
  have hconj : ∀ n : ℤ, a * u ^ n * a = u ^ (-n) := fun n => by
    have h1 : (a * u * a⁻¹) ^ n = a * u ^ n * a⁻¹ := conj_zpow
    rw [hai, hau, inv_zpow'] at h1
    exact h1.symm
  have hcomm : ∀ n : ℤ, a * u ^ n = u ^ (-n) * a := fun n => by
    calc a * u ^ n = a * u ^ n * (a * a) := by rw [ha, mul_one]
      _ = (a * u ^ n * a) * a := by group
      _ = u ^ (-n) * a := by rw [hconj n]
  have hu4 : u ^ 4 = 1 := hab
  let T : Subgroup G :=
    { carrier := {x | ∃ n : ℤ, x = u ^ n ∨ x = u ^ n * a}
      mul_mem' := by
        rintro x y ⟨m, rfl | rfl⟩ ⟨n, rfl | rfl⟩
        · exact ⟨m + n, Or.inl (zpow_add u m n).symm⟩
        · exact ⟨m + n, Or.inr (by rw [zpow_add, mul_assoc])⟩
        · refine ⟨m + -n, Or.inr ?_⟩
          rw [zpow_add, mul_assoc, hcomm n, ← mul_assoc]
        · refine ⟨m + -n, Or.inl ?_⟩
          rw [zpow_add, mul_assoc, ← mul_assoc a, hconj n]
      one_mem' := ⟨0, Or.inl (zpow_zero u).symm⟩
      inv_mem' := by
        rintro x ⟨n, rfl | rfl⟩
        · exact ⟨-n, Or.inl (zpow_neg u n).symm⟩
        · refine ⟨n, Or.inr ?_⟩
          rw [mul_inv_rev, hai, ← zpow_neg, hcomm (-n), neg_neg] }
  have hle : Subgroup.closure ({a, b} : Set G) ≤ T := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg_one, hu, mul_inv_rev, hai, hbi, mul_assoc, ha, mul_one]
  intro g
  obtain ⟨n, hn | hn⟩ := hle g.2
  · refine ⟨2, ?_⟩
    apply Subtype.ext
    show (g : G) ^ 2 ^ 2 = 1
    have h4 : u ^ ((2 ^ 2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; simpa using hu4
    rw [hn, ← zpow_natCast, ← zpow_mul, zpow_mul', h4, one_zpow]
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    show (g : G) ^ 2 ^ 1 = 1
    rw [hn, pow_one, pow_two]
    calc u ^ n * a * (u ^ n * a) = u ^ n * (a * u ^ n * a) := by group
      _ = 1 := by rw [hconj n, ← zpow_add]; simp

@[expose] def NoD8 (L : Type*) [Group L] : Prop :=
  ∀ a b : L, a * a = 1 → b * b = 1 → (a * b) ^ 4 = 1 → a * b = b * a

theorem NoD8.of_mulEquiv {L X : Type*} [Group L] [Group X] (e : L ≃* X) (h : NoD8 X) : NoD8 L := by
  intro a b ha hb hab
  apply e.injective
  rw [map_mul, map_mul]
  exact h (e a) (e b) (by rw [← map_mul, ha, map_one]) (by rw [← map_mul, hb, map_one])
    (by rw [← map_mul, ← map_pow, hab, map_one])

theorem noD8_of_sylow_involutions_central {G : Type*} [Group G] [Finite G]
    (h : ∀ S : Sylow 2 G, ∀ x : (S : Subgroup G), x ≠ 1 → x * x = 1 →
      x ∈ Subgroup.center (S : Subgroup G)) : NoD8 G := by
  intro a b ha hb hab
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  by_cases hb1 : b = 1
  · rw [hb1, one_mul, mul_one]
  obtain ⟨S, hS⟩ := (isPGroup_closure_dihedral ha hb hab).exists_le_sylow
  have haS : a ∈ (S : Subgroup G) := hS (Subgroup.subset_closure (by simp))
  have hbS : b ∈ (S : Subgroup G) := hS (Subgroup.subset_closure (by simp))
  have hc := Subgroup.mem_center_iff.mp
    (h S ⟨a, haS⟩ (fun e => ha1 (congrArg Subtype.val e)) (Subtype.ext ha)) ⟨b, hbS⟩
  exact (congrArg Subtype.val hc).symm

theorem center_eq_bot_of_simple {L : Type*} [Group L] [Finite L] (hs : IsSimpleGroup L)
    (hnp : ¬ (Nat.card L).Prime) : Subgroup.center L = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : L, x * y = y * x := fun x y =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x
    let _ : CommGroup L := { (inferInstance : Group L) with mul_comm := hcomm }
    exact hnp (IsSimpleGroup.prime_card (α := L))

theorem center_eq_bot_of_mulEquiv {L X : Type*} [Group L] [Group X] (e : L ≃* X)
    (h : Subgroup.center X = ⊥) : Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx y]
  rw [h, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  exact e.injective (hx'.trans e.map_one.symm)

end InspW2

end S143

end CFSG.Quasithin
