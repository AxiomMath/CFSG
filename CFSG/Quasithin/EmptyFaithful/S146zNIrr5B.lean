module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.A6Irr5

theorem card_modEq_card_fixedBy {G α : Type*} [Group G] [MulAction G α] [Finite α] {y : G}
    (hy : orderOf y = 5) :
    Nat.card α ≡ Nat.card (MulAction.fixedBy α y) [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hY : IsPGroup 5 (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hy, pow_one]
  have h := hY.card_modEq_card_fixedPoints α
  have hfix : MulAction.fixedPoints (Subgroup.zpowers y) α = MulAction.fixedBy α y := by
    ext x
    constructor
    · intro hx
      exact hx ⟨y, Subgroup.mem_zpowers y⟩
    · intro hx g
      have hle : Subgroup.zpowers y ≤ MulAction.stabilizer G x :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hx)
      exact MulAction.mem_stabilizer_iff.mp (hle g.2)
  rw [hfix] at h
  exact h

variable {V : Type*} [CommGroup V]

theorem exists_fixed_pair [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 32)
    {y : MulAut V} (hy : orderOf y = 5) :
    ∃ v : V, v ≠ 1 ∧ y v = v ∧ ∀ x : V, y x = x → x = 1 ∨ x = v := by
  let C : Subgroup V :=
    { carrier := {x | y x = x}
      one_mem' := map_one y
      mul_mem' := fun {a b} (ha : y a = a) (hb : y b = b) =>
        show y (a * b) = a * b by rw [map_mul, ha, hb]
      inv_mem' := fun {a} (ha : y a = a) => show y a⁻¹ = a⁻¹ by rw [map_inv, ha] }
  have hmod : Nat.card V ≡ Nat.card C [MOD 5] := card_modEq_card_fixedBy (α := V) hy
  have hC2 : Nat.card C = 2 ^ rk C := card_eq_two_pow hV C
  have hdvd : Nat.card C ∣ 32 := hcard ▸ Subgroup.card_subgroup_dvd_card C
  have hle : Nat.card C ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
  have hmod' : Nat.card C % 5 = 2 := by
    have h : Nat.card V % 5 = Nat.card C % 5 := hmod
    omega
  obtain ⟨k, hk⟩ : ∃ k, Nat.card C = 2 ^ k := ⟨_, hC2⟩
  have hk5 : k ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn : Nat.card C = 2 ∨ Nat.card C = 32 := by
    interval_cases k <;> omega
  have hC2' : Nat.card C = 2 := by
    rcases hn with h | h
    · exact h
    · exfalso
      have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [h, hcard])
      have hy1 : y = 1 := by
        ext x
        have hx : x ∈ C := by rw [htop]; trivial
        exact hx
      rw [hy1, orderOf_one] at hy
      omega
  obtain ⟨z, hz1, hz2⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hC2'
  refine ⟨z.1, ?_, z.2, ?_⟩
  · intro h
    exact hz1 (Subtype.ext h)
  · intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have : (⟨x, hx⟩ : C) = z := hz2 _ (fun h => hx1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this

end CFSG.Quasithin.A6Irr5
