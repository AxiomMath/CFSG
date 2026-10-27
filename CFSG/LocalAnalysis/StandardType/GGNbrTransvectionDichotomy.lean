module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.StandardType

theorem mulAut_eq_one_or_transvection {V : Type*} [Group V] [Finite V] {p : ℕ} (hp : p.Prime)
    (hVc : ∀ a b : V, a * b = b * a) (hVp : ∀ v : V, v ^ p = 1) (N : Subgroup V)
    (hN : Nat.card N ≤ p) (κ : MulAut V) (hκ : ∀ v : V, v⁻¹ * κ v ∈ N)
    (hfix : ∀ n ∈ N, κ n = n) :
    κ = 1 ∨ (Nat.card {v : V // κ v = v} * p = Nat.card V ∧
      ∀ v : V, κ (v⁻¹ * κ v) = v⁻¹ * κ v) := by
  classical
  let f : V →* V :=
    { toFun := fun v => v⁻¹ * κ v
      map_one' := by simp
      map_mul' := by
        intro v w
        letI : CommGroup V := { ‹Group V› with mul_comm := hVc }
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hfval : ∀ v : V, f v = v⁻¹ * κ v := fun v => rfl
  have hmem : ∀ v : V, v ∈ f.ker ↔ κ v = v := by
    intro v
    rw [MonoidHom.mem_ker, hfval v, inv_mul_eq_one]
    exact eq_comm
  have hcardfix : Nat.card {v : V // κ v = v} = Nat.card f.ker := by
    apply Nat.card_congr
    exact
      { toFun := fun v => ⟨v.1, (hmem v.1).mpr v.2⟩
        invFun := fun v => ⟨v.1, (hmem v.1).mp v.2⟩
        left_inv := fun v => Subtype.ext rfl
        right_inv := fun v => Subtype.ext rfl }
  have hcardV : Nat.card V = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  by_cases htriv : f.range = ⊥
  ·
    left
    ext v
    have hmemrange : f v ∈ f.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rw [htriv] at hmemrange
    have hfv : f v = 1 := by simpa using hmemrange
    have hv : κ v = v := (hmem v).mp (MonoidHom.mem_ker.mpr hfv)
    simpa using hv
  ·
    right
    have hrange_le_N : f.range ≤ N := by
      intro x hx
      obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hx
      simpa [hfval v] using hκ v
    have hcard_range_le_p : Nat.card f.range ≤ p :=
      (Subgroup.card_le_of_le hrange_le_N).trans hN
    obtain ⟨a, ha, hane⟩ := (Subgroup.bot_or_exists_ne_one f.range).resolve_left htriv
    obtain ⟨v0, hv0⟩ := MonoidHom.mem_range.mp ha
    have hap : a ^ p = 1 := by
      rw [← hv0, ← map_pow, hVp v0, map_one]
    have hdivp : orderOf a ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hap
    have hne1 : orderOf a ≠ 1 := fun h => hane (orderOf_eq_one_iff.mp h)
    have horder : orderOf a = p := by
      rcases (Nat.dvd_prime hp).mp hdivp with h | h
      · exact absurd h hne1
      · exact h
    have hdvd : p ∣ Nat.card f.range := by
      rw [← horder]
      exact Subgroup.orderOf_dvd_natCard f.range ha
    have hcard_pos : 0 < Nat.card f.range := by
      haveI : Nonempty ↥f.range := ⟨⟨a, ha⟩⟩
      exact Finite.card_pos
    have hcard_range : Nat.card f.range = p :=
      le_antisymm hcard_range_le_p (Nat.le_of_dvd hcard_pos hdvd)
    have hmain : Nat.card {v : V // κ v = v} * p = Nat.card V := by
      rw [hcardfix, hcardV, hcard_range, Nat.mul_comm]
    exact ⟨hmain, fun v => hfix _ (hκ v)⟩

end CFSG.StandardType

end
