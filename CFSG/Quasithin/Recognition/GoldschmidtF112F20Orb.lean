module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin

namespace F112B3

variable {G : Type*} [Group G]

theorem card_modEq_card_inf_centralizer [Finite G] {S : Subgroup G} {x : G} (hx : x ^ 5 = 1)
    (hS : x ∈ Subgroup.normalizer (S : Set G)) :
    Nat.card S ≡ Nat.card ↥(S ⊓ Subgroup.centralizer {x}) [MOD 5] := by
  have hP : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G) := Subgroup.zpowers_le.mpr hS
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hPg : IsPGroup 5 ↥(Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card]
    rcases (Nat.dvd_prime h5.out).mp (orderOf_dvd_of_pow_eq_one hx) with h | h
    · exact ⟨0, by rw [Nat.card_zpowers, h]; rfl⟩
    · exact ⟨1, by rw [Nat.card_zpowers, h]; rfl⟩
  let _ : MulAction ↥(Subgroup.zpowers x) ↥S :=
    { smul := fun y s => ⟨(y : G) * s * (y : G)⁻¹,
        ((Subgroup.mem_normalizer_iff.mp (hP y.2)) s).mp s.2⟩
      one_smul := fun s => Subtype.ext (by
        show ((1 : ↥(Subgroup.zpowers x)) : G) * s.1 * ((1 : ↥(Subgroup.zpowers x)) : G)⁻¹ = s.1
        simp)
      mul_smul := fun a b s => Subtype.ext (by
        show ((a * b : ↥(Subgroup.zpowers x)) : G) * s.1 * ((a * b : ↥(Subgroup.zpowers x)) : G)⁻¹ =
          (a : G) * ((b : G) * s.1 * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hmod := hPg.card_modEq_card_fixedPoints ↥S
  have hfix : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥S) =
      Nat.card ↥(S ⊓ Subgroup.centralizer {x}) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨(s.1 : G), s.1.2, Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]
          have := congrArg Subtype.val (s.2 ⟨x, Subgroup.mem_zpowers x⟩)
          have h2 : x * (s.1 : G) * x⁻¹ = s.1 := this
          rw [mul_inv_eq_iff_eq_mul] at h2
          exact h2⟩
        invFun := fun s => ⟨⟨s.1, s.2.1⟩, fun y => Subtype.ext (by
          show (y : G) * s.1 * (y : G)⁻¹ = s.1
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
          have hc : (s.1 : G) * x = x * s.1 :=
            (Subgroup.mem_centralizer_iff.mp s.2.2 x (Set.mem_singleton x)).symm
          rw [← hn, mul_inv_eq_iff_eq_mul]
          exact (Commute.zpow_left hc.symm n).eq)⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
  rw [hfix] at hmod
  exact hmod

theorem four_dvd_sub_of_pow_modEq {c n : ℕ} (hc : c ≤ n) (h : 2 ^ n ≡ 2 ^ c [MOD 5]) :
    4 ∣ n - c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  have h1 : 2 ^ d ≡ 1 [MOD 5] := by
    have h2 : 2 ^ c * 2 ^ d ≡ 2 ^ c * 1 [MOD 5] := by
      rw [← pow_add, mul_one]; exact h
    exact Nat.ModEq.cancel_left_of_coprime (by
      rw [show Nat.gcd 5 (2 ^ c) = 1 from
        (Nat.Coprime.pow_right c (by decide : Nat.Coprime 5 2))]) h2
  rw [Nat.add_sub_cancel_left]
  have hd : 2 ^ d % 5 = 2 ^ (d % 4) % 5 := by
    conv_lhs => rw [← Nat.div_add_mod d 4, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : 2 ^ d % 5 = 1 := h1
  have h4 : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h5 : d % 4 = 0 := by
    rw [hd] at h3
    interval_cases (d % 4) <;> simp_all
  omega

theorem sixteen_mul_card_le [Finite G] {S : Subgroup G} (hS2 : IsPGroup 2 S) {x : G}
    (hx : x ^ 5 = 1) (hxS : x ∈ Subgroup.normalizer (S : Set G))
    (hne : ¬ S ≤ Subgroup.centralizer {x}) :
    16 * Nat.card ↥(S ⊓ Subgroup.centralizer {x}) ≤ Nat.card S := by
  have hmod := card_modEq_card_inf_centralizer hx hxS
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hS2
  obtain ⟨c, hc⟩ :=
    (IsPGroup.iff_card (p := 2)).mp (hS2.to_inf_left (K := Subgroup.centralizer {x}))
  have hcle : Nat.card ↥(S ⊓ Subgroup.centralizer {x}) ∣ Nat.card S :=
    Subgroup.card_dvd_of_le inf_le_left
  have hcn : c ≤ n := by
    rw [hn, hc] at hcle
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hcle
  have hlt : c < n := by
    rcases hcn.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hne
      have heq : S ⊓ Subgroup.centralizer {x} = S := by
        refine Subgroup.eq_of_le_of_card_ge (inf_le_left) ?_
        rw [hn, hc, h]
      exact heq ▸ inf_le_right
  rw [hn, hc] at hmod ⊢
  have h4 := four_dvd_sub_of_pow_modEq hcn hmod
  obtain ⟨m, hm⟩ := h4
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm; omega
    · exact h0
  have : n = c + 4 * m := by omega
  rw [this, pow_add]
  have h16 : 16 ≤ 2 ^ (4 * m) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 16 * 2 ^ c = 2 ^ c * 16 := by ring
    _ ≤ 2 ^ c * 2 ^ (4 * m) := Nat.mul_le_mul_left _ h16

end F112B3

end CFSG.Quasithin
