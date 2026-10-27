module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

theorem eq_one_of_card_le_sixteen {W : Type*} [Group W] [Finite W] (hW : IsPGroup 2 W)
    (hW16 : Nat.card W ≤ 16) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    {g : MulAut W} {k : ℕ} (hg : g ^ p ^ k = 1) {w₀ : W} (hw₀ : w₀ ≠ 1) (hgw : g w₀ = w₀) :
    g = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set P := Subgroup.zpowers g with hPdef
  have hP : IsPGroup p P := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hg)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  let F : Subgroup W :=
    { carrier := {w | g w = w}
      mul_mem' := fun {a b} ha hb => by
        show g (a * b) = a * b
        rw [map_mul, show g a = a from ha, show g b = b from hb]
      one_mem' := map_one g
      inv_mem' := fun {a} ha => by
        show g a⁻¹ = a⁻¹
        rw [map_inv, show g a = a from ha] }
  have hfix : MulAction.fixedPoints P W = (F : Set W) := by
    ext w
    constructor
    · intro hw
      exact hw ⟨g, Subgroup.mem_zpowers g⟩
    · intro hw
      rintro ⟨h, hh⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hw' : g w = w := hw
      show (g ^ m) w = w
      have key : ∀ n : ℕ, (g ^ n) w = w := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hw', ih]
      rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast]
        exact key n
      · rw [zpow_neg, zpow_natCast]
        calc (g ^ n)⁻¹ w = (g ^ n)⁻¹ ((g ^ n) w) := by rw [key n]
          _ = w := MulAut.inv_apply_self _ _ _
  have hmod := hP.card_modEq_card_fixedPoints W
  rw [hfix] at hmod
  have hcF : Nat.card (F : Set W) = Nat.card F := rfl
  rw [hcF] at hmod
  obtain ⟨w, hw⟩ := (IsPGroup.iff_card (p := 2)).mp hW
  have hdvd : Nat.card F ∣ 2 ^ w := hw ▸ Subgroup.card_subgroup_dvd_card F
  obtain ⟨f, hfw, hf⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hw4 : w ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hf1 : 1 ≤ f := by
    by_contra h
    have hF : F = ⊥ := Subgroup.eq_bot_of_card_eq F (by rw [hf]; simp [show f = 0 by omega])
    have : w₀ ∈ F := hgw
    rw [hF, Subgroup.mem_bot] at this
    exact hw₀ this
  have hFW : f = w := by
    by_contra hne
    have hlt : f < w := lt_of_le_of_ne hfw hne
    rw [hw, hf] at hmod
    have h1 : p ∣ 2 ^ w - 2 ^ f := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num)
      hfw)).mp hmod.symm
    have h2 : 2 ^ w - 2 ^ f = 2 ^ f * (2 ^ (w - f) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hfw]
    rw [h2] at h1
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h3 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3))
    · have hd : w - f = 1 ∨ w - f = 2 ∨ w - f = 3 := by omega
      rcases hd with hd | hd | hd
      · rw [hd] at h3
        norm_num at h3
        exact absurd h3 hp.one_lt.ne'
      · rw [hd] at h3
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using h3))
      · rw [hd] at h3
        exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (by simpa using h3))
  have hF : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hf, hFW, hw])
  exact MulEquiv.ext fun x => by
    have hx : x ∈ F := by rw [hF]; trivial
    exact hx

theorem eq_one_of_fixed_commutator {M : Type*} [CommGroup M] {g : MulAut M} {m : ℕ}
    (hm : Odd m) (hgm : g ^ m = 1) {u t : M} (hu : g u = u * t) (ht : g t = t)
    (ht2 : t * t = 1) : t = 1 := by
  have key : ∀ n : ℕ, (g ^ n) u = u * t ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, hu, map_pow, ht, pow_succ', mul_assoc]
  have h1 := key m
  rw [hgm, MulAut.one_apply] at h1
  have h2 : t ^ m = 1 := by
    have := congrArg (fun x => u⁻¹ * x) h1
    simpa using this.symm
  obtain ⟨k, hk⟩ := hm
  rw [hk, pow_succ, pow_mul, show t ^ 2 = 1 from by rw [pow_two]; exact ht2, one_pow,
    one_mul] at h2
  exact h2

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
