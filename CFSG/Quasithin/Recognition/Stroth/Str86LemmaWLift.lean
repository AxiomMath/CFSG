module

public import Mathlib.GroupTheory.PGroup

import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.Stroth

theorem exists_lift_pow_primePow_eq_one {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f) (hK : IsPGroup 2 f.ker) {p a : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {h : H} (hh : h ^ p ^ a = 1) : ∃ g : G, f g = h ∧ g ^ p ^ a = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₁, hg₁⟩ := hf h
  obtain ⟨i, n', hn', horder⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g₁).ne' p hp.ne_one
  have hcop : Nat.Coprime n' (orderOf h) :=
    (Nat.Prime.coprime_pow_of_not_dvd hp hn').of_dvd_right (orderOf_dvd_of_pow_eq_one hh)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hfg : f (g₁ ^ (n' * m)) = h := by
    calc
      f (g₁ ^ (n' * m)) = (f g₁) ^ (n' * m) := by rw [map_pow]
      _ = (h ^ n') ^ m := by rw [hg₁, pow_mul]
      _ = h := hm
  have hgpow : (g₁ ^ (n' * m)) ^ (p ^ i) = 1 := by
    rw [← pow_mul, show n' * m * p ^ i = p ^ i * n' * m by ring, pow_mul, ← horder,
      pow_orderOf_eq_one, one_pow]
  have hmem : (g₁ ^ (n' * m)) ^ (p ^ a) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hfg, hh]
  have hP : IsPGroup p (Subgroup.zpowers ((g₁ ^ (n' * m)) ^ (p ^ a))) := by
    apply IsPGroup.of_card_dvd_pow (n := i)
    rw [Nat.card_zpowers]
    exact (orderOf_pow_dvd (p ^ a)).trans (orderOf_dvd_of_pow_eq_one hgpow)
  have hdisj : Disjoint f.ker (Subgroup.zpowers ((g₁ ^ (n' * m)) ^ (p ^ a))) :=
    IsPGroup.disjoint_of_ne 2 p hp2.symm f.ker _ hK hP
  exact ⟨g₁ ^ (n' * m), hfg, Subgroup.disjoint_def.mp hdisj hmem (Subgroup.mem_zpowers _)⟩

private theorem exists_preimage_commute {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f) (hK : IsPGroup 2 f.ker) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {w : G} (hPw : IsPGroup p (Subgroup.zpowers w)) {y : H}
    (hyw : Commute y (f w)) : ∃ c : G, f c = y ∧ Commute c w := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg₀⟩ := hf y
  have hKcard : ¬ p ∣ Nat.card f.ker := by
    obtain ⟨k, hk⟩ := hK.exists_card_eq
    rw [hk]
    intro hdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdiv))
  have hcommP : ∀ b : Subgroup.zpowers w, Commute y (f (b : G)) := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hk, map_zpow]
    exact hyw.zpow_right k
  have hinv : ∀ b : Subgroup.zpowers w, ∀ x : G, x * g₀⁻¹ ∈ f.ker →
      ((MulAut.conj (b : G)) x) * g₀⁻¹ ∈ f.ker := by
    intro b x hx
    have h1 : (b : G) * (x * g₀⁻¹) * (b : G)⁻¹ ∈ f.ker :=
      (inferInstance : f.ker.Normal).conj_mem _ hx _
    have h2 : (b : G) * g₀ * (b : G)⁻¹ * g₀⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hg₀]
      rw [(hcommP b).eq.symm]
      group
    have h3 : (b : G) * (x * g₀⁻¹) * (b : G)⁻¹ * ((b : G) * g₀ * (b : G)⁻¹ * g₀⁻¹) =
        (b : G) * x * (b : G)⁻¹ * g₀⁻¹ := by group
    rw [MulAut.conj_apply, ← h3]
    exact f.ker.mul_mem h1 h2
  obtain ⟨c, hcK, hcfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed p hPw
      (MulAut.conj.comp (Subgroup.zpowers w).subtype) f.ker hKcard g₀).1 hinv
  have hfc : f c = y := by
    have hker : f (c * g₀⁻¹) = 1 := MonoidHom.mem_ker.mp hcK
    rw [map_mul, map_inv, hg₀] at hker
    exact mul_inv_eq_one.mp hker
  refine ⟨c, hfc, ?_⟩
  have h := hcfix ⟨w, Subgroup.mem_zpowers w⟩
  change w * c * w⁻¹ = c at h
  change c * w = w * c
  calc
    c * w = (w * c * w⁻¹) * w := by rw [h]
    _ = w * c := by group

private theorem exists_odd_pow_of_commute {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) {w c : G} {y : H} (hfc : f c = y) (hy : Odd (orderOf y))
    (hcw : Commute c w) : ∃ x : G, f x = y ∧ Odd (orderOf x) ∧ Commute x w := by
  obtain ⟨b, n', hoddn', horder⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcop2 : Nat.Coprime (orderOf y) (2 ^ b) := by
    have h2 : Nat.Coprime (orderOf y) 2 := Nat.coprime_two_right.mpr hy
    cases b with
    | zero => simpa using Nat.coprime_one_right (orderOf y)
    | succ b =>
        rw [Nat.coprime_pow_right_iff (Nat.succ_pos b)]
        exact h2
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime (x := y) (n := 2 ^ b) hcop2.symm
  have hxpow : (c ^ (2 ^ b * t)) ^ n' = 1 := by
    rw [← pow_mul, show 2 ^ b * t * n' = (2 ^ b * n') * t by ring, pow_mul, ← horder,
      pow_orderOf_eq_one, one_pow]
  refine ⟨c ^ (2 ^ b * t), ?_, hoddn'.of_dvd_nat (orderOf_dvd_of_pow_eq_one hxpow),
    hcw.pow_left (2 ^ b * t)⟩
  calc
    f (c ^ (2 ^ b * t)) = (f c) ^ (2 ^ b * t) := by rw [map_pow]
    _ = (y ^ 2 ^ b) ^ t := by rw [hfc, ← pow_mul]
    _ = y := ht

theorem exists_lift_odd_commute {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (hK : IsPGroup 2 f.ker) {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {w : G} (hw : w ^ p ^ a = 1) {y : H} (hy : Odd (orderOf y)) (hyw : Commute y (f w)) :
    ∃ x : G, f x = y ∧ Odd (orderOf x) ∧ Commute x w := by
  have hPw : IsPGroup p (Subgroup.zpowers w) := by
    apply IsPGroup.of_card_dvd_pow (n := a)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hw
  obtain ⟨c, hfc, hcw⟩ := exists_preimage_commute f hf hK hp hp2 hPw hyw
  exact exists_odd_pow_of_commute f hfc hy hcw

end CFSG.Quasithin.Stroth

end
