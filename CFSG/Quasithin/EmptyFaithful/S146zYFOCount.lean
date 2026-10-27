module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

open MulAction

theorem card_dvd_of_free {G X : Type*} [Group G] [MulAction G X]
    (h : ∀ g : G, ∀ x : X, g • x = x → g = 1) : Nat.card G ∣ Nat.card X := by
  have hst : ∀ b : X, stabilizer G b = ⊥ := fun b => by
    ext g
    rw [mem_stabilizer_iff, Subgroup.mem_bot]
    exact ⟨h g b, fun hg => by rw [hg, one_smul]⟩
  rw [Nat.card_congr (selfEquivOrbitsQuotientProd hst), Nat.card_prod]
  exact Dvd.intro_left _ rfl

theorem exists_pow_order_five {P : Type*} [Group P] (hP : Nat.card P = 25) {p : P} (hp : p ≠ 1) :
    ∃ k : ℕ, (p ^ k) ^ 5 = 1 ∧ p ^ k ≠ 1 := by
  have hord : orderOf p ∣ 25 := hP ▸ orderOf_dvd_natCard p
  have h1 : orderOf p ≠ 1 := fun h => hp (orderOf_eq_one_iff.1 h)
  have h25 : orderOf p = 5 ∨ orderOf p = 25 := by
    have hle : orderOf p ≤ 25 := Nat.le_of_dvd (by norm_num) hord
    have hpos : 0 < orderOf p := Nat.pos_of_dvd_of_pos hord (by norm_num)
    interval_cases h : orderOf p <;> simp_all
  rcases h25 with h | h
  · exact ⟨1, by rw [pow_one, ← h]; exact pow_orderOf_eq_one p, by rwa [pow_one]⟩
  · refine ⟨5, ?_, ?_⟩
    · rw [← pow_mul, show 5 * 5 = orderOf p by rw [h]]
      exact pow_orderOf_eq_one p
    · intro h5
      have := orderOf_dvd_of_pow_eq_one h5
      rw [h] at this
      omega

@[expose, instance_reducible] def actOnCompl {G Ω : Type*} [Group G] [MulAction G Ω] (x : Ω)
    (hx : ∀ g : G, g • x = x) : MulAction G {y : Ω // y ≠ x} where
  smul g y := ⟨g • y.1, fun h => y.2 (MulAction.injective g (h.trans (hx g).symm))⟩
  one_smul y := Subtype.ext (one_smul G y.1)
  mul_smul a b y := Subtype.ext (mul_smul a b y.1)

theorem exists_common_fixed_point {Γ Ω : Type*} [Group Γ] [Finite Γ] [Finite Ω] [MulAction Γ Ω]
    (hΓ : Nat.card Γ = 400)
    (H1 : ∀ g : Γ, g ^ 5 = 1 → ∃ x : Ω, g • x = x)
    (H2 : ∀ g : Γ, g ^ 5 = 1 → ∀ x y : Ω, x ≠ y → g • x = x → g • y = y → g = 1) :
    ∃ x : Ω, (∀ γ : Γ, γ • x = x) ∧ Nat.card Ω % 25 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := Γ) 5 (n := 2)
    (by rw [hΓ]; norm_num)
  have hP25 : Nat.card P = 25 := by simpa using hP
  have hcomm : IsMulCommutative P :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (by simpa using hP25)
  have hnt : Nontrivial P := by
    have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP25]; norm_num)
    exact Finite.one_lt_card_iff_nontrivial.1 (by rw [hP25]; norm_num)
  obtain ⟨p0, hp0⟩ := exists_ne (1 : P)
  obtain ⟨k, hk5, hk1⟩ := exists_pow_order_five hP25 hp0
  set g0 : P := p0 ^ k with hg0def
  have hg05 : ((g0 : Γ)) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow]
    exact congrArg Subtype.val hk5
  have hg01 : (g0 : Γ) ≠ 1 := fun h => hk1 (Subtype.ext h)
  obtain ⟨x, hx⟩ := H1 (g0 : Γ) hg05
  have huniq : ∀ y : Ω, (g0 : Γ) • y = y → y = x := by
    intro y hy
    by_contra hne
    exact hg01 (H2 (g0 : Γ) hg05 y x hne hy hx)
  have hPx : ∀ p : P, (p : Γ) • x = x := by
    intro p
    apply huniq
    have hc : (g0 : Γ) * (p : Γ) = (p : Γ) * (g0 : Γ) := by
      have := hcomm.is_comm.comm g0 p
      exact congrArg Subtype.val this
    rw [← mul_smul, hc, mul_smul, hx]
  have hfree : ∀ y : Ω, y ≠ x → ∀ p : P, (p : Γ) • y = y → p = 1 := by
    intro y hyx p hpy
    by_contra hp1
    obtain ⟨k', hk'5, hk'1⟩ := exists_pow_order_five hP25 hp1
    have hq5 : (((p ^ k' : P) : Γ)) ^ 5 = 1 := by
      rw [← Subgroup.coe_pow]
      exact congrArg Subtype.val hk'5
    have hqy : ((p ^ k' : P) : Γ) • y = y := by
      have : ((p : Γ)) ^ k' ∈ stabilizer Γ y := Subgroup.pow_mem _ (mem_stabilizer_iff.2 hpy) k'
      rw [Subgroup.coe_pow]
      exact mem_stabilizer_iff.1 this
    have hqx := hPx (p ^ k')
    exact hk'1 (Subtype.ext (H2 _ hq5 y x hyx hqy hqx))
  refine ⟨x, ?_, ?_⟩
  ·
    intro γ
    by_contra hγ
    have hyx : γ • x ≠ x := hγ
    have hmem : ∀ p : P, (p : Γ) • (γ • x) ∈ orbit Γ x := fun p =>
      mem_orbit_iff.2 ⟨(p : Γ) * γ, by rw [mul_smul]⟩
    let f : P → orbit Γ x := fun p => ⟨(p : Γ) • (γ • x), hmem p⟩
    have hinj : Function.Injective f := by
      intro p p' hpp
      have h1 : (p : Γ) • (γ • x) = (p' : Γ) • (γ • x) := congrArg Subtype.val hpp
      have h2 : ((p'⁻¹ * p : P) : Γ) • (γ • x) = γ • x := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h1, ← mul_smul, inv_mul_cancel,
          one_smul]
      exact (inv_mul_eq_one.1 (hfree _ hyx _ h2)).symm
    have hle : Nat.card P ≤ Nat.card (orbit Γ x) := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_coe_set_eq, hP25] at hle
    have hPS : P ≤ stabilizer Γ x := fun p hp => mem_stabilizer_iff.2 (hPx ⟨p, hp⟩)
    have hdvd : 25 ∣ Nat.card (stabilizer Γ x) := hP25 ▸ Subgroup.card_dvd_of_le hPS
    have hmul := Subgroup.card_mul_index (stabilizer Γ x)
    rw [index_stabilizer, hΓ] at hmul
    have hpos : 0 < Nat.card (stabilizer Γ x) := Nat.card_pos
    have h25 : 25 ≤ Nat.card (stabilizer Γ x) := Nat.le_of_dvd hpos hdvd
    have : 25 * 25 ≤ Nat.card (stabilizer Γ x) * (orbit Γ x).ncard := Nat.mul_le_mul h25 hle
    omega
  ·
    let _ : MulAction P {y : Ω // y ≠ x} := actOnCompl x hPx
    have hdvd : Nat.card P ∣ Nat.card {y : Ω // y ≠ x} := by
      refine card_dvd_of_free fun p y hpy => ?_
      exact hfree y.1 y.2 p (congrArg Subtype.val hpy)
    rw [hP25] at hdvd
    have hcard : Nat.card {y : Ω // y ≠ x} + 1 = Nat.card Ω := by
      classical
      have := Fintype.ofFinite Ω
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl (fun y => y = x), Fintype.card_subtype_eq]
      have : 0 < Fintype.card Ω := Fintype.card_pos_iff.2 ⟨x⟩
      omega
    omega

theorem not_card_four_hundred {L Ω : Type*} [Group L] [Finite L] [Finite Ω] [MulAction L Ω]
    [IsPretransitive L Ω] (hL : Nat.card L = 126000) (hΩ : 1 < Nat.card Ω)
    (H1 : ∀ g : L, g ^ 5 = 1 → ∃ x : Ω, g • x = x)
    (H2 : ∀ g : L, g ^ 5 = 1 → ∀ x y : Ω, x ≠ y → g • x = x → g • y = y → g = 1)
    (H : Subgroup L) : Nat.card H ≠ 400 := by
  intro hH
  obtain ⟨x, hfix, hmod⟩ := exists_common_fixed_point (Γ := H) (Ω := Ω) hH
    (fun g hg => H1 (g : L) (by rw [← Subgroup.coe_pow, hg, Subgroup.coe_one]))
    (fun g hg x y hxy hx hy => Subtype.ext
      (H2 (g : L) (by rw [← Subgroup.coe_pow, hg, Subgroup.coe_one]) x y hxy hx hy))
  have hHS : H ≤ stabilizer L x := fun h hh => mem_stabilizer_iff.2 (hfix ⟨h, hh⟩)
  have hdvd : 400 ∣ Nat.card (stabilizer L x) := hH ▸ Subgroup.card_dvd_of_le hHS
  have hmul := Subgroup.card_mul_index (stabilizer L x)
  rw [index_stabilizer, orbit_eq_univ, Set.ncard_univ, hL] at hmul
  obtain ⟨t, ht⟩ := hdvd
  rw [ht] at hmul
  have h315 : Nat.card Ω ∣ 315 :=
    ⟨t, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 400) (by
      rw [show 400 * 315 = 126000 by norm_num, ← hmul]
      ring)⟩
  have hdiv : Nat.card Ω ∈ Nat.divisors 315 := by simp [h315]
  have key : ∀ d ∈ Nat.divisors 315, d % 25 = 1 → d = 1 := by decide
  have := key _ hdiv hmod
  omega

end FiveOdd

end CFSG.Quasithin.S146zY
