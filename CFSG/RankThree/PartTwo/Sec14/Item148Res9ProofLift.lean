module

public import Mathlib.GroupTheory.Sylow
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res9

open scoped Pointwise

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_of_conj_mem [Finite Γ] {H : Subgroup Γ} {g : Γ}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let φ : H → H := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hφ : Function.Injective φ := by
    intro y z hyz
    have h1 : g * (y : Γ) * g⁻¹ = g * z * g⁻¹ := congrArg Subtype.val hyz
    exact Subtype.ext (by simpa using h1)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨_, hx⟩
  have h1 : g * (y : Γ) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hy
  have h2 : (y : Γ) = x := by simpa using h1
  exact h2 ▸ y.2

theorem exists_pow_mod_three_eq_one [Finite Γ] (g : Γ) :
    ∃ M s : ℕ, M % 3 = 1 ∧ (g ^ M) ^ (3 ^ s) = 1 := by
  set n := orderOf g with hn
  have hn0 : n ≠ 0 := (orderOf_pos g).ne'
  have hcop := Nat.coprime_ordCompl Nat.prime_three hn0
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self n 3
  set m := n / 3 ^ n.factorization 3 with hm
  refine ⟨m ^ 2, n.factorization 3, ?_, ?_⟩
  · have hm3 : m % 3 ≠ 0 := fun h0 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop (Nat.dvd_of_mod_eq_zero h0)
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases this with h | h <;> rw [h]
  · rw [← pow_mul, show m ^ 2 * 3 ^ n.factorization 3 = (3 ^ n.factorization 3 * m) * m by ring,
      hsplit, pow_mul, hn, pow_orderOf_eq_one, one_pow]

theorem exists_mem_sylow_of_isPGroup_quotient [Finite Γ] {U N : Subgroup Γ} (hNU : N ≤ U)
    (hUN : U ≤ Subgroup.normalizer (N : Set Γ)) {p : ℕ} [Fact p.Prime]
    (hUp : ∀ y ∈ U, ∃ k : ℕ, y ^ (p ^ k) ∈ N) (P0 : Sylow p U) {y : Γ} (hy : y ∈ U) :
    ∃ x ∈ (P0 : Subgroup U).map U.subtype, x⁻¹ * y ∈ N := by
  have : (N.subgroupOf U).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNU).mpr hUN
  set π := QuotientGroup.mk' (N.subgroupOf U) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set S := P0.mapSurjective hπs with hS
  have hQ : IsPGroup p (U ⧸ N.subgroupOf U) := by
    intro q
    obtain ⟨z, rfl⟩ := hπs q
    obtain ⟨k, hk⟩ := hUp z z.2
    refine ⟨k, ?_⟩
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hk
  have htop : (S : Subgroup (U ⧸ N.subgroupOf U)) = ⊤ :=
    (S.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  have hmem : π ⟨y, hy⟩ ∈ (S : Subgroup (U ⧸ N.subgroupOf U)) := htop ▸ Subgroup.mem_top _
  rw [hS, Sylow.coe_mapSurjective] at hmem
  obtain ⟨x, hx, hxy⟩ := hmem
  refine ⟨x, Subgroup.mem_map_of_mem _ hx, ?_⟩
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hxy
  simpa using hxy

theorem exists_commute_of_coprime [Finite Γ] {P N : Subgroup Γ} {p : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (hP : IsPGroup p P) (hPN : P ≤ Subgroup.normalizer (N : Set Γ)) {b : Γ}
    (hbP : b ∈ Subgroup.normalizer (P : Set Γ)) (hbN : b ∈ Subgroup.normalizer (N : Set Γ))
    {s : ℕ} (hbs : b ^ (3 ^ s) = 1) (hfix : ∀ x ∈ P, x⁻¹ * (b * x * b⁻¹) ∈ N) {x : Γ}
    (hx : x ∈ P) : ∃ c ∈ P, b * c = c * b ∧ c⁻¹ * x ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup 3 (Subgroup.zpowers b) := by
    have hdvd : Nat.card (Subgroup.zpowers b) ∣ 3 ^ s := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hbs
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card hk
  have hbP' : Subgroup.zpowers b ≤ Subgroup.normalizer (P : Set Γ) :=
    Subgroup.zpowers_le.mpr hbP
  have hbN' : Subgroup.zpowers b ≤ Subgroup.normalizer (N : Set Γ) :=
    Subgroup.zpowers_le.mpr hbN
  set α : Subgroup.zpowers b →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hbP')
    with hα
  have hαapp : ∀ (z : Subgroup.zpowers b) (y : P), ((α z y : P) : Γ) = z * y * z⁻¹ :=
    fun _ _ => rfl
  have : (N.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPN
  have hN : ∀ z : Subgroup.zpowers b, ∀ n ∈ N.subgroupOf P, α z n ∈ N.subgroupOf P := by
    intro z n hn
    rw [Subgroup.mem_subgroupOf, hαapp]
    exact (Subgroup.mem_normalizer_iff.mp (hbN' z.2) n).mp hn
  have hcop : ¬ 3 ∣ Nat.card (N.subgroupOf P) := by
    have hNp : IsPGroup p (N.subgroupOf P) := (hP.to_subgroup (N.subgroupOf P))
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    rw [hk]
    intro h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)).symm
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA α (N.subgroupOf P)
    hN hcop
  have hpow : ∀ n : ℕ, ∀ y ∈ P, y⁻¹ * (b ^ n * y * (b ^ n)⁻¹) ∈ N := by
    intro n
    induction n with
    | zero => intro y _; simp
    | succ n ih =>
      intro y hy
      have hy' : b * y * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hbP y).mp hy
      have h1 := ih _ hy'
      have h2 := hfix y hy
      have h3 : y⁻¹ * (b ^ (n + 1) * y * (b ^ (n + 1))⁻¹) =
          (y⁻¹ * (b * y * b⁻¹)) * ((b * y * b⁻¹)⁻¹ * (b ^ n * (b * y * b⁻¹) * (b ^ n)⁻¹)) := by
        rw [pow_succ]
        group
      rw [h3]
      exact N.mul_mem h2 h1
  have hq : (QuotientGroup.mk' (N.subgroupOf P) ⟨x, hx⟩ : P ⧸ N.subgroupOf P) ∈
      {q | ∀ z : Subgroup.zpowers b,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (N.subgroupOf P) hN z q =
          q} := by
    intro z
    rw [QuotientGroup.mk'_apply, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).mpr z.2
    have hz : (z : Γ) = b ^ n := hn.symm
    have h1 := hpow n x hx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hαapp, hz]
    have h2 : (b ^ n * x * (b ^ n)⁻¹)⁻¹ * x = ((x⁻¹ * (b ^ n * x * (b ^ n)⁻¹)))⁻¹ := by group
    rw [h2]
    exact N.inv_mem h1
  rw [hlift] at hq
  obtain ⟨c, hc, hcx⟩ := hq
  refine ⟨c, c.2, ?_, ?_⟩
  · have h1 : b * (c : Γ) * b⁻¹ = c := by
      have := congrArg Subtype.val (hc ⟨b, Subgroup.mem_zpowers b⟩)
      rw [hαapp] at this
      simpa using this
    calc b * c = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [h1]
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hcx
    simpa using hcx

theorem exists_centralizing_lift [Finite Γ] {U N : Subgroup Γ} (hNU : N ≤ U)
    (hUN : U ≤ Subgroup.normalizer (N : Set Γ)) {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hUp : ∀ y ∈ U, ∃ k : ℕ, y ^ (p ^ k) ∈ N) {a : Γ}
    (haU : a ∈ Subgroup.normalizer (U : Set Γ)) (haN : a ∈ Subgroup.normalizer (N : Set Γ))
    (ha3 : a ^ 3 = 1) (hfix : ∀ y ∈ U, a * y * a⁻¹ * y⁻¹ ∈ N) :
    ∃ b : Γ, a⁻¹ * b ∈ U ∧ (∃ s : ℕ, b ^ (3 ^ s) = 1) ∧ ∃ P : Subgroup Γ, P ≤ U ∧
      IsPGroup p P ∧ ∀ y ∈ U, ∃ c ∈ P, b * c = c * b ∧ c⁻¹ * y ∈ N := by
  obtain ⟨P0⟩ := (inferInstance : Nonempty (Sylow p U))
  set P : Subgroup Γ := (P0 : Subgroup U).map U.subtype with hP
  have hPU : P ≤ U := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hPp : IsPGroup p P := P0.isPGroup'.map U.subtype
  have hcos : ∀ {y : Γ}, y ∈ U → ∃ x ∈ P, x⁻¹ * y ∈ N := fun hy =>
    exists_mem_sylow_of_isPGroup_quotient hNU hUN hUp P0 hy
  set cU := U.normalizerMonoidHom ⟨a, haU⟩ with hcU
  have hcUapp : ∀ y : U, ((cU y : U) : Γ) = a * y * a⁻¹ := fun _ => rfl
  set P1 := P0.mapSurjective (f := (cU : U →* U)) cU.surjective with hP1
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq U P1 P0
  have hwmem : ∀ x ∈ (P0 : Subgroup U), w * cU x * w⁻¹ ∈ (P0 : Subgroup U) := by
    intro x hx
    have h1 : cU x ∈ (P1 : Subgroup U) := by
      rw [hP1, Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem _ hx
    have h2 : MulAut.conj w • cU x ∈ MulAut.conj w • (P1 : Subgroup U) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [← Sylow.coe_subgroup_smul, hw] at h2
    exact h2
  set g : Γ := (w : Γ) * a with hg
  have hgP : g ∈ Subgroup.normalizer (P : Set Γ) := by
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨_, hwmem x hx, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hcUapp, hg]
    group
  obtain ⟨x₀, hx₀P, hx₀⟩ := hcos (U.inv_mem w.2)
  set g' : Γ := g * x₀ with hg'
  have hwU : (w : Γ) ∈ U := w.2
  have hx₀U : x₀ ∈ U := hPU hx₀P
  have haU' : ∀ y ∈ U, a * y * a⁻¹ ∈ U := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp haU y).mp hy
  have haN' : ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp haN n).mp hn
  have hUN' : ∀ u ∈ U, ∀ n ∈ N, u * n * u⁻¹ ∈ N := fun u hu n hn =>
    (Subgroup.mem_normalizer_iff.mp (hUN hu) n).mp hn
  have hg'N : g' ∈ Subgroup.normalizer (N : Set Γ) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hUN hwU) haN) (hUN hx₀U)
  have hg'U : g' ∈ Subgroup.normalizer (U : Set Γ) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hwU) haU)
      (Subgroup.le_normalizer hx₀U)
  have hg'P : g' ∈ Subgroup.normalizer (P : Set Γ) :=
    Subgroup.mul_mem _ hgP (Subgroup.le_normalizer hx₀P)
  have hg'fix : ∀ y ∈ U, g' * y * g'⁻¹ * y⁻¹ ∈ N := by
    intro y hy
    set m : Γ := (w : Γ) * x₀ with hm
    have hmN : m ∈ N := by
      have := N.inv_mem hx₀
      simpa [hm] using this
    set y₁ : Γ := m * y * m⁻¹ with hy₁
    set y₂ : Γ := (w : Γ)⁻¹ * y₁ * w with hy₂
    have hy₁U : y₁ ∈ U := U.mul_mem (U.mul_mem (hNU hmN) hy) (U.inv_mem (hNU hmN))
    have hy₂U : y₂ ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hwU) hy₁U) hwU
    have hn' := hfix y₂ hy₂U
    have h1 : g' * y * g'⁻¹ * y⁻¹ =
        ((w : Γ) * (a * y₂ * a⁻¹ * y₂⁻¹) * (w : Γ)⁻¹) * (m * (y * m⁻¹ * y⁻¹)) := by
      simp only [hg', hg, hy₂, hy₁, hm]
      group
    rw [h1]
    refine N.mul_mem (hUN' _ hwU _ hn') (N.mul_mem hmN ?_)
    have := hUN' y hy _ (N.inv_mem hmN)
    simpa using this
  obtain ⟨M, s, hM, hbs⟩ := exists_pow_mod_three_eq_one g'
  refine ⟨g' ^ M, ?_, ⟨s, hbs⟩, P, hPU, hPp, ?_⟩
  ·
    have hg'a : a⁻¹ * g' ∈ U := by
      have : a⁻¹ * g' = (a⁻¹ * (w : Γ) * a) * x₀ := by simp only [hg', hg]; group
      rw [this]
      refine U.mul_mem ?_ hx₀U
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haU) _).mp hwU
      simpa using this
    have hk : ∀ k : ℕ, (a ^ k)⁻¹ * g' ^ k ∈ U := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have : (a ^ (k + 1))⁻¹ * g' ^ (k + 1) =
            (a⁻¹ * ((a ^ k)⁻¹ * g' ^ k) * a) * (a⁻¹ * g') := by
          rw [pow_succ, pow_succ]
          group
        rw [this]
        refine U.mul_mem ?_ hg'a
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haU) _).mp ih
        simpa using this
    have haM : a ^ M = a := by
      rw [← Nat.div_add_mod M 3, hM, pow_add, pow_mul, ha3, one_pow, one_mul, pow_one]
    have := hk M
    rwa [haM] at this
  ·
    have hbP : g' ^ M ∈ Subgroup.normalizer (P : Set Γ) := Subgroup.pow_mem _ hg'P M
    have hbN : g' ^ M ∈ Subgroup.normalizer (N : Set Γ) := Subgroup.pow_mem _ hg'N M
    have hpowfix : ∀ k : ℕ, ∀ y ∈ U, y⁻¹ * (g' ^ k * y * (g' ^ k)⁻¹) ∈ N := by
      intro k
      induction k with
      | zero => intro y _; simp
      | succ k ih =>
        intro y hy
        have hy' : g' * y * g'⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hg'U y).mp hy
        have h1 := ih _ hy'
        have h2 : y⁻¹ * (g' * y * g'⁻¹) ∈ N := by
          have := hg'fix y hy
          have h3 : y⁻¹ * (g' * y * g'⁻¹) = y⁻¹ * (g' * y * g'⁻¹ * y⁻¹) * y := by group
          rw [h3]
          have := hUN' _ (U.inv_mem hy) _ this
          simpa using this
        have h3 : y⁻¹ * (g' ^ (k + 1) * y * (g' ^ (k + 1))⁻¹) =
            (y⁻¹ * (g' * y * g'⁻¹)) *
              ((g' * y * g'⁻¹)⁻¹ * (g' ^ k * (g' * y * g'⁻¹) * (g' ^ k)⁻¹)) := by
          rw [pow_succ]
          group
        rw [h3]
        exact N.mul_mem h2 h1
    intro y hy
    obtain ⟨x, hxP, hxy⟩ := hcos hy
    obtain ⟨c, hcP, hcb, hcx⟩ := exists_commute_of_coprime hp3 hPp (hPU.trans hUN) hbP hbN hbs
      (fun x hx => hpowfix M x (hPU hx)) hxP
    refine ⟨c, hcP, hcb, ?_⟩
    have : c⁻¹ * y = (c⁻¹ * x) * (x⁻¹ * y) := by group
    rw [this]
    exact N.mul_mem hcx hxy

end CFSG.RankThree.PartTwo.Sec14.Item148Res9
