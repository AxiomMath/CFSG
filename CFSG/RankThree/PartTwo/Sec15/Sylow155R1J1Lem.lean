module

public import CFSG.Walter.Cited.HuppertPlane

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

private theorem res1J1_eq_of_modEq {n c p : ℕ} (hn : n ∣ 8) (hc : c ∣ n) (hp : p.Prime)
    (hp42 : Nat.Coprime p 42) (h : n ≡ c [MOD p]) : c = n := by
  have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn (by norm_num)
  have hn8 : n ≤ 8 := Nat.le_of_dvd (by norm_num) hn
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos hc hn0
  have hcn : c ≤ n := Nat.le_of_dvd hn0 hc
  by_contra hne
  have hdvd : p ∣ n - c := (Nat.modEq_iff_dvd' hcn).1 h.symm
  have hpos : 0 < n - c := by omega
  have hp7 : p ≤ 7 := (Nat.le_of_dvd hpos hdvd).trans (by omega)
  have hp2 := hp.two_le
  interval_cases n <;> interval_cases c <;> (try omega) <;> interval_cases p <;>
    first
      | omega
      | exact absurd hp42 (by decide)
      | exact absurd hp (by norm_num)

theorem res1J1_mulAut_eq_one_of_pow_prime {R : Type*} [Group R] (hR : Nat.card R ∣ 8) {p : ℕ}
    (hp : p.Prime) (hp42 : Nat.Coprime p 42) {σ : MulAut R} (hσ : σ ^ p = 1) : σ = 1 := by
  haveI : Finite R := Nat.finite_of_card_ne_zero fun h => by rw [h] at hR; norm_num at hR
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod := CFSG.Walter.Huppert.card_fixedSubgroup_modEq (p := p) (σ := σ) (k := 1)
    (by rw [pow_one]; exact hσ)
  have heq := res1J1_eq_of_modEq hR
    (Subgroup.card_subgroup_dvd_card (CFSG.Walter.Huppert.fixedSubgroup σ)) hp hp42 hmod
  have htop := Subgroup.eq_top_of_card_eq _ heq
  ext r
  exact CFSG.Walter.Huppert.mem_fixedSubgroup.mp (htop ▸ Subgroup.mem_top r)

theorem res1J1_mulAut_eq_one_of_pow_coprime {R : Type*} [Group R] (hR : Nat.card R ∣ 8) :
    ∀ (n : ℕ) (σ : MulAut R), σ ^ n = 1 → Nat.Coprime n 42 → σ = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hσ hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n
      · exact absurd hn (by decide)
      · simpa using hσ
    · obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      have hp2 := hp.two_le
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hmn : m < n := by nlinarith
      have hpc : Nat.Coprime p 42 := Nat.Coprime.coprime_dvd_left ⟨m, hm⟩ hn
      have hmc : Nat.Coprime m 42 :=
        Nat.Coprime.coprime_dvd_left ⟨p, by rw [hm, mul_comm]⟩ hn
      have hτ : (σ ^ p) ^ m = 1 := by rw [← pow_mul, ← hm]; exact hσ
      exact res1J1_mulAut_eq_one_of_pow_prime hR hp hpc (ih m hmn (σ ^ p) hτ hmc)

theorem res1J1_centralizes_of_pow_eq_one {G : Type*} [Group G] {V : Subgroup G}
    (hV : Nat.card V ∣ 8) {a : G} (ha : ∀ v ∈ V, a * v * a⁻¹ ∈ V) {n : ℕ} (hn : a ^ n = 1)
    (hcop : Nat.Coprime n 42) : ∀ v ∈ V, a * v = v * a := by
  have hpow : ∀ k : ℕ, ∀ v ∈ V, a ^ k * v * (a ^ k)⁻¹ ∈ V := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
      intro v hv
      have h := ha _ (ih v hv)
      have e : a * (a ^ k * v * (a ^ k)⁻¹) * a⁻¹ = a ^ (k + 1) * v * (a ^ (k + 1))⁻¹ := by
        rw [pow_succ']
        group
      rwa [e] at h
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact absurd hcop (by decide))
  have hnorm : a ∈ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨ha h, fun hh => ?_⟩
    have hinv : a ^ (n - 1) = a⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hn1]
      exact hn
    have h1 := hpow (n - 1) _ hh
    rw [hinv] at h1
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rwa [e] at h1
  have hpowN : (⟨a, hnorm⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ n = 1 :=
    Subtype.ext (by simpa using hn)
  have hσ : (V.normalizerMonoidHom ⟨a, hnorm⟩) ^ n = 1 := by
    rw [← map_pow, hpowN, map_one]
  have h1 := res1J1_mulAut_eq_one_of_pow_coprime hV n _ hσ hcop
  intro v hv
  have h2 : (V.normalizerMonoidHom ⟨a, hnorm⟩) ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [h1]; rfl
  have h3 : a * v * a⁻¹ = v := by
    have := congrArg Subtype.val h2
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
  exact mul_inv_eq_iff_eq_mul.1 h3

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
