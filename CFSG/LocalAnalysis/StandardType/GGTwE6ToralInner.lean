module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcTwE6
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

namespace TwE6Toral

open TableB.TwE6

section Param

variable {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ}

theorem pow_three_mem_torus₀ (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    {b : Fin 6 → Kˣ} (hb : b ∈ compat σ) : b ^ 3 ∈ torus₀ σ := by
  obtain ⟨x, hx⟩ := exists_mul_edge_inv_mem hq hK hσ hb
  have h3 : b ^ 3 = (b * (edge σ x)⁻¹) ^ 3 * edge σ (x ^ 3) := by
    rw [map_pow, mul_pow, inv_pow, inv_mul_cancel_right]
  rw [h3]
  exact mul_mem (pow_mem hx 3) (edge_pow_three_mem (sigma_sigma hK hσ) x)

theorem pow_sq_card_eq (hK : Nat.card K = q ^ 2) (x : K) : x ^ (q ^ 2) = x := by
  have : Fintype K := Fintype.ofFinite K
  rw [← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem edge_mem_torus₀_of_fixed (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    {c : Kˣ} (hc : σ (c : K) = c) : edge σ c ∈ torus₀ σ := by
  have hσσ := sigma_sigma hK hσ
  have hμ : ((((c ^ 3)⁻¹ : Kˣ) : K)) ^ q = (((c ^ 3)⁻¹ : Kˣ) : K) := by
    rw [← hσ]
    simp [hc]
  obtain ⟨y, hy⟩ := TableB.exists_norm_eq hq hK (Units.ne_zero _) hμ
  have hyσ : (y : K) * σ y = (c : K)⁻¹ ^ 3 := by
    rw [hσ, ← pow_succ', hy]
    simp
  have h1 : edge σ (y ^ 3 * c ^ 4) ∈ torus₀ σ := by
    refine ⟨![y ^ 2 * c ^ 2, c⁻¹, y, c⁻¹ ^ 2, Units.map σ.toMonoidHom y,
      Units.map σ.toMonoidHom (y ^ 2 * c ^ 2)], fun i => ?_, ?_⟩
    · fin_cases i <;> (apply Units.ext; simp [rhoE6_values, hσσ, hc])
    · rw [cartanHom_eq, edge_apply]
      funext l
      have hc0 : (c : K) ≠ 0 := Units.ne_zero c
      have hy0 : (y : K) ≠ 0 := Units.ne_zero y
      have hσy : σ (y : K) = (c : K)⁻¹ ^ 3 / y :=
        (eq_div_iff hy0).mpr (by rw [mul_comm]; exact hyσ)
      fin_cases l
      · apply Units.ext
        simp
        field_simp
      · apply Units.ext
        simp
      · apply Units.ext
        simp
      · apply Units.ext
        simp [hσy]
        field_simp
      · apply Units.ext
        simp [hc]
        field_simp
      · apply Units.ext
        simp [hc]
        field_simp
  have h2 : edge σ ((y * c) ^ 3) ∈ torus₀ σ := edge_pow_three_mem hσσ (y * c)
  have e : c = y ^ 3 * c ^ 4 * ((y * c) ^ 3)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_pow, mul_left_comm, ← pow_succ']
  rw [e, map_mul, map_inv]
  exact mul_mem h1 (inv_mem h2)

theorem edge_mem_torus₀_of_not_dvd (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) (h3 : ¬ 3 ∣ q + 1) (x : Kˣ) : edge σ x ∈ torus₀ σ := by
  obtain ⟨k, m, hkm⟩ : ∃ k m : ℕ, k * (q + 1) = 3 * m + 1 := by
    rcases (by omega : (q + 1) % 3 = 1 ∨ (q + 1) % 3 = 2) with h | h
    · exact ⟨1, (q + 1) / 3, by omega⟩
    · exact ⟨2, 2 * (q + 1) / 3, by omega⟩
  have hfix : σ (((x ^ (q + 1)) ^ k : Kˣ) : K) = (((x ^ (q + 1)) ^ k : Kˣ) : K) := by
    have h1 : σ ((x : K) ^ (q + 1)) = (x : K) ^ (q + 1) := by
      rw [hσ, ← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, pow_sq_card_eq hK,
        ← pow_succ']
    simp only [Units.val_pow_eq_pow_val, map_pow, h1]
  have h1 := edge_mem_torus₀_of_fixed hq hK hσ hfix
  have h2 : edge σ ((x ^ m) ^ 3) ∈ torus₀ σ := edge_pow_three_mem (sigma_sigma hK hσ) (x ^ m)
  have e : x = (x ^ (q + 1)) ^ k * ((x ^ m) ^ 3)⁻¹ := by
    rw [← pow_mul, ← pow_mul, mul_comm (q + 1) k, hkm, pow_succ, mul_comm m 3]
    group
  rw [e, map_mul, map_inv]
  exact mul_mem h1 (inv_mem h2)

theorem mem_torus₀_of_not_dvd (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (h3 : ¬ 3 ∣ q + 1) {b : Fin 6 → Kˣ} (hb : b ∈ compat σ) : b ∈ torus₀ σ := by
  obtain ⟨x, hx⟩ := exists_mul_edge_inv_mem hq hK hσ hb
  have h := mul_mem hx (edge_mem_torus₀_of_not_dvd hq hK hσ h3 x)
  rwa [inv_mul_cancel_right] at h

theorem card_galoisField_two_mul (f : ℕ) (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
  rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]

theorem two_le_two_pow {f : ℕ} (hf : 1 ≤ f) : 2 ≤ 2 ^ f := by
  have := Nat.one_lt_two_pow (n := f) (by omega)
  omega

end Param

section Aut

variable {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ}

theorem compatParamAut_pow_three_mem (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) (b : ↥(compat σ)) :
    RootCentExc.compatParamAut σ b ^ 3 ∈
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range := by
  rw [← map_pow]
  exact RootCentExc.compatParamAut_mem_range_of_mem_torus σ (pow_three_mem_torus₀ hq hK hσ b.2)

theorem compatParamAut_mem_of_not_dvd (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) (h3 : ¬ 3 ∣ q + 1) (b : ↥(compat σ)) :
    RootCentExc.compatParamAut σ b ∈
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range :=
  RootCentExc.compatParamAut_mem_range_of_mem_torus σ (mem_torus₀_of_not_dvd hq hK hσ h3 b.2)

theorem mem_range_conj_of_mem_twInndiag (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) {p : ℕ} (hp : p.Prime) (h : p ≠ 3 ∨ ¬ 3 ∣ q + 1)
    {α : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)}
    (hα : α ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range ⊔
      (RootCentExc.compatParamAut σ).range)
    (hαp : α ^ p = 1) :
    α ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range := by
  set I := (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
    MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range with hI
  have : I.Normal := RootCentExc.normal_range_mulAutConj
  have hαm : QuotientGroup.mk' I α ∈ (RootCentExc.compatParamAut σ).range.map
      (QuotientGroup.mk' I) := by
    have h1 : QuotientGroup.mk' I α ∈ (I ⊔ (RootCentExc.compatParamAut σ).range).map
        (QuotientGroup.mk' I) := ⟨α, hα, rfl⟩
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hαm
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' I α = 1
  rcases h with hp3 | h3
  · have h3 : QuotientGroup.mk' I α ^ 3 = 1 := by
      rw [← hb, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact compatParamAut_pow_three_mem hq hK hσ b
    have hpα : QuotientGroup.mk' I α ^ p = 1 := by rw [← map_pow, hαp, map_one]
    have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)
    have hd : orderOf (QuotientGroup.mk' I α) ∣ Nat.gcd 3 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hpα)
    rw [Nat.Coprime.gcd_eq_one hcop] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  · rw [← hb, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact compatParamAut_mem_of_not_dvd hq hK hσ h3 b

end Aut

end TwE6Toral

section Inputs

theorem ggTwE6InndiagOrdPInnerInput_holds : GGTwE6InndiagOrdPInnerInput := by
  intro f p hf hp _ h3 α hα hαp
  refine TwE6Toral.mem_range_conj_of_mem_twInndiag (TwE6Toral.two_le_two_pow hf)
    (TwE6Toral.card_galoisField_two_mul f hf) (frobQ_apply 2 f) hp ?_ hα hαp
  by_cases hp3 : p = 3
  · exact Or.inr fun h => h3 ⟨hp3, h⟩
  · exact Or.inl hp3

theorem ggTwE6CenterTrivialInput_holds : GGTwE6CenterTrivialInput := by
  intro f hf h3
  obtain ⟨hcard, -⟩ := CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
    (k := GaloisField 2 (2 * f)) (θ := frobQ 2 f) (q := 2 ^ f)
    (TwE6Toral.card_galoisField_two_mul f hf) (frobQ_apply 2 f)
  rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)] at hcard
  exact Subgroup.card_eq_one.mp hcard

end Inputs

end CFSG.StandardType
