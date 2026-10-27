module

public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofU
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
import CFSG.RankThree.PartTwo.KFacts.K71SU3Torus
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3
import CFSG.RankThree.PartTwo.KFacts.AutPSUDet

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace KS165UProof

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedSU StatedScalars)
open Matrix

theorem not_nine_dvd_sq_sub_one {m : ℕ} (hm : m % 3 = 2) (hm9 : m % 9 ≠ 8) :
    ¬ 9 ∣ m ^ 2 - 1 := by
  have hr : m % 9 = 2 ∨ m % 9 = 5 := by omega
  have hs : m ^ 2 % 9 = 4 ∨ m ^ 2 % 9 = 7 := by
    rw [Nat.pow_mod]
    rcases hr with hr | hr <;> rw [hr] <;> norm_num
  have h1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  generalize m ^ 2 = s at hs h1
  omega

theorem pow_three_ne {K : Type} [Field K] [Finite K] (h9 : ¬ 9 ∣ Nat.card K - 1) {ε : K}
    (hε : ε ^ 3 = 1) (hε1 : ε ≠ 1) (μ : K) : μ ^ 3 ≠ ε := by
  intro hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [← hμ] at hε
    norm_num at hε
  set u : Kˣ := Units.mk0 μ hμ0 with hu
  have hu9 : u ^ 9 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
      show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hμ, hε]
  have hcardU : Nat.card Kˣ = Nat.card K - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hd1 : orderOf u ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hu9)
  have hd2 : orderOf u ∣ Nat.card K - 1 := hcardU ▸ orderOf_dvd_natCard u
  obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd1
  have hk2 : k ≠ 2 := by
    rintro rfl
    rw [hke] at hd2
    exact h9 (by simpa using hd2)
  have hu3 : u ^ 3 = 1 := by
    have : orderOf u ∣ 3 := by
      rw [hke]
      interval_cases k
      · simp
      · simp
      · exact absurd rfl hk2
    exact orderOf_dvd_iff_pow_eq_one.mp this
  apply hε1
  rw [← hμ]
  have := congrArg Units.val hu3
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this

section Lift

variable {n : ℕ} {K : Type} [Field K] (hK : PiField false 2 n K)

theorem not_nine_dvd_card (hK : PiField false 2 n K) (hq : 2 ^ n % 3 = 2)
    (hq9 : 2 ^ n % 9 ≠ 8) : ¬ 9 ∣ Nat.card K - 1 := by
  rw [hK.card]
  exact not_nine_dvd_sq_sub_one hq hq9

theorem mem_unitaryScalars_of_eq_smul {v : unitarySU 2 n K 3} {c : K}
    (hv : ((v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) :
    v ∈ unitaryScalars hK.unitary 3 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hdet := congrArg Matrix.det hv
    rw [zero_smul, det_zero] at hdet
    exact (Units.ne_zero (GeneralLinearGroup.det (v : GL (Fin 3) K))) (by
      rw [GeneralLinearGroup.val_det_apply]
      exact hdet)
  rw [unitaryScalars_eq hK.unitary (by norm_num), Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range]
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, hv, scalar_apply, ← smul_one_eq_diagonal]
  rfl

theorem pow_three_eq_one_of_mk (hq : 2 ^ n % 3 = 2) (hq9 : 2 ^ n % 9 ≠ 8)
    (v : unitarySU 2 n K 3) (hv : ((v : unitaryPSU hK.unitary 3)) ^ 3 = 1) : v ^ 3 = 1 := by
  have := hK.finite
  have hv3 : v ^ 3 ∈ unitaryScalars hK.unitary 3 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hv
  obtain ⟨c, -, hc3, hvc⟩ := hv3
  by_cases hc1 : c = 1
  · apply Subtype.ext
    rw [Subgroup.coe_one, hvc, hc1, map_one]
  exfalso
  have hc1' : (c : K) ≠ 1 := fun h => hc1 (Units.ext h)
  have hc3' : (c : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hcube := pow_three_ne (not_nine_dvd_card hK hq hq9) hc3' hc1'
  have hy : ((v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (c : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hvc, GeneralLinearGroup.coe_scalar,
      scalar_apply, smul_one_eq_diagonal]
  have hdet := Sec4.det_eq_of_cube hcube hy
  have hdet1 := ((mem_unitarySU_iff hK.unitary).mp v.2).1
  exact hc1' (hdet.symm.trans hdet1)

theorem not_smul_of_mk_ne_one {v : unitarySU 2 n K 3}
    (hv : ((v : unitaryPSU hK.unitary 3)) ≠ 1) :
    ∀ c : K, ((v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
  intro c hc
  apply hv
  rw [QuotientGroup.eq_one_iff]
  exact mem_unitaryScalars_of_eq_smul hK hc

theorem card_unitaryScalars_three (hq : 2 ^ n % 3 = 2) :
    Nat.card (unitaryScalars hK.unitary 3) = 3 := by
  rw [card_unitaryScalars hK.unitary (by norm_num)]
  have h3 : 3 ∣ 2 ^ n + 1 := by omega
  exact Nat.gcd_eq_left h3

theorem pow_three_of_mem_unitaryScalars {z : unitarySU 2 n K 3}
    (hz : z ∈ unitaryScalars hK.unitary 3) : z ^ 3 = 1 := by
  obtain ⟨c, -, hc3, hzc⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one, Subgroup.coe_one]

theorem eq_one_of_mem_unitaryScalars_of_pow {z : unitarySU 2 n K 3}
    (hz : z ∈ unitaryScalars hK.unitary 3) {N : ℕ} (hN : ¬ 3 ∣ N) (hzN : z ^ N = 1) :
    z = 1 := by
  have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (pow_three_of_mem_unitaryScalars hK hz)
  have h2 : orderOf z ∣ N := orderOf_dvd_of_pow_eq_one hzN
  have hcop : Nat.Coprime 3 N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem eq_bot_of_normalizes_psu (hq : 2 ^ n % 3 = 2) (hq9 : 2 ^ n % 9 ≠ 8)
    {x : unitaryPSU hK.unitary 3} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (R : Subgroup (unitaryPSU hK.unitary 3)) (hR : IsPGroup 2 R)
    (hRx : ∀ r ∈ R, x * r * x⁻¹ ∈ R) : R = ⊥ := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
  have := hK.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv3 := pow_three_eq_one_of_mk hK hq hq9 v hx3
  have hvs := not_smul_of_mk_ne_one hK hx1
  have hcard := card_unitaryScalars_three hK hq
  have hker : (unitaryProj hK.unitary 3).ker = unitaryScalars hK.unitary 3 :=
    ker_unitaryProj hK.unitary 3
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
    rw [hk]
    intro h3
    have := (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hcop : Nat.Coprime (Nat.card (unitaryProj hK.unitary 3).ker) (Nat.card R) := by
    rw [hker, hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR3
  obtain ⟨Y, hYR, hYdisj⟩ :=
    Sec6.BThreeCensus.exists_lift_of_coprime (unitaryProj_surjective hK.unitary 3) R hcop
  set N := Nat.card R with hN
  have hYN : ∀ y ∈ Y, y ^ N = 1 := by
    intro y hy
    have hyR : unitaryProj hK.unitary 3 y ∈ R := hYR ▸ Subgroup.mem_map_of_mem _ hy
    have h1 : unitaryProj hK.unitary 3 (y ^ N) = 1 := by
      rw [map_pow]
      have := pow_card_eq_one' (G := R) (x := ⟨_, hyR⟩)
      exact congrArg Subtype.val this
    have h2 : y ^ N ∈ Y ⊓ (unitaryProj hK.unitary 3).ker := ⟨pow_mem hy N, h1⟩
    rw [hYdisj.eq_bot] at h2
    exact h2
  have hYchar : ∀ g : unitarySU 2 n K 3, unitaryProj hK.unitary 3 g ∈ R → g ^ N = 1 → g ∈ Y := by
    intro g hgR hgN
    rw [← hYR] at hgR
    obtain ⟨y, hy, hyg⟩ := hgR
    set z := y⁻¹ * g with hz
    have hzker : z ∈ unitaryScalars hK.unitary 3 := by
      rw [← hker, MonoidHom.mem_ker, hz, map_mul, map_inv, hyg, inv_mul_cancel]
    have hzc : z ∈ Subgroup.center (unitarySU 2 n K 3) :=
      unitaryScalars_le_center hK.unitary 3 hzker
    have hgyz : g = y * z := by rw [hz, mul_inv_cancel_left]
    have hcomm : Commute y z := ((Subgroup.mem_center_iff.mp hzc) y)
    have hzN : z ^ N = 1 := by
      have : g ^ N = y ^ N * z ^ N := by rw [hgyz, hcomm.mul_pow]
      rw [hgN, hYN y hy, one_mul] at this
      exact this.symm
    have hz1 := eq_one_of_mem_unitaryScalars_of_pow hK hzker hR3 hzN
    rw [hgyz, hz1, mul_one]
    exact hy
  set X := Y.map (unitarySU 2 n K 3).subtype with hX
  have hXu : X ≤ glPi false 3 (2 ^ n) K := by
    rintro _ ⟨y, -, rfl⟩
    exact slPi_le_glPi (π := false) (fun _ => hK.unitary) y.2
  have hX2 : IsPGroup 2 X := by
    have hY2 : IsPGroup 2 Y := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
      intro y
      refine ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, ← hk, Subgroup.coe_one]
      exact hYN y y.2
    exact hY2.map _
  have hXv : ∀ g ∈ X, (v : GL (Fin 3) K) * g * (v : GL (Fin 3) K)⁻¹ ∈ X := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨v * y * v⁻¹, hYchar _ ?_ ?_, rfl⟩
    · have hyR : unitaryProj hK.unitary 3 y ∈ R := hYR ▸ Subgroup.mem_map_of_mem _ hy
      rw [map_mul, map_mul, map_inv]
      exact hRx _ hyR
    · rw [conj_pow, hYN y hy, mul_one, mul_inv_cancel]
  have hvmem : (v : GL (Fin 3) K) ∈ StatedSU 3 (2 ^ n) K := v.2
  have hv3' : (v : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hv3, Subgroup.coe_one]
  have hXbot := eq_bot_of_normalizes hK hq hvmem hv3' hvs hXu hX2 hXv
  have hYbot : Y = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : ((y : GL (Fin 3) K)) ∈ X := ⟨y, hy, rfl⟩
    rw [hXbot, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  rw [← hYR, hYbot, Subgroup.map_bot]

end Lift

section Commute

variable {n : ℕ} {K : Type} [Field K] (hK : PiField false 2 n K)

theorem cube_root_cases {ω y : K} (hω : ω ^ 2 + ω + 1 = 0) (hy : y ^ 3 = 1) :
    y = 1 ∨ y = ω ∨ y = ω ^ 2 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h : (y - 1) * (y - ω) * (y - ω ^ 2) = 0 := by
    linear_combination hy + (-y ^ 2 + y) * hω + (y - 1) * hω3
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem diag_facts {y g : GL (Fin 3) K} {x : Fin 3 → K} (hy3 : y ^ 3 = 1)
    (hdet : (y : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hx : ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal x) :
    (∀ i, x i ^ 3 = 1) ∧ x 0 * x 1 * x 2 = 1 := by
  have h3 : (g⁻¹ * y * g) ^ 3 = 1 := by
    have := conj_pow (a := g⁻¹) (b := y) (i := 3)
    rw [inv_inv] at this
    rw [this, hy3, mul_one, inv_mul_cancel]
  have hm : (diagonal x) ^ 3 = 1 := by
    rw [← hx, ← Units.val_pow_eq_pow_val, h3, Units.val_one]
  rw [diagonal_pow, ← diagonal_one] at hm
  refine ⟨fun i => by simpa using congrFun (diagonal_injective hm) i, ?_⟩
  have hd := congrArg Matrix.det hx
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, det_diagonal,
    Fin.prod_univ_three, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    det_one] at hd
  exact hd.symm

theorem not_commute_of_lift (hq : 2 ^ n % 3 = 2) {b₁ b₂ : unitarySU 2 n K 3}
    (h₁3 : b₁ ^ 3 = 1) (h₂3 : b₂ ^ 3 = 1) (h₁ : (b₁ : unitaryPSU hK.unitary 3) ≠ 1)
    (h₂ : (b₂ : unitaryPSU hK.unitary 3) ∉ Subgroup.zpowers (b₁ : unitaryPSU hK.unitary 3)) :
    b₁ * b₂ ≠ b₂ * b₁ := by
  intro hcomm
  have := hK.finite
  have : CharP K 2 := hK.charP
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hv3 : (b₁ : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, h₁3, Subgroup.coe_one]
  have hw3 : (b₂ : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, h₂3, Subgroup.coe_one]
  obtain ⟨g, d, e, -, hvg, hde, hd⟩ :=
    exists_unitary_diagonal hK hq b₁.2 hv3 (not_smul_of_mk_ne_one hK h₁)
  set δ₁ : GL (Fin 3) K := g⁻¹ * (b₁ : GL (Fin 3) K) * g with hδ₁
  set δ₂ : GL (Fin 3) K := g⁻¹ * (b₂ : GL (Fin 3) K) * g with hδ₂
  have hδ₁d : (δ₁ : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [hδ₁, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hvg, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hcommδ : δ₂ * δ₁ = δ₁ * δ₂ := by
    have hc : (b₂ : GL (Fin 3) K) * b₁ = b₁ * b₂ := by
      have := congrArg Subtype.val hcomm
      simpa using this.symm
    rw [hδ₁, hδ₂]
    calc g⁻¹ * ↑b₂ * g * (g⁻¹ * ↑b₁ * g) = g⁻¹ * (↑b₂ * ↑b₁) * g := by group
      _ = g⁻¹ * (↑b₁ * ↑b₂) * g := by rw [hc]
      _ = g⁻¹ * ↑b₁ * g * (g⁻¹ * ↑b₂ * g) := by group
  have hdinj : ∀ i j, i ≠ j → d i ≠ d j := by
    intro i j hij hdij
    have h1 := hd i j hij
    rw [← hdij, hde i, hdij, hde j] at h1
    have h2 : (1 : K) + 1 = 0 := by linear_combination h2K
    exact one_ne_zero (h1.symm.trans h2)
  set x : Fin 3 → K := fun i => (δ₂ : Matrix (Fin 3) (Fin 3) K) i i with hx
  have hδ₂x : (δ₂ : Matrix (Fin 3) (Fin 3) K) = diagonal x := by
    have hcm : (δ₂ : Matrix (Fin 3) (Fin 3) K) * diagonal d =
        diagonal d * (δ₂ : Matrix (Fin 3) (Fin 3) K) := by
      rw [← hδ₁d, ← Units.val_mul, ← Units.val_mul, hcommδ]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hx]
    · rw [offDiag_eq_zero_of_commute_diagonal hdinj hcm hij, diagonal_apply_ne _ hij]
  obtain ⟨hx3, hxp⟩ := diag_facts hw3 ((mem_unitarySU_iff hK.unitary).mp b₂.2).1 hδ₂x
  obtain ⟨hd3, hdp⟩ := diag_facts hv3 ((mem_unitarySU_iff hK.unitary).mp b₁.2).1 hδ₁d
  set ω := d 1 * e 0 with hω
  have hω' : ω ^ 2 + ω + 1 = 0 := by
    have h01 := hd 0 1 (by decide)
    linear_combination ω * h01 - (d 1 * e 1) * hde 0 - hde 1 + ω * h2K
  have hd1 : d 1 = ω * d 0 := by
    rw [hω]
    linear_combination (-(d 1)) * hde 0
  set ρ := d 2 * e 0 with hρdef
  have hρ : ρ ^ 2 + ρ + 1 = 0 := by
    have h02 := hd 0 2 (by decide)
    linear_combination ρ * h02 - (d 2 * e 2) * hde 0 - hde 2 + ρ * h2K
  have hd2ρ : d 2 = ρ * d 0 := by
    rw [hρdef]
    linear_combination (-(d 2)) * hde 0
  have hρω : ρ ≠ ω := by
    intro h
    apply hdinj 1 2 (by decide)
    rw [hd1, hd2ρ, h]
  have hρω2 : ρ = ω ^ 2 := by
    have h : (ρ - ω) * (ρ - ω ^ 2) = 0 := by
      linear_combination hρ + (-ρ + ω - 1) * hω'
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hρω
    · exact sub_eq_zero.mp h
  have hd2 : d 2 = ω ^ 2 * d 0 := by rw [hd2ρ, hρω2]
  have hd0 : d 0 ≠ 0 := by
    intro h0
    have := hd3 0
    rw [h0] at this
    norm_num at this
  have hx0 : x 0 ≠ 0 := by
    intro h0
    have := hx3 0
    rw [h0] at this
    norm_num at this
  set τ := x 1 * (x 0)⁻¹ with hτdef
  have hx1 : x 1 = τ * x 0 := by
    rw [hτdef, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτdef, mul_pow, inv_pow, hx3 1, hx3 0, inv_one, mul_one]
  have hx2 : x 2 = τ ^ 2 * x 0 := by
    have E : τ * x 0 ^ 2 * x 2 = 1 := by
      rw [← hxp, hx1]
      ring
    linear_combination (τ ^ 2 * x 0) * E - x 2 * x 0 ^ 3 * hτ3 - x 2 * hx3 0
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω'
  have hlam : ∃ (lam : K) (j : ℕ), ∀ i, x i = lam * d i ^ j := by
    rcases cube_root_cases hω' hτ3 with hτ | hτ | hτ
    · refine ⟨x 0, 0, fun i => ?_⟩
      fin_cases i
      · simp
      · simp [hx1, hτ]
      · simp [hx2, hτ]
    · refine ⟨x 0 * (d 0)⁻¹, 1, fun i => ?_⟩
      fin_cases i
      · simp [hd0]
      · simp only [Fin.mk_one, pow_one]
        rw [hx1, hτ, hd1]
        field_simp
      · simp only [Fin.reduceFinMk, pow_one]
        rw [hx2, hτ, hd2]
        field_simp
    · refine ⟨x 0 * (d 0 ^ 2)⁻¹, 2, fun i => ?_⟩
      fin_cases i
      · simp [hd0]
      · simp only [Fin.mk_one]
        rw [hx1, hτ, hd1]
        field_simp
      · simp only [Fin.reduceFinMk]
        rw [hx2, hτ, hd2]
        field_simp
  obtain ⟨lam, j, hxl⟩ := hlam
  have hδ : (δ₂ : Matrix (Fin 3) (Fin 3) K) = lam • ((δ₁ ^ j : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) := by
    rw [hδ₂x, Units.val_pow_eq_pow_val, hδ₁d, diagonal_pow, ← diagonal_smul]
    congr 1
    funext i
    rw [hxl i]
    rfl
  have hb₂ : ((b₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      lam • (((b₁ : GL (Fin 3) K) ^ j : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have e1 : (b₂ : GL (Fin 3) K) = g * δ₂ * g⁻¹ := by rw [hδ₂]; group
    have e2 : (b₁ : GL (Fin 3) K) ^ j = g * δ₁ ^ j * g⁻¹ := by
      have := conj_pow (a := g⁻¹) (b := (b₁ : GL (Fin 3) K)) (i := j)
      rw [inv_inv] at this
      rw [hδ₁, this]
      group
    rw [e1, e2, Units.val_mul, Units.val_mul, hδ, Units.val_mul, Units.val_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  set w : unitarySU 2 n K 3 := b₂ * (b₁ ^ j)⁻¹ with hw
  have hwm : ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = lam • 1 := by
    rw [hw, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, Units.val_mul, hb₂,
      Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hw1 : (w : unitaryPSU hK.unitary 3) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact mem_unitaryScalars_of_eq_smul hK hwm
  apply h₂
  have : (b₂ : unitaryPSU hK.unitary 3) = (b₁ : unitaryPSU hK.unitary 3) ^ j := by
    rw [hw, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow,
      mul_inv_eq_one] at hw1
    exact hw1
  rw [this]
  exact Subgroup.npow_mem_zpowers _ j

end Commute

section Fixed

variable {n : ℕ} {K : Type} [Field K] (hK : PiField false 2 n K)

omit [Field K] in
theorem mem_center_of_conj_eq_one {X : Type*} [Group X] {z : X} (hz : MulAut.conj z = 1) :
    z ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : z * g * z⁻¹ = g := by
    have := congrArg (fun τ : MulAut X => τ g) hz
    simpa [MulAut.conj_apply] using this
  calc g * z = z * g * z⁻¹ * z := by rw [h1]
    _ = z * g := by group

omit [Field K] in
theorem mul_conj_mul_inv_eq {X : Type*} [Group X] (t : MulAut X) (x : X) :
    t * MulAut.conj x * t⁻¹ = MulAut.conj (t x) := by
  ext g
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [show t (t⁻¹ g) = g from MulEquiv.apply_symm_apply t g]

theorem fixed_of_mem (hq : 2 ^ n % 3 = 2) (hq9 : 2 ^ n % 9 ≠ 8)
    (hZ : Subgroup.center (unitaryPSU hK.unitary 3) = ⊥)
    (B : Subgroup (unitaryPSU hK.unitary 3)) (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (T : Subgroup (MulAut (unitaryPSU hK.unitary 3)))
    (hT : IsPGroup 2 T)
    (hTB : ∀ b ∈ B, ∀ t ∈ T, MulAut.conj b * t * (MulAut.conj b)⁻¹ ∈ T) :
    (∀ y : unitaryPSU hK.unitary 3, MulAut.conj y ∈ T → y = 1) ∧
      ∀ t ∈ T, ∀ b ∈ B, t b = b := by
  set R := T.comap (MulAut.conj : unitaryPSU hK.unitary 3 →* _) with hR
  have hR2 : IsPGroup 2 R := by
    intro y
    obtain ⟨k, hk⟩ := hT ⟨MulAut.conj (y : unitaryPSU hK.unitary 3), y.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : MulAut.conj ((y : unitaryPSU hK.unitary 3) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h2 := mem_center_of_conj_eq_one h1
    rw [hZ, Subgroup.mem_bot] at h2
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h2
  have hBne : B ≠ ⊥ := by
    intro hB0
    rw [hB0, Subgroup.card_bot] at hB9
    norm_num at hB9
  obtain ⟨b₀, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hRb : ∀ r ∈ R,
      (b₀ : unitaryPSU hK.unitary 3) * r * (b₀ : unitaryPSU hK.unitary 3)⁻¹ ∈ R := by
    intro r hr
    change MulAut.conj _ ∈ T
    rw [map_mul, map_mul, map_inv]
    exact hTB _ b₀.2 _ hr
  have hb₀3 : (b₀ : unitaryPSU hK.unitary 3) ^ 3 = 1 := hB.2 _ b₀.2
  have hb₀1' : (b₀ : unitaryPSU hK.unitary 3) ≠ 1 := fun h => hb₀1 (Subtype.ext h)
  have hRbot := eq_bot_of_normalizes_psu hK hq hq9 hb₀3 hb₀1' R hR2 hRb
  have hinn : ∀ y : unitaryPSU hK.unitary 3, MulAut.conj y ∈ T → y = 1 := by
    intro y hy
    have : y ∈ R := hy
    rw [hRbot, Subgroup.mem_bot] at this
    exact this
  refine ⟨hinn, fun t ht b hb => ?_⟩
  have hy : MulAut.conj (b * (t b)⁻¹) ∈ T := by
    rw [map_mul, map_inv, ← mul_conj_mul_inv_eq, _root_.mul_inv_rev, _root_.mul_inv_rev,
      inv_inv, ← mul_assoc, ← mul_assoc]
    exact mul_mem (hTB b hb t ht) (inv_mem ht)
  have h1 := hinn _ hy
  rw [mul_inv_eq_one] at h1
  exact h1.symm

end Fixed

section Field

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem psuConj_mul_psuField_pow (A : unitaryIsom3 h) (σ : K ≃+* K) (m : ℕ) :
    ∃ A' : unitaryIsom3 h,
      (psuConj h A * psuField h σ) ^ m = psuConj h A' * psuField h (σ ^ m) := by
  induction m with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨A', hA'⟩ := ih
    have hcomm : psuField h (σ ^ m) * psuConj h A =
        psuConj h ⟨UnitaryHigher.glAut (σ ^ m) A, glAut_mem_unitaryIsom3 _ A.2⟩ *
          psuField h (σ ^ m) := by
      rw [← psuField_mul_psuConj_mul_inv, inv_mul_cancel_right]
    refine ⟨A' * ⟨UnitaryHigher.glAut (σ ^ m) A, glAut_mem_unitaryIsom3 _ A.2⟩, ?_⟩
    rw [pow_succ, hA', map_mul, pow_succ, map_mul]
    calc psuConj h A' * psuField h (σ ^ m) * (psuConj h A * psuField h σ) =
        psuConj h A' * (psuField h (σ ^ m) * psuConj h A) * psuField h σ := by group
      _ = _ := by rw [hcomm]; group

theorem ringAut_eq_one {n : ℕ} {K : Type} [Field K] (hK : PiField false 2 n K)
    (hq : 2 ^ n % 3 = 2) {σ : K ≃+* K} {k : ℕ} (hσ : σ ^ 2 ^ k = 1) {ε : K} (hε3 : ε ^ 3 = 1)
    (hε1 : ε ≠ 1) (hσε : σ ε = ε) : σ = 1 := by
  classical
  have := hK.finite
  set hu := hK.unitary
  have hn : Odd n := by
    by_contra hne
    obtain ⟨m, rfl⟩ := Nat.not_odd_iff_even.mp hne
    have : 2 ^ (m + m) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  have hcardAut : Nat.card (K ≃+* K) = 2 * n := by
    rw [CFSG.ComponentClassification.AutL2Facts.card_ringAut K Nat.prime_two (f := 2 * n)]
    rw [hK.card]
    show (2 ^ n) ^ 2 = 2 ^ (2 * n)
    rw [← pow_mul, mul_comm]
  have hσ2 : σ ^ 2 = 1 := by
    have h1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hσ
    have h2 : orderOf σ ∣ 2 * n := hcardAut ▸ orderOf_dvd_natCard σ
    have h3 : orderOf σ ∣ 2 := by
      obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      rcases j with _ | _ | j
      · rw [hjeq]; simp
      · rw [hjeq]; simp
      · exfalso
        rw [hjeq] at h2
        have h4 : 2 ^ 2 ∣ 2 * n := (pow_dvd_pow 2 (by omega)).trans h2
        obtain ⟨m, hm⟩ := hn
        omega
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  by_contra hσ1
  have hbarinj : Function.Injective hu.bar := hu.bar.injective
  have hbarbij : Function.Bijective hu.bar :=
    ⟨hbarinj, Finite.surjective_of_injective hbarinj⟩
  set ψ : K ≃+* K := RingEquiv.ofBijective hu.bar hbarbij with hψ
  have hψapp : ∀ c, ψ c = c ^ 2 ^ n := fun c => hu.bar_apply c
  have hψ2 : ψ ^ 2 = 1 := by
    rw [pow_two]
    ext c
    exact hu.bar_bar c
  have hψ1 : ψ ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := hu.exists_bar_ne
    apply hc
    have := congrArg (fun τ : K ≃+* K => τ c) h1
    exact this
  have hσψ : σ ≠ ψ := by
    intro h1
    apply hε1
    have h2 : ψ ε = ε := h1 ▸ hσε
    rw [hψapp] at h2
    have h3 : ε ^ 2 ^ n = ε ^ 2 := by
      rw [← Nat.mod_add_div (2 ^ n) 3, hq, pow_add, pow_mul, hε3, one_pow, mul_one]
    rw [h3] at h2
    have hε0 : ε ≠ 0 := by
      rintro rfl
      norm_num at hε3
    have : ε * ε = ε * 1 := by rw [mul_one, ← pow_two, h2]
    exact mul_left_cancel₀ hε0 this
  have hcyc := CFSG.ComponentClassification.AutL2Facts.isCyclic_ringAut K
  have : Fintype (K ≃+* K) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := K ≃+* K) (n := 2) two_pos
  have hsub : ({1, σ, ψ} : Finset (K ≃+* K)) ⊆
      Finset.univ.filter (fun a : K ≃+* K => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hσ2
    · exact hψ2
  have h3 : ({1, σ, ψ} : Finset (K ≃+* K)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hσψ]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hσ1 h.symm, fun h => hψ1 h.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem norm_det_eq_one (A : unitaryIsom3 h) :
    h.norm ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  CFSG.RankThree.PartTwo.KFacts.norm_det_of_mem_unitaryIsom3 A.2

theorem scalar_mem_unitaryIsom3' {c : Kˣ} (hc : h.norm (c : K) = 1) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [mul_comm]
  exact hc

theorem exists_conj_of_pow (A : unitaryIsom3 h) {k : ℕ} (hA : psuConj h A ^ 2 ^ k = 1) :
    ∃ g : unitarySU p f K 3, psuConj h A = MulAut.conj (g : unitaryPSU h 3) := by
  have hA' : psuConj h (A ^ 2 ^ k) * psuField h 1 = 1 := by
    rw [map_pow, hA, map_one, mul_one]
  obtain ⟨-, c, hc, hcA⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ hA'
  set δ : Kˣ := GeneralLinearGroup.det (A : GL (Fin 3) K) with hδ
  have hδn : h.norm (δ : K) = 1 := by
    rw [hδ, GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one A
  have hδc : δ ^ 2 ^ k = c ^ 3 := by
    have h1 := congrArg (GeneralLinearGroup.det) hcA
    rw [Subgroup.coe_pow, map_pow] at h1
    rw [hδ, h1]
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
      det_diagonal, Fin.prod_const, Units.val_pow_eq_pow_val]
  obtain ⟨u, m, hum⟩ : ∃ u m : ℕ, u * 2 ^ k = 1 + 3 * m := by
    have h3 : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
      have : ¬ 3 ∣ 2 ^ k := fun h3 => by
        have := Nat.prime_three.dvd_of_dvd_pow h3
        omega
      omega
    rcases h3 with h3 | h3
    · exact ⟨1, 2 ^ k / 3, by omega⟩
    · exact ⟨2, 1 + 2 * (2 ^ k / 3), by omega⟩
  set μ : Kˣ := c ^ u * (δ ^ m)⁻¹ with hμ
  have hμ3 : μ ^ 3 = δ := by
    have e1 : (c ^ u) ^ 3 = δ * δ ^ (3 * m) := by
      rw [← pow_mul, mul_comm u 3, pow_mul, ← hδc, ← pow_mul, mul_comm (2 ^ k) u, hum,
        pow_add, pow_one]
    rw [hμ, mul_pow, e1, inv_pow, ← pow_mul, mul_comm m 3, mul_inv_cancel_right]
  have hnormU : ∀ u : Kˣ, h.norm (u : K) = 1 → ∀ v : Kˣ, h.norm (v : K) = 1 →
      h.norm ((u * v : Kˣ) : K) = 1 := by
    intro u hu v hv
    rw [Units.val_mul, norm_mul_eq h, hu, hv, one_mul]
  have hnorminv : ∀ u : Kˣ, h.norm (u : K) = 1 → h.norm ((u⁻¹ : Kˣ) : K) = 1 := by
    intro u hu
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hu, inv_one]
  have hnormpow : ∀ u : Kˣ, h.norm (u : K) = 1 → ∀ j : ℕ, h.norm ((u ^ j : Kˣ) : K) = 1 := by
    intro u hu j
    induction j with
    | zero => simp [UnitaryFieldData.norm]
    | succ j ih =>
      rw [pow_succ]
      exact hnormU _ ih _ hu
  have hμn : h.norm (μ : K) = 1 :=
    hnormU _ (hnormpow c hc u) _ (hnorminv _ (hnormpow δ hδn m))
  set s : unitaryIsom3 h := ⟨GeneralLinearGroup.scalar (Fin 3) μ⁻¹,
    scalar_mem_unitaryIsom3' (hnorminv μ hμn)⟩ with hs
  set g₀ : unitaryIsom3 h := s * A with hg₀
  have hg₀SU : (g₀ : GL (Fin 3) K) ∈ unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨?_, g₀.2⟩
    rw [hg₀, Subgroup.coe_mul, Units.val_mul, det_mul, hs]
    simp only
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Fin.prod_const]
    have h1 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = (δ : K) := by
      rw [hδ, GeneralLinearGroup.val_det_apply]
    rw [h1, ← hμ3, Units.val_pow_eq_pow_val, ← mul_pow, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_pow]
  refine ⟨⟨g₀, hg₀SU⟩, ?_⟩
  rw [conj_mk_eq_psuConj]
  have hs1 : psuConj h s = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [psuConj_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [coe_suConj, Subgroup.coe_inv, hs]
      simp only
      rw [(commute_scalar μ⁻¹ (y : GL (Fin 3) K)).symm.eq, mul_inv_cancel_right]
  have : (⟨(g₀ : GL (Fin 3) K), unitarySU_le_unitaryIsom3 hg₀SU⟩ : unitaryIsom3 h) = s * A := by
    apply Subtype.ext
    rfl
  rw [this, map_mul, hs1, one_mul]

end Field

section Main

variable {n : ℕ} {K : Type} [Field K] (hK : PiField false 2 n K)

omit [Field K] in
theorem commutator_mul_central {G : Type*} [Group G] {a b z₁ z₂ : G}
    (h₁ : z₁ ∈ Subgroup.center G) (h₂ : z₂ ∈ Subgroup.center G) :
    a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have c1 := Subgroup.mem_center_iff.mp h₁
  have c2 := Subgroup.mem_center_iff.mp h₂
  calc a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹ =
      a * (z₁ * b) * z₂ * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (z₁ * z₂ * z₁⁻¹) * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [← c1 b]; group
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by
        rw [← c1 z₂, mul_inv_cancel_right]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [← c2 a⁻¹]; group

theorem psuConj_mul_psuField_mk (A : unitaryIsom3 hK.unitary) (σ : K ≃+* K)
    (g : unitarySU 2 n K 3) :
    (psuConj hK.unitary A * psuField hK.unitary σ) (g : unitaryPSU hK.unitary 3) =
      (((suConj hK.unitary A * suField hK.unitary σ) g : unitarySU 2 n K 3) :
        unitaryPSU hK.unitary 3) := by
  rw [MulAut.mul_apply, psuField_mk, psuConj_mk]
  rfl

theorem exists_fixed_root (hq : 2 ^ n % 3 = 2) {b₁ b₂ : unitarySU 2 n K 3} (h₁3 : b₁ ^ 3 = 1)
    (h₂3 : b₂ ^ 3 = 1) (h₁ : (b₁ : unitaryPSU hK.unitary 3) ≠ 1)
    (h₂ : (b₂ : unitaryPSU hK.unitary 3) ∉ Subgroup.zpowers (b₁ : unitaryPSU hK.unitary 3))
    (hcomm : (b₁ : unitaryPSU hK.unitary 3) * (b₂ : unitaryPSU hK.unitary 3) =
      (b₂ : unitaryPSU hK.unitary 3) * (b₁ : unitaryPSU hK.unitary 3))
    (A : unitaryIsom3 hK.unitary) (σ : K ≃+* K)
    (hf₁ : (psuConj hK.unitary A * psuField hK.unitary σ) (b₁ : unitaryPSU hK.unitary 3) =
      (b₁ : unitaryPSU hK.unitary 3))
    (hf₂ : (psuConj hK.unitary A * psuField hK.unitary σ) (b₂ : unitaryPSU hK.unitary 3) =
      (b₂ : unitaryPSU hK.unitary 3)) :
    ∃ ε : K, ε ^ 3 = 1 ∧ ε ≠ 1 ∧ σ ε = ε := by
  set φ := suConj hK.unitary A * suField hK.unitary σ with hφ
  have hφg : ∀ g : unitarySU 2 n K 3, ((φ g : unitarySU 2 n K 3) : GL (Fin 3) K) =
      (A : GL (Fin 3) K) * UnitaryHigher.glAut σ (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ := by
    intro g
    rw [hφ, MulAut.mul_apply, coe_suConj, coe_suField, Subgroup.coe_inv]
  have hz : ∀ g : unitarySU 2 n K 3,
      (psuConj hK.unitary A * psuField hK.unitary σ) (g : unitaryPSU hK.unitary 3) =
        (g : unitaryPSU hK.unitary 3) →
        ∃ z ∈ Subgroup.center (unitarySU 2 n K 3), φ g = g * z := by
    intro g hg
    rw [psuConj_mul_psuField_mk hK] at hg
    refine ⟨g⁻¹ * φ g, ?_, by group⟩
    have hmem : g⁻¹ * φ g ∈ unitaryScalars hK.unitary 3 := by
      rw [← QuotientGroup.eq]
      exact hg.symm
    exact unitaryScalars_le_center hK.unitary 3 hmem
  obtain ⟨z₁, hz₁, hφ₁⟩ := hz b₁ hf₁
  obtain ⟨z₂, hz₂, hφ₂⟩ := hz b₂ hf₂
  set w := b₁ * b₂ * b₁⁻¹ * b₂⁻¹ with hw
  have hφw : φ w = w := by
    rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, hφ₁, hφ₂]
    exact commutator_mul_central hz₁ hz₂
  have hwZ : w ∈ unitaryScalars hK.unitary 3 := by
    rw [← QuotientGroup.eq_one_iff, hw, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm]
    group
  obtain ⟨c, -, hc3, hwc⟩ := hwZ
  have hc1 : c ≠ 1 := by
    intro hc1
    apply not_commute_of_lift hK hq h₁3 h₂3 h₁ h₂
    have hw1 : w = 1 := by
      apply Subtype.ext
      rw [hwc, hc1, map_one, Subgroup.coe_one]
    rw [hw] at hw1
    calc b₁ * b₂ = b₁ * b₂ * b₁⁻¹ * b₂⁻¹ * (b₂ * b₁) := by group
      _ = b₂ * b₁ := by rw [hw1, one_mul]
  refine ⟨(c : K), ?_, fun h => hc1 (Units.ext h), ?_⟩
  · rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  · have h1 := congrArg (fun g : unitarySU 2 n K 3 => (g : GL (Fin 3) K)) hφw
    rw [hφg, hwc] at h1
    have h2 : UnitaryHigher.glAut σ (GeneralLinearGroup.scalar (Fin 3) c) =
        GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) c) := by
      apply Units.ext
      rw [UnitaryHigher.coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
        scalar_apply, scalar_apply, diagonal_map (map_zero σ), Units.coe_map]
      rfl
    rw [h2, (commute_scalar _ (A : GL (Fin 3) K)).eq, mul_inv_cancel_right] at h1
    have h3 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
      Units.coe_map] at h3
    exact h3

theorem eq_bot_psu (hq : 2 ^ n % 3 = 2) (hq9 : 2 ^ n % 9 ≠ 8) (hq2 : 2 < 2 ^ n)
    (hZ : Subgroup.center (unitaryPSU hK.unitary 3) = ⊥)
    (B : Subgroup (unitaryPSU hK.unitary 3)) (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (T : Subgroup (MulAut (unitaryPSU hK.unitary 3)))
    (hT : IsPGroup 2 T)
    (hTB : ∀ b ∈ B, ∀ t ∈ T, MulAut.conj b * t * (MulAut.conj b)⁻¹ ∈ T) : T = ⊥ := by
  obtain ⟨hinn, hfix⟩ := fixed_of_mem hK hq hq9 hZ B hB hB9 T hT hTB
  have hBne : B ≠ ⊥ := by
    intro hB0
    rw [hB0, Subgroup.card_bot] at hB9
    norm_num at hB9
  obtain ⟨⟨x₁, hx₁B⟩, hx₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hx₁1' : x₁ ≠ 1 := fun h => hx₁1 (Subtype.ext h)
  have hx₁3 : x₁ ^ 3 = 1 := hB.2 x₁ hx₁B
  have hord : orderOf x₁ = 3 := orderOf_eq_prime hx₁3 hx₁1'
  have := hK.finite
  have : Finite (unitaryPSU hK.unitary 3) := inferInstance
  obtain ⟨x₂, hx₂B, hx₂⟩ : ∃ x₂ ∈ B, x₂ ∉ Subgroup.zpowers x₁ := by
    by_contra hcon
    have hle : B ≤ Subgroup.zpowers x₁ := fun y hy => by
      by_contra hy'
      exact hcon ⟨y, hy, hy'⟩
    have := Subgroup.card_le_of_le hle
    rw [hB9, Nat.card_zpowers, hord] at this
    norm_num at this
  have hx₂3 : x₂ ^ 3 = 1 := hB.2 x₂ hx₂B
  obtain ⟨b₁, rfl⟩ := QuotientGroup.mk_surjective x₁
  obtain ⟨b₂, rfl⟩ := QuotientGroup.mk_surjective x₂
  have hb₁3 := pow_three_eq_one_of_mk hK hq hq9 b₁ hx₁3
  have hb₂3 := pow_three_eq_one_of_mk hK hq hq9 b₂ hx₂3
  have hcomm : ((b₁ : unitaryPSU hK.unitary 3)) * (b₂ : unitaryPSU hK.unitary 3) =
      (b₂ : unitaryPSU hK.unitary 3) * (b₁ : unitaryPSU hK.unitary 3) := by
    have := isMulCommutative_iff.mp hB.1 ⟨_, hx₁B⟩ ⟨_, hx₂B⟩
    exact congrArg Subtype.val this
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq2 t
  obtain ⟨ε, hε3, hε1, hσε⟩ := exists_fixed_root hK hq hb₁3 hb₂3 hx₁1' hx₂ hcomm A σ
    (hfix _ ht _ hx₁B) (hfix _ ht _ hx₂B)
  obtain ⟨A', hA'⟩ := psuConj_mul_psuField_pow A σ (2 ^ k)
  rw [hA'] at hk'
  have hσk := (eq_one_of_psuConj_mul_psuField_eq_one A' _ hk').1
  have hσ1 := ringAut_eq_one hK hq hσk hε3 hε1 hσε
  rw [hσ1, map_one, mul_one] at ht ⊢
  have hk'' : psuConj hK.unitary A ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa [hσ1] using this
  obtain ⟨g, hg⟩ := exists_conj_of_pow A hk''
  rw [hg] at ht ⊢
  rw [hinn _ ht, map_one]

end Main

section Transport

variable {Q : Type} [Group Q]

theorem isElemAbelian_map' {X : Type*} [Group X] {p : ℕ} (φ : Q →* X) {E : Subgroup Q}
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.map φ) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem centerDescend_injective [Group.IsPerfect Q] :
    Function.Injective (centerDescend Q) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro τ hτ
  rw [MonoidHom.mem_ker] at hτ
  rw [Subgroup.mem_bot]
  apply eq_one_of_forall_mul_inv_mem_center
  intro s
  have h1 := congrArg (fun α : MulAut (Q ⧸ Subgroup.center Q) => α (s : Q ⧸ Subgroup.center Q)) hτ
  simp only [centerDescend_mk, MulAut.one_apply] at h1
  rw [← QuotientGroup.eq]
  exact h1.symm

end Transport

end KS165UProof

open KS165UProof CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
  CFSG.ClassicalGroups.UnitaryFlag in
theorem ks165U : KS165U := by
  intro Q _ _ n hq hq9 hQ hZ3 hiso B hB hB9 T hT hTB
  obtain ⟨e⟩ := hiso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := by
    rcases n with _ | n
    · norm_num at hq
    · omega
  set K := GaloisField 2 (2 * n) with hKdef
  have hK : PiField false 2 n K := Sec13.piField_galoisField_two 2 n hn
  obtain ⟨ψ⟩ := nonempty_unitaryPSU_mulEquiv_projSU (p := 2) (f := n) hK.unitary
  set φ : Q ⧸ Subgroup.center Q ≃* unitaryPSU hK.unitary 3 := e.trans ψ.symm with hφ
  obtain ⟨hperf, hsimp, hnab⟩ := hQ
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hsimp
  have hZQ : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q))
      with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := h ▸ Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.mp hb a)
  have hZP : Subgroup.center (unitaryPSU hK.unitary 3) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : φ.symm z ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have := hz (φ g)
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, this]
    rw [hZQ, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← φ.apply_symm_apply z, hz', map_one]
  have hq2 : 2 < 2 ^ n := by
    by_contra hle
    have hn1 : n = 1 := by
      rcases n with _ | _ | n
      · omega
      · rfl
      · exfalso
        apply hle
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    subst hn1
    have hsol : Group.IsSolvable (CFSG.Assembly.RankThreeEven.projSU 3 2 1) := by
      rw [Sec13.projSU_eq]
      exact Sec13.isSolvable_projImage_slPi_two (Sec13.piField_galoisField_two 2 1 le_rfl) rfl
    have hsolQ : Group.IsSolvable (Q ⧸ Subgroup.center Q) := Group.isSolvable_of_surjective
      (f := e.symm.toMonoidHom) e.symm.surjective
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolQ) a b)
  set Ψ : MulAut Q →* MulAut (unitaryPSU hK.unitary 3) :=
    (MulAut.congr φ).toMonoidHom.comp (centerDescend Q) with hΨ
  have : Group.IsPerfect Q := hperf
  have hΨinj : Function.Injective Ψ :=
    (MulAut.congr φ).injective.comp centerDescend_injective
  have hΨconj : ∀ b : Q, Ψ (MulAut.conj b) =
      MulAut.conj (φ (b : Q ⧸ Subgroup.center Q)) := by
    intro b
    rw [hΨ, MonoidHom.comp_apply, KFacts.centerDescend_conj]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  set B' : Subgroup (unitaryPSU hK.unitary 3) := (B.map π).map φ.toMonoidHom with hB'
  have hB'ab : CFSG.Assembly.IsElemAbelian 3 B' :=
    isElemAbelian_map' _ (isElemAbelian_map' _ hB)
  have hinjB : Function.Injective (φ.toMonoidHom.comp (π.comp B.subtype)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ φ.injective, MonoidHom.comp_apply, Subgroup.coe_subtype, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
    rw [Subgroup.mem_bot]
    have hb3 : (b : Q) ^ 3 = 1 := hB.2 _ b.2
    have h1 : orderOf (⟨(b : Q), hb⟩ : Subgroup.center Q) ∣ Nat.card (Subgroup.center Q) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (⟨(b : Q), hb⟩ : Subgroup.center Q) ∣ 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hb3
    have h3 : orderOf (⟨(b : Q), hb⟩ : Subgroup.center Q) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
      · exact h
      · exact absurd (h ▸ h1) hZ3
    rw [orderOf_eq_one_iff, Subgroup.mk_eq_one] at h3
    exact Subtype.ext h3
  have hB'9 : Nat.card B' = 9 := by
    have hrange : B' = (φ.toMonoidHom.comp (π.comp B.subtype)).range := by
      rw [hB', MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinjB).toEquiv, hB9]
  set T' := T.map Ψ with hT'
  have hT'2 : IsPGroup 2 T' := hT.map Ψ
  have hT'B' : ∀ b ∈ B', ∀ t ∈ T', MulAut.conj b * t * (MulAut.conj b)⁻¹ ∈ T' := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨MulAut.conj b * t * (MulAut.conj b)⁻¹, hTB b hb t ht, ?_⟩
    rw [map_mul, map_mul, map_inv, hΨconj]
    rfl
  have hT'bot := eq_bot_psu hK hq hq9 hq2 hZP B' hB'ab hB'9 T' hT'2 hT'B'
  exact (Subgroup.map_eq_bot_iff_of_injective T hΨinj).mp hT'bot

end CFSG.RankThree.PartTwo.Sec16
