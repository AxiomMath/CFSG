module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148RNineDef
public import CFSG.RankThree.PartTwo.KFacts.K71SU3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff)
open Matrix

section Arith

theorem mod_six_of_two_pow_mod_nine {f : ℕ} (h9 : 2 ^ f % 9 = 8) : f % 6 = 3 := by
  have h : 2 ^ f % 9 = 2 ^ (f % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod f 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  obtain ⟨r, hr⟩ : ∃ r, r = f % 6 := ⟨_, rfl⟩
  have hlt : r < 6 := hr ▸ Nat.mod_lt _ (by norm_num)
  rw [h, ← hr] at h9
  rw [← hr]
  interval_cases r <;> first | rfl | (norm_num at h9)

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : n % 2 = 1) : 2 ^ n % 3 = 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = 2 * r + 1 := ⟨n / 2, by omega⟩
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_cube_root_of_pow {K : Type} [Field K] [Finite K] {Q m : ℕ}
    (hK : Nat.card K = Q ^ 2) (hQ : 1 ≤ Q) (hm : Q + 1 = 3 * m) {u : Kˣ} (hu : u ^ m = 1) :
    ∃ μ : Kˣ, μ ^ 3 = u ∧ μ ^ (Q + 1) = 1 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ζ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hζ
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcard : Nat.card Kˣ = (Q - 1) * (Q + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    zify [hQ2, hQ]
    ring
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ζ ^ a = u := mem_powers_iff_mem_zpowers.mpr (hζ u)
  have hdvd : (Q - 1) * (Q + 1) ∣ a * m := by
    rw [← hcard, ← hord]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_mul, ha, hu])
  have hm0 : 0 < m := by omega
  have h3 : 3 * (Q - 1) ∣ a := by
    refine Nat.dvd_of_mul_dvd_mul_right hm0 ?_
    calc 3 * (Q - 1) * m = (Q - 1) * (Q + 1) := by rw [hm]; ring
      _ ∣ a * m := hdvd
  obtain ⟨b, hb⟩ := h3
  refine ⟨ζ ^ ((Q - 1) * b), ?_, ?_⟩
  · rw [← pow_mul, ← ha, hb]
    ring_nf
  · rw [← pow_mul, show (Q - 1) * b * (Q + 1) = (Q - 1) * (Q + 1) * b by ring, pow_mul, ← hcard,
      ← hord, pow_orderOf_eq_one, one_pow]

theorem pow_succ_eq_one_of_fixed {K : Type} [Field K] {p f e : ℕ} {k : Subfield K} [Finite k]
    (hfe : f = 3 * e) (hk : Nat.card k = p ^ (2 * e)) {w : K} (hwk : w ∈ k)
    (hw : w ^ (p ^ f + 1) = 1) : w ^ (p ^ e + 1) = 1 := by
  have := Fintype.ofFinite k
  have h1 : (⟨w, hwk⟩ : k) ^ Fintype.card k = ⟨w, hwk⟩ := FiniteField.pow_card _
  rw [← Nat.card_eq_fintype_card, hk] at h1
  have h2 : w ^ p ^ (2 * e) = w := congrArg Subtype.val h1
  have h3 : p ^ f = p ^ (2 * e) * p ^ e := by rw [hfe, ← pow_add]; ring_nf
  rw [h3, pow_succ, pow_mul, h2] at hw
  rw [pow_succ]
  exact hw

end Arith

section Field

variable {f : ℕ} {K : Type} [Field K]

theorem glAut_scalar (σ : K ≃+* K) (c : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
    scalar_apply, diagonal_map (map_zero σ), Units.coe_map]
  rfl

theorem kf148PGUFieldCent : Sec14.Ronan148R.KF148PGUFieldCent := by
  intro f K _ h h9 σ hσ A hA
  have := h.finite
  have h2 : Nat.Prime 2 := Nat.prime_two
  obtain ⟨f₀, hf, -, hk⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have hf6 := mod_six_of_two_pow_mod_nine h9
  have hq3 : 2 ^ f₀ % 3 = 2 := two_pow_mod_three_of_odd (by omega)
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ f₀ = 3 * t + 2 := ⟨2 ^ f₀ / 3, by omega⟩
  set m : ℕ := (2 ^ f₀ + 1) * (3 * t ^ 2 + 3 * t + 1) with hmdef
  have hQf : 2 ^ f = (2 ^ f₀) ^ 3 := by rw [hf, ← pow_mul, mul_comm]
  have hm : 2 ^ f + 1 = 3 * m := by
    rw [hQf, hmdef, ht]
    ring
  set lam : K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det with hlam
  have hAu : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := A.2
  have hlamN : h.bar lam * lam = 1 := by
    have h1 := congrArg Matrix.det hAu
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
      show (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar).det = h.bar lam from
        (RingHom.map_det h.bar _).symm] at h1
    exact h1
  have hlamσ : σ lam = lam := by
    have h1 := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K).det) hA
    simp only [coe_glAut] at h1
    rw [show (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ).det = σ lam from
      (RingHom.map_det (σ : K →+* K) _).symm] at h1
    exact h1
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hlamN
    exact zero_ne_one hlamN
  have hlamQ : lam ^ (2 ^ f + 1) = 1 := by
    rw [pow_succ, ← UnitaryFieldData.bar_apply]
    exact hlamN
  have hlamq : lam ^ (2 ^ f₀ + 1) = 1 :=
    pow_succ_eq_one_of_fixed hf hk ((mem_fixedField_iff σ lam).mpr hlamσ) hlamQ
  set u : Kˣ := (Units.mk0 lam hlam0)⁻¹ with hu
  have hum : u ^ m = 1 := by
    apply Units.ext
    rw [hu, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hmdef,
      pow_mul, hlamq, one_pow, inv_one, Units.val_one]
  have hK2 : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨μ, hμ3, hμN⟩ := exists_cube_root_of_pow hK2 (Nat.one_le_two_pow) hm hum
  have hμ3' : (μ : K) ^ 3 = lam⁻¹ := by
    have := congrArg (fun v : Kˣ => (v : K)) hμ3
    simpa [hu] using this
  have hμN' : h.norm (μ : K) = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ', ← Units.val_pow_eq_pow_val,
      hμN, Units.val_one]
  set S := GeneralLinearGroup.scalar (Fin 3) μ with hS
  set g : GL (Fin 3) K := S * (A : GL (Fin 3) K) with hg
  have hgdet : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [hg, Units.val_mul, Matrix.det_mul, hS, GeneralLinearGroup.coe_scalar, scalar_apply,
      det_diagonal, Fin.prod_const, ← hlam, hμ3', inv_mul_cancel₀ hlam0]
  have hgU : (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hg, Units.val_mul, hS, GeneralLinearGroup.coe_scalar, scalar_apply, Matrix.map_mul,
      Matrix.transpose_mul, diagonal_map (map_zero h.bar), diagonal_transpose]
    calc (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
          diagonal (fun _ : Fin 3 => h.bar (μ : K)) *
          (diagonal (fun _ : Fin 3 => (μ : K)) * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        = ((μ : K) * h.bar (μ : K)) • ((((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map
            h.bar)ᵀ * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
          rw [← smul_one_eq_diagonal, ← smul_one_eq_diagonal]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul]
      _ = 1 := by
          rw [hAu, ← UnitaryFieldData.norm, hμN', one_smul]
  have hgSU : g ∈ unitarySU 2 f K 3 := (mem_unitarySU_iff h).mpr ⟨hgdet, hgU⟩
  refine ⟨⟨g, hgSU⟩, ?_, ?_⟩
  ·
    rw [show unitaryProj h 3 ⟨g, hgSU⟩ = ((⟨g, hgSU⟩ : unitarySU 2 f K 3) : unitaryPSU h 3) from
      rfl, conj_mk_eq_psuConj]
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [psuConj_mk, psuConj_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suConj, coe_suConj]
    have hc := (commute_scalar μ ((A : GL (Fin 3) K) * (y : GL (Fin 3) K) *
      (A : GL (Fin 3) K)⁻¹)).eq
    change (A : GL (Fin 3) K) * y * (A : GL (Fin 3) K)⁻¹ = g * y * g⁻¹
    calc (A : GL (Fin 3) K) * y * (A : GL (Fin 3) K)⁻¹
        = ((A : GL (Fin 3) K) * y * (A : GL (Fin 3) K)⁻¹) * S * S⁻¹ := by group
      _ = S * ((A : GL (Fin 3) K) * y * (A : GL (Fin 3) K)⁻¹) * S⁻¹ := by rw [hc]
      _ = g * y * g⁻¹ := by rw [hg]; group
  ·
    rw [show unitaryProj h 3 ⟨g, hgSU⟩ = ((⟨g, hgSU⟩ : unitarySU 2 f K 3) : unitaryPSU h 3) from
      rfl, psuField_mk, QuotientGroup.eq]
    set c : Kˣ := (Units.map (σ : K →* K) μ)⁻¹ * μ with hc
    have hσμ3 : (Units.map (σ : K →* K) μ) ^ 3 = μ ^ 3 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, ← map_pow, hμ3',
        map_inv₀, hlamσ, ← hμ3', Units.val_pow_eq_pow_val]
    have hσμN : (Units.map (σ : K →* K) μ) ^ (2 ^ f + 1) = 1 := by
      rw [← map_pow, hμN, map_one]
    refine ⟨c, ?_, ?_, ?_⟩
    · have hcN : c ^ (2 ^ f + 1) = 1 := by
        rw [hc, mul_pow, inv_pow, hσμN, hμN, inv_one, one_mul]
      rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ',
        ← Units.val_pow_eq_pow_val, hcN, Units.val_one]
    · rw [hc, mul_pow, inv_pow, hσμ3, inv_mul_cancel]
    · have hgσ : glAut σ g = GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) μ) *
          (A : GL (Fin 3) K) := by
        rw [hg, map_mul, hS, glAut_scalar, hA]
      change (glAut σ g)⁻¹ * g = GeneralLinearGroup.scalar (Fin 3) c
      rw [hgσ, hg, hS, hc, map_mul, map_inv]
      have hcomm := (commute_scalar ((Units.map (σ : K →* K) μ)⁻¹ * μ)
        (A : GL (Fin 3) K)).eq
      rw [map_mul, map_inv] at hcomm
      calc (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) μ) *
            (A : GL (Fin 3) K))⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ * (A : GL (Fin 3) K))
          = (A : GL (Fin 3) K)⁻¹ * (((GeneralLinearGroup.scalar (Fin 3)
              (Units.map (σ : K →* K) μ))⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ) *
                (A : GL (Fin 3) K)) := by group
        _ = (A : GL (Fin 3) K)⁻¹ * ((A : GL (Fin 3) K) *
              ((GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) μ))⁻¹ *
                GeneralLinearGroup.scalar (Fin 3) μ)) := by rw [← hcomm]
        _ = (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) μ))⁻¹ *
              GeneralLinearGroup.scalar (Fin 3) μ := by group

end Field

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
