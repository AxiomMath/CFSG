module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open Matrix.GeneralLinearGroup

private lemma triD4Line_norm_algebraMap_units (k K : Type) [Field k] [Field K] [Algebra k K]
    (hdeg : Module.finrank k K = 3) (a : kˣ) :
    Units.map (Algebra.norm k (S := K)) (Units.map (algebraMap k K).toMonoidHom a) = a ^ 3 := by
  apply Units.ext
  show Algebra.norm k (algebraMap k K (a : k)) = (a : k) ^ 3
  rw [Algebra.norm_algebraMap, hdeg]

private lemma triD4Line_cubeKer_card (k : Type) [Field k] [Finite k]
    (h3 : 3 ∣ Nat.card k - 1) :
    Nat.card ((powMonoidHom 3 : kˣ →* kˣ).ker) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := kˣ) 3 (by rwa [Nat.card_units])
  have hprim : IsPrimitiveRoot (ω : k) 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr (hω ▸ IsPrimitiveRoot.orderOf ω)
  have hcard : Nat.card (rootsOfUnity 3 k) = 3 := hprim.card_rootsOfUnity
  rwa [rootsOfUnity_eq_ker] at hcard

private lemma triD4Line_cube_decomp (G : Type) [CommGroup G] [Finite G]
    (hker : Nat.card ((powMonoidHom 3 : G →* G).ker) = 3)
    (ν : G) (hν : ν ∉ (powMonoidHom 3 : G →* G).range) (δ : G) :
    ∃ a : G, ∃ j : ℕ, δ = a ^ 3 * ν ^ j := by
  classical
  let f : G →* G := powMonoidHom 3
  have hcardC : Nat.card f.range * 3 = Nat.card G := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [show f.ker = (powMonoidHom 3 : G →* G).ker from rfl, hker] at h
    rwa [mul_comm] at h
  haveI : Nonempty f.range := ⟨⟨1, f.range.one_mem⟩⟩
  have hindex : f.range.index = 3 :=
    Nat.mul_left_cancel (Nat.card_pos (α := f.range))
      (by rw [Subgroup.card_mul_index, hcardC])
  have hcoat : IsCoatom f.range :=
    Subgroup.isCoatom_of_index_prime (by simpa [hindex] using Nat.prime_three)
  have hsup : f.range ⊔ Subgroup.zpowers ν = ⊤ := by
    have hne : f.range ⊔ Subgroup.zpowers ν ≠ f.range := by
      intro h
      exact hν (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers ν))
    exact (hcoat.ne_iff_eq_top le_sup_left).mp hne
  obtain ⟨c, hc, b, hb, hcb⟩ := (Subgroup.mem_sup).1 (hsup ▸ Subgroup.mem_top δ)
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hc
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 ((mem_zpowers_iff_mem_range_orderOf).1 hb)
  have ha' : a ^ 3 = c := ha
  exact ⟨a, j, by rw [ha', hj, hcb]⟩

private lemma triD4LineMk_congr (k K : Type) [Field k] [Field K] [Algebra k K]
    {g g' : GL (Fin 3) k} {c c' : Kˣ} (hg : g = g') (hc : c = c')
    (h : det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : det g' = Units.map (Algebra.norm k (S := K)) c') :
    triD4LineMk k K g c h = triD4LineMk k K g' c' h' := by
  subst hg
  subst hc
  rfl

private lemma triD4Line_mk_scalar_mem_zpowers (k K : Type) [Field k] [Field K] [Algebra k K]
    (ζ : kˣ) (hζ3 : ζ ^ 3 = 1) (hζne : ζ ≠ 1)
    (hζ : det (scalar (Fin 3) ζ) = Units.map (Algebra.norm k (S := K)) 1)
    (μ : kˣ) (hμ3 : μ ^ 3 = 1)
    (hμ : det (scalar (Fin 3) μ) = Units.map (Algebra.norm k (S := K)) 1) :
    triD4LineMk k K (scalar (Fin 3) μ) 1 hμ ∈
      Subgroup.zpowers (triD4LineMk k K (scalar (Fin 3) ζ) 1 hζ) := by
  have hord : orderOf ζ = 3 := by
    have hdvd : orderOf ζ ∣ 3 := orderOf_dvd_of_pow_eq_one hζ3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hζne
    · exact h
  have hprim : IsPrimitiveRoot (ζ : k) 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr (hord ▸ IsPrimitiveRoot.orderOf ζ)
  have hμK : (μ : k) ^ 3 = 1 := by
    have := congrArg Units.val hμ3
    simpa [Units.val_pow_eq_pow_val] using this
  obtain ⟨i, hi, hiu⟩ := hprim.eq_pow_of_pow_eq_one hμK
  have hμeq : μ = ζ ^ i := by
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val] using hiu.symm
  have hscalar : scalar (Fin 3) μ = (scalar (Fin 3) ζ) ^ i := by rw [hμeq, map_pow]
  have hpowdet : det
      ((scalar (Fin 3) ζ) ^ i) =
      Units.map (Algebra.norm k (S := K)) (1 ^ i) := by rw [map_pow, map_pow, hζ]
  have hmem : triD4LineMk k K (scalar (Fin 3) μ) 1 hμ =
      (triD4LineMk k K (scalar (Fin 3) ζ) 1 hζ) ^ i := by
    rw [triD4LineMk_pow k K (scalar (Fin 3) ζ) 1 hζ i hpowdet]
    exact triD4LineMk_congr k K hscalar (one_pow i).symm hμ hpowdet
  rw [hmem]
  exact Subgroup.npow_mem_zpowers _ i

private lemma triD4LineMk_conj (k K : Type) [Field k] [Field K] [Algebra k K]
    (gx g : GL (Fin 3) k) (d c : Kˣ)
    (hd : det gx = Units.map (Algebra.norm k (S := K)) d)
    (hc : det g = Units.map (Algebra.norm k (S := K)) c)
    (hbig : det (gx * g * gx⁻¹) = Units.map (Algebra.norm k (S := K)) (d * c * d⁻¹)) :
    triD4LineMk k K gx d hd * triD4LineMk k K g c hc * (triD4LineMk k K gx d hd)⁻¹ =
      triD4LineMk k K (gx * g * gx⁻¹) (d * c * d⁻¹) hbig := by
  have h1 : det (gx * g) = Units.map (Algebra.norm k (S := K)) (d * c) := by
    rw [map_mul, map_mul, hd, hc]
  have h2 : det gx⁻¹ = Units.map (Algebra.norm k (S := K)) d⁻¹ := by
    rw [map_inv, map_inv, hd]
  rw [triD4LineMk_mul k K gx g d c hd hc h1,
    triD4LineMk_inv k K gx d hd h2,
    triD4LineMk_mul k K (gx * g) gx⁻¹ (d * c) d⁻¹ h1 h2 hbig]

private lemma triD4Line_lambda_exists (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (gx : GL (Fin 3) k) (cx : Kˣ)
    (hcx : det gx = Units.map (Algebra.norm k (S := K)) cx)
    (e : TriD4LineX k K)
    (hxe : triD4LineMk k K gx cx hcx * triD4LineSigma k K σ e * (triD4LineMk k K gx cx hcx)⁻¹ = e) :
    ∃ (g : GL (Fin 3) k) (c : Kˣ)
      (h : det g = Units.map (Algebra.norm k (S := K)) c)
      (lam : kˣ), e = triD4LineMk k K g c h ∧ gx * g * gx⁻¹ = scalar (Fin 3) lam * g ∧
        Units.mapEquiv σ.toRingEquiv.toMulEquiv c =
          Units.map (algebraMap k K).toMonoidHom lam * c ∧ lam ^ 3 = 1 := by
  obtain ⟨g, c, h, rfl⟩ := triD4LineMk_surjective k K e
  let σc : Kˣ := Units.mapEquiv σ.toRingEquiv.toMulEquiv c
  have h' : det g = Units.map (Algebra.norm k (S := K)) σc :=
    h.trans (Units.ext (Algebra.norm_eq_of_algEquiv σ (c : K))).symm
  rw [triD4LineSigma_mk k K σ g c h h'] at hxe
  have hbig : det (gx * g * gx⁻¹) = Units.map (Algebra.norm k (S := K)) (cx * σc * cx⁻¹) := by
    simp only [map_mul, map_inv, hcx, h']
  rw [triD4LineMk_conj k K gx g cx σc hcx h' hbig] at hxe
  obtain ⟨μ, hμg, hμc⟩ :=
    (triD4LineMk_eq_mk_iff k K (gx * g * gx⁻¹) g (cx * σc * cx⁻¹) c hbig h).1 hxe
  have hc_eq : c = Units.map (algebraMap k K).toMonoidHom μ * σc := by
    rw [hμc]
    congr 1
    rw [mul_assoc, mul_comm σc cx⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hG : gx * g * gx⁻¹ = scalar (Fin 3) μ⁻¹ * g := by
    conv_rhs => rw [hμg]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hσc : σc = Units.map (algebraMap k K).toMonoidHom μ⁻¹ * c := by
    have h1 : Units.map (algebraMap k K).toMonoidHom μ⁻¹ * c = σc := by
      conv_lhs => rw [hc_eq]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    exact h1.symm
  have hlam3 : (μ⁻¹) ^ 3 = 1 := by
    have hfin : det g = (μ⁻¹) ^ 3 * det g := by
      calc det g = det (gx * g * gx⁻¹) := by
            rw [map_mul, map_mul, map_inv, mul_assoc, mul_comm (det g) (det gx)⁻¹,
              ← mul_assoc, mul_inv_cancel, one_mul]
        _ = det (scalar (Fin 3) μ⁻¹ * g) := by rw [hG]
        _ = (μ⁻¹) ^ 3 * det g := by rw [map_mul, det_scalar, Fintype.card_fin]
    exact mul_right_cancel (hfin.symm.trans (one_mul (det g)).symm)
  exact ⟨g, c, h, μ⁻¹, rfl, hG, hσc, hlam3⟩

private lemma triD4Line_mem_N0_of_lambda_eq_one (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3)
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : det g = Units.map (Algebra.norm k (S := K)) c) (lam : kˣ)
    (hc : Units.mapEquiv σ.toRingEquiv.toMulEquiv c =
      Units.map (algebraMap k K).toMonoidHom lam * c) (h1 : lam = 1) :
    triD4LineMk k K g c h ∈ triD4LineN0 k K := by
  refine (triD4LineMk_mem_N0_iff k K hdeg g c h).2 ?_
  have hσc : σ (c : K) = (c : K) := by
    have := congrArg Units.val hc
    rw [h1, map_one, one_mul] at this
    simpa using this
  obtain ⟨a, ha⟩ := triD4Line_exists_algebraMap_of_sigma_eq k K hdeg σ hσ (c : K) hσc
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact c.ne_zero ha.symm
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  rw [Units.coe_map, Units.val_mk0]
  exact ha.symm

private lemma triD4Line_conj_eq (k K : Type) [Field k] [Field K] [Algebra k K]
    (gx : GL (Fin 3) k) (d : Kˣ)
    (hd : det gx = Units.map (Algebra.norm k (S := K)) d)
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : det g = Units.map (Algebra.norm k (S := K)) c)
    (lam : kˣ)
    (hw : det (scalar (Fin 3) lam) = Units.map (Algebra.norm k (S := K)) 1)
    (hg : gx * g * gx⁻¹ = scalar (Fin 3) lam * g) :
    triD4LineMk k K gx d hd * triD4LineMk k K g c h * (triD4LineMk k K gx d hd)⁻¹ =
      triD4LineMk k K (scalar (Fin 3) lam) 1 hw * triD4LineMk k K g c h := by
  have hbig : det (gx * g * gx⁻¹) = Units.map (Algebra.norm k (S := K)) (d * c * d⁻¹) := by
    simp only [map_mul, map_inv, hd, h]
  rw [triD4LineMk_conj k K gx g d c hd h hbig]
  rw [triD4LineMk_mul k K (scalar (Fin 3) lam) g 1 c hw h (by rw [map_mul, map_mul, hw, h])]
  exact triD4LineMk_congr k K hg
    (by rw [one_mul, mul_assoc, mul_comm c d⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]) _ _

theorem triD4LineX_moves_line_of_not_le_N0 (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (hdeg : Module.finrank k K = 3) (h3 : 3 ∣ Nat.card k - 1) (σ : K ≃ₐ[k] K)
    (hσ : orderOf σ = 3)
    (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3) (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K))
    (E : Subgroup (TriD4LineX k K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hzE : z₀ ∈ E) (x : TriD4LineX k K) (hx : ∀ e ∈ E, x * triD4LineSigma k K σ e * x⁻¹ = e)
    (hEN : ¬ E ≤ triD4LineN0 k K) :
    ∃ n : TriD4LineX k K, (∀ e' ∈ E, n * e' * n⁻¹ ∈ E) ∧
      (∀ e ∈ E, e ∉ Subgroup.zpowers z₀ → n * e * n⁻¹ ∉ Subgroup.zpowers e) ∧
      n * (x * triD4LineSigma k K σ n * x⁻¹)⁻¹ ∈ E := by
  classical
  haveI : Finite k := Finite.of_injective _ (algebraMap k K).injective
  obtain ⟨ζ, hζ3, hζne1, hζdet, hz0eq⟩ :=
    triD4Line_eq_mk_of_mem_center k K h3 hzc hz₀
  have hz0N : z₀ ∈ triD4LineN0 k K := by
    rw [← hz0eq]
    exact (mem_triD4LineN0_iff k K _).2 ⟨_, hζdet, rfl⟩
  have hz0_le_E : Subgroup.zpowers z₀ ≤ E := Subgroup.zpowers_le.mpr hzE
  have hz0_le_N0 : Subgroup.zpowers z₀ ≤ triD4LineN0 k K := Subgroup.zpowers_le.mpr hz0N
  have hle : Subgroup.zpowers z₀ ≤ E ⊓ triD4LineN0 k K := le_inf hz0_le_E hz0_le_N0
  have hcardz0 : Nat.card (Subgroup.zpowers z₀) = 3 := by rw [Nat.card_zpowers, hz₀]
  have hdvd9 : Nat.card ↥(E ⊓ triD4LineN0 k K) ∣ 9 := by
    rw [← hEc]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdvd3 : 3 ∣ Nat.card ↥(E ⊓ triD4LineN0 k K) := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [hcardz0] at h
  have hne9 : Nat.card ↥(E ⊓ triD4LineN0 k K) ≠ 9 := by
    intro h9
    have hEq : E ⊓ triD4LineN0 k K = E := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      rw [h9, hEc]
    exact hEN (hEq ▸ inf_le_right)
  have hcardinf : Nat.card ↥(E ⊓ triD4LineN0 k K) = 3 := by
    have hdvd9' : Nat.card ↥(E ⊓ triD4LineN0 k K) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
      exact hdvd9
    obtain ⟨m, _, hpow⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd9'
    interval_cases m
    · rw [hpow] at hdvd3
      norm_num at hdvd3
    · simpa using hpow
    · exact absurd (hpow.trans (by norm_num)) hne9
  have hinf : E ⊓ triD4LineN0 k K = Subgroup.zpowers z₀ :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardinf, hcardz0])).symm
  have hnotN : ∀ e ∈ E, e ∉ Subgroup.zpowers z₀ → e ∉ triD4LineN0 k K := by
    intro e he hez heN
    exact hez (hinf ▸ ⟨he, heN⟩)
  obtain ⟨e₁, he₁E, he₁N⟩ := SetLike.not_le_iff_exists.mp hEN
  obtain ⟨gx, cx, hcx, rfl⟩ := triD4LineMk_surjective k K x
  obtain ⟨g₁, c₁, h₁, lam₁, he₁eq, _, hc₁, hlam₁3⟩ :=
    triD4Line_lambda_exists k K σ gx cx hcx e₁ (hx e₁ he₁E)
  have hpow : det (g₁ ^ 3) =
      Units.map (Algebra.norm k (S := K)) (c₁ ^ 3) := by rw [map_pow, h₁, map_pow]
  have h3eq : triD4LineMk k K (g₁ ^ 3) (c₁ ^ 3) hpow = 1 := by
    rw [← triD4LineMk_pow k K g₁ c₁ h₁ 3 hpow, ← he₁eq]
    exact hE.2 e₁ he₁E
  obtain ⟨ν, _, hcν⟩ := (triD4LineMk_eq_one_iff k K (g₁ ^ 3) (c₁ ^ 3) hpow).mp h3eq
  have hσ1 : σ (c₁ : K) = algebraMap k K (lam₁ : k) * (c₁ : K) := by
    simpa [Units.coe_map] using congrArg Units.val hc₁
  have hσ2 : (σ ^ 2) (c₁ : K) = algebraMap k K (lam₁ : k) ^ 2 * (c₁ : K) := by
    rw [pow_two, AlgEquiv.mul_apply, hσ1, map_mul, AlgEquiv.commutes, hσ1, pow_two]
    ring
  have hlam₁3k : (algebraMap k K (lam₁ : k)) ^ 3 = 1 := by
    have h : (lam₁ : k) ^ 3 = 1 := by
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hlam₁3
    rw [← map_pow, h, map_one]
  have hcνval : (c₁ : K) ^ 3 = algebraMap k K (ν : k) := by
    simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hcν
  have hnorm : algebraMap k K (Algebra.norm k (c₁ : K)) = algebraMap k K (ν : k) := by
    rw [triD4Line_algebraMap_norm k K hdeg σ hσ, hσ1, hσ2]
    rw [show (c₁ : K) * (algebraMap k K (lam₁ : k) * (c₁ : K)) *
        (algebraMap k K (lam₁ : k) ^ 2 * (c₁ : K)) =
        (algebraMap k K (lam₁ : k)) ^ 3 * (c₁ : K) ^ 3 by ring, hlam₁3k, one_mul, hcνval]
  have hNc : Units.map (Algebra.norm k (S := K)) c₁ = ν :=
    Units.ext ((algebraMap k K).injective hnorm)
  have hν_notcube : ν ∉ (powMonoidHom 3 : kˣ →* kˣ).range := by
    rintro ⟨τ, hτ⟩
    have hτ3 : τ ^ 3 = ν := by simpa using hτ
    apply he₁N
    rw [he₁eq]
    refine (triD4LineMk_mem_N0_iff k K hdeg g₁ c₁ h₁).2 ?_
    let τK : Kˣ := Units.map (algebraMap k K).toMonoidHom τ
    let u : Kˣ := c₁ * τK⁻¹
    have hτK3 : τK ^ 3 = Units.map (algebraMap k K).toMonoidHom ν := by
      dsimp [τK]
      rw [← map_pow, hτ3]
    have hu3 : u ^ 3 = 1 := by
      dsimp [u]
      rw [mul_pow, inv_pow, hcν, hτK3, mul_inv_cancel]
    have hu3val : (u : K) ^ 3 = 1 := by
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hu3
    obtain ⟨a, ha⟩ := triD4Line_exists_algebraMap_of_pow_three k K h3 (u : K) hu3val
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact u.ne_zero ha.symm
    have hmapμ0 : Units.map (algebraMap k K).toMonoidHom (Units.mk0 a ha0) = u := by
      apply Units.ext
      rw [Units.coe_map, Units.val_mk0]
      exact ha
    have hcu : c₁ = u * τK := by
      rw [show u = c₁ * τK⁻¹ from rfl, mul_assoc, inv_mul_cancel, mul_one]
    refine ⟨Units.mk0 a ha0 * τ, ?_⟩
    rw [map_mul, hmapμ0]
    exact hcu
  obtain ⟨a, j, hdet⟩ :=
    triD4Line_cube_decomp (kˣ) (triD4Line_cubeKer_card k h3) ν hν_notcube (det gx)
  let d : Kˣ := Units.map (algebraMap k K).toMonoidHom a * c₁ ^ j
  have hdN : Units.map (Algebra.norm k (S := K)) d = det gx := by
    show Units.map (Algebra.norm k (S := K))
      (Units.map (algebraMap k K).toMonoidHom a * c₁ ^ j) = det gx
    rw [map_mul, map_pow, triD4Line_norm_algebraMap_units k K hdeg a, hNc]
    exact hdet.symm
  let n : TriD4LineX k K := triD4LineMk k K gx d hdN.symm
  have hwdet_of : ∀ lam : kˣ, lam ^ 3 = 1 →
      det (scalar (Fin 3) lam) = Units.map (Algebra.norm k (S := K)) 1 := by
    intro lam hlam
    rw [det_scalar, Fintype.card_fin, hlam, map_one]
  refine ⟨n, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨g, c, h, lam, heq, hglam, hclam, hlam3⟩ :=
      triD4Line_lambda_exists k K σ gx cx hcx e (hx e he)
    have hwdet := hwdet_of lam hlam3
    have hwE : triD4LineMk k K (scalar (Fin 3) lam) 1 hwdet ∈ E := by
      have hmem := triD4Line_mk_scalar_mem_zpowers k K ζ hζ3 hζne1 hζdet lam hlam3 hwdet
      rw [hz0eq] at hmem
      exact Subgroup.zpowers_le.mpr hzE hmem
    have hconj := triD4Line_conj_eq k K gx d hdN.symm g c h lam hwdet hglam
    rw [heq] at he ⊢
    rw [hconj]
    exact E.mul_mem hwE he
  · intro e he hez
    obtain ⟨g, c, h, lam, heq, hglam, hclam, hlam3⟩ :=
      triD4Line_lambda_exists k K σ gx cx hcx e (hx e he)
    have hwdet := hwdet_of lam hlam3
    have hconj := triD4Line_conj_eq k K gx d hdN.symm g c h lam hwdet hglam
    rw [← heq] at hconj
    rw [hconj]
    intro hmem
    have heN : e ∉ triD4LineN0 k K := hnotN e he hez
    have hlamne : lam ≠ 1 := fun h1 =>
      heN (heq ▸ triD4Line_mem_N0_of_lambda_eq_one k K hdeg σ hσ g c h lam hclam h1)
    let hw : TriD4LineX k K := triD4LineMk k K (scalar (Fin 3) lam) 1 hwdet
    have hw_z0 : hw ∈ Subgroup.zpowers z₀ := by
      have hmem0 := triD4Line_mk_scalar_mem_zpowers k K ζ hζ3 hζne1 hζdet lam hlam3 hwdet
      rw [hz0eq] at hmem0
      exact hmem0
    have hw_e : hw ∈ Subgroup.zpowers e := by
      have hsplit : hw = (hw * e) * e⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [hsplit]
      exact (Subgroup.zpowers e).mul_mem hmem
        ((Subgroup.zpowers e).inv_mem (Subgroup.mem_zpowers e))
    have hwne : hw ≠ 1 := by
      intro hw1
      apply hlamne
      obtain ⟨ν', hsc, hmapν⟩ := (triD4LineMk_eq_one_iff k K
        (scalar (Fin 3) lam) 1 hwdet).1 hw1
      have hν1 : ν' = 1 := by
        have hv := congrArg Units.val hmapν
        have : algebraMap k K (ν' : k) = 1 := by simpa using hv.symm
        exact Units.ext ((algebraMap k K).injective (by simpa using this))
      have hlamν : lam = ν' := by
        refine Units.ext ((Matrix.scalar_inj (n := Fin 3)).mp ?_)
        simpa only [coe_scalar] using
          congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k)) hsc
      rw [hlamν, hν1]
    have he3 : orderOf e = 3 := by
      have hdvd : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one (hE.2 e he)
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) (fun he1 => hez (he1 ▸ Subgroup.one_mem _))
      · exact h3
    have hw3 : orderOf (hw) = 3 := by
      have hdvd : orderOf (hw) ∣ 3 := by
        have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z₀) hw_z0
        rwa [Nat.card_zpowers, hz₀] at h
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hwne
      · exact h3
    have hweq : Subgroup.zpowers (hw) = Subgroup.zpowers e := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw_e) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hw3, he3]
    have he_w : e ∈ Subgroup.zpowers (hw) := by
      rw [hweq]
      exact Subgroup.mem_zpowers e
    exact hez (Subgroup.zpowers_le.mpr hw_z0 he_w)
  · let σd : Kˣ := Units.mapEquiv σ.toRingEquiv.toMulEquiv d
    have hσd : det gx = Units.map (Algebra.norm k (S := K)) σd :=
      hdN.symm.trans (Units.ext (Algebra.norm_eq_of_algEquiv σ (d : K))).symm
    have hxstep : triD4LineMk k K gx cx hcx * triD4LineSigma k K σ n *
        (triD4LineMk k K gx cx hcx)⁻¹ = triD4LineMk k K gx σd hσd := by
      have hNd : Units.map (Algebra.norm k (S := K)) σd =
          Units.map (Algebra.norm k (S := K)) cx := hσd.symm.trans hcx
      have hbig : det (gx * gx * gx⁻¹) =
          Units.map (Algebra.norm k (S := K)) (cx * σd * cx⁻¹) := by
        simp only [map_mul, map_inv, hcx, hNd]
      dsimp only [n]
      rw [triD4LineSigma_mk k K σ gx d hdN.symm hσd,
        triD4LineMk_conj k K gx gx cx σd hcx hσd hbig]
      exact triD4LineMk_congr k K (by rw [mul_assoc, mul_inv_cancel, mul_one])
        (by rw [mul_assoc, mul_comm σd cx⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]) _ _
    have hquot : d * σd⁻¹ = ((Units.map (algebraMap k K).toMonoidHom lam₁) ^ j)⁻¹ := by
      have h : σd = d * (Units.map (algebraMap k K).toMonoidHom lam₁) ^ j := by
        have hsa : Units.mapEquiv σ.toRingEquiv.toMulEquiv
            (Units.map (algebraMap k K).toMonoidHom a) =
              Units.map (algebraMap k K).toMonoidHom a :=
          Units.ext (AlgEquiv.commutes σ (a : k))
        dsimp only [σd, d]
        rw [map_mul, map_pow, hsa, hc₁, mul_pow]
        ac_rfl
      dsimp only [d] at h ⊢
      rw [h, mul_inv_rev, ← mul_assoc, mul_comm (Units.map (algebraMap k K).toMonoidHom a * c₁ ^ j),
        mul_assoc, mul_inv_cancel, mul_one]
    have hB : det gx⁻¹ = Units.map (Algebra.norm k (S := K)) σd⁻¹ := by
      simp only [map_inv, hσd]
    have hA : det (gx * gx⁻¹) =
        Units.map (Algebra.norm k (S := K)) (d * σd⁻¹) := by rw [map_mul, map_mul, hdN, hB]
    have hnstep : n * (triD4LineMk k K gx cx hcx * triD4LineSigma k K σ n *
        (triD4LineMk k K gx cx hcx)⁻¹)⁻¹ =
          triD4LineMk k K (gx * gx⁻¹) (d * σd⁻¹) hA := by
      dsimp only [n]
      rw [hxstep, triD4LineMk_inv k K gx σd hσd hB,
        triD4LineMk_mul k K gx gx⁻¹ d σd⁻¹ hdN.symm hB hA]
    rw [hnstep]
    have hw : det
        (scalar (Fin 3) (lam₁ ^ j)) = Units.map (Algebra.norm k (S := K)) 1 := by
      rw [det_scalar, Fintype.card_fin, ← pow_mul, mul_comm j 3, pow_mul, hlam₁3, one_pow, map_one]
    have hfin : triD4LineMk k K (gx * gx⁻¹) (d * σd⁻¹) hA =
        triD4LineMk k K (scalar (Fin 3) (lam₁ ^ j)) 1 hw := by
      refine (triD4LineMk_eq_mk_iff k K (gx * gx⁻¹)
        (scalar (Fin 3) (lam₁ ^ j)) (d * σd⁻¹) 1 hA hw).2
        ⟨lam₁ ^ j, ?_, ?_⟩
      · rw [mul_inv_cancel, mul_one]
      · rw [hquot, ← map_pow, mul_inv_cancel]
    rw [hfin]
    have hmem := triD4Line_mk_scalar_mem_zpowers k K ζ hζ3 hζne1 hζdet (lam₁ ^ j)
      (by rw [← pow_mul, mul_comm j 3, pow_mul, hlam₁3, one_pow]) hw
    rw [hz0eq] at hmem
    exact Subgroup.zpowers_le.mpr hzE hmem

end CFSG.StandardType
