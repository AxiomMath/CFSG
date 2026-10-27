module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.InspPS

open Matrix
open scoped MatrixGroups commutatorElement

variable {K : Type*} [Field K]

theorem orderOf_mk_eq_three {x : SL(2, K)} (h3 : x ^ 3 ∈ Subgroup.center SL(2, K))
    (h1 : x ∉ Subgroup.center SL(2, K)) :
    orderOf (QuotientGroup.mk x : PSL(2, K)) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 h3
  · intro h; exact h1 ((QuotientGroup.eq_one_iff _).1 h)

theorem not_mem_center_of_entry10 {x : SL(2, K)} (h : (x : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    x ∉ Subgroup.center SL(2, K) := by
  intro hx
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  apply h
  rw [← hr]
  simp [Matrix.scalar_apply]

theorem not_mem_center_of_entry01 {x : SL(2, K)} (h : (x : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0) :
    x ∉ Subgroup.center SL(2, K) := by
  intro hx
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  apply h
  rw [← hr]
  simp [Matrix.scalar_apply]

theorem cube_mem_center_of_trace_one (x : SL(2, K))
    (htr : (x : Matrix (Fin 2) (Fin 2) K) 0 0 + (x : Matrix (Fin 2) (Fin 2) K) 1 1 = 1) :
    x ^ 3 ∈ Subgroup.center SL(2, K) := by
  have hdet : (x : Matrix (Fin 2) (Fin 2) K).det = 1 := x.2
  rw [Matrix.det_fin_two] at hdet
  have hsq : (x : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) =
      (x : Matrix (Fin 2) (Fin 2) K) - 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hsq,
    mul_sub, mul_one, hsq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

theorem orderOf_mk_of_odd {x : SL(2, K)} (hx : Odd (orderOf x)) :
    orderOf (QuotientGroup.mk x : PSL(2, K)) = orderOf x := by
  have hcen : ∀ z ∈ Subgroup.center SL(2, K), z ^ 2 = 1 := by
    intro z hz
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
    rw [Fintype.card_fin] at hr
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr]
    simp
  apply Nat.dvd_antisymm
  · exact orderOf_map_dvd (QuotientGroup.mk' _) x
  · set n := orderOf (QuotientGroup.mk x : PSL(2, K))
    have h1 : x ^ n ∈ Subgroup.center SL(2, K) := by
      have : (QuotientGroup.mk (x ^ n) : PSL(2, K)) = 1 := by
        rw [QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _
      exact (QuotientGroup.eq_one_iff _).1 this
    have h2 : x ^ (n * 2) = 1 := by rw [pow_mul]; exact hcen _ h1
    have h3 : orderOf x ∣ n * 2 := orderOf_dvd_of_pow_eq_one h2
    exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_two_right.2 hx) h3

theorem cube_eq_one_of_trace (x : SL(2, K))
    (htr : (x : Matrix (Fin 2) (Fin 2) K) 0 0 + (x : Matrix (Fin 2) (Fin 2) K) 1 1 = -1) :
    x ^ 3 = 1 := by
  have hdet : (x : Matrix (Fin 2) (Fin 2) K).det = 1 := x.2
  rw [Matrix.det_fin_two] at hdet
  have hsq : (x : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) =
      -(x : Matrix (Fin 2) (Fin 2) K) - 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  apply Subtype.ext
  rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hsq,
    mul_sub, mul_neg, mul_one, hsq]
  simp

noncomputable def unipHom (K : Type*) [Field K] : Multiplicative K →* SL(2, K) where
  toFun c := SpecialLinearGroup.transvection zero_ne_one c.toAdd
  map_one' := by simp
  map_mul' c d := by rw [toAdd_mul, SpecialLinearGroup.transvection_add]

theorem unipHom_pow_p {p : ℕ} [CharP K p] (c : K) :
    (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) ^ p = 1 := by
  have h := congrArg (unipHom K) (show (Multiplicative.ofAdd c) ^ p = 1 by
    rw [← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero])
  rw [map_pow, map_one] at h
  exact h

theorem exists_pair_unip {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) :
    ∃ x y : PSL(2, K), orderOf x = 3 ∧ orderOf y = 3 ∧ orderOf (x * y) = p := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1
      ((CharP.cast_eq_zero_iff K p 2).1 h'))
  let a : SL(2, K) := ⟨!![0, 1 / 2; -2, -1], by
    rw [Matrix.det_fin_two_of]; field_simp; ring⟩
  let b : SL(2, K) := ⟨!![-1, -3 / 2; 2, 2], by
    rw [Matrix.det_fin_two_of]; field_simp; ring⟩
  have hab : a * b = SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : K) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, b, Matrix.mul_apply, Fin.sum_univ_two, SpecialLinearGroup.transvection_coe] <;>
      field_simp <;> ring
  have ha3 : a ^ 3 = 1 := cube_eq_one_of_trace a (by simp [a])
  have hb3 : b ^ 3 ∈ Subgroup.center SL(2, K) :=
    cube_mem_center_of_trace_one b (by simp [b]; norm_num)
  have ha_nc : a ∉ Subgroup.center SL(2, K) :=
    not_mem_center_of_entry10 (by simpa [a] using h2)
  have hb_nc : b ∉ Subgroup.center SL(2, K) :=
    not_mem_center_of_entry10 (by simpa [b] using h2)
  refine ⟨QuotientGroup.mk a, QuotientGroup.mk b,
    orderOf_mk_eq_three (by rw [ha3]; exact Subgroup.one_mem _) ha_nc,
    orderOf_mk_eq_three hb3 hb_nc, ?_⟩
  rw [← QuotientGroup.mk_mul, hab]
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, unipHom_pow_p (p := p)]
    exact Subgroup.one_mem _
  · intro h
    exact one_ne_zero ((SpecialLinearGroup.transvection_mem_center_iff _ (1 : K)).1
      ((QuotientGroup.eq_one_iff _).1 h))

noncomputable def diag2Hom (K : Type*) [Field K] : Kˣ →* SL(2, K) where
  toFun u := SpecialLinearGroup.diag2 (u : K) u.ne_zero
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.diag2_coe']
  map_mul' u v := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.diag2_coe', Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem coe_diag2Hom (u : Kˣ) :
    (diag2Hom K u : Matrix (Fin 2) (Fin 2) K) = !![(u : K), 0; 0, (u : K)⁻¹] :=
  SpecialLinearGroup.diag2_coe' u.ne_zero

theorem diag2Hom_injective : Function.Injective (diag2Hom K) := by
  intro u v h
  have h00 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa [diag2Hom, SpecialLinearGroup.diag2_coe'] using Units.ext h00

theorem exists_pair_torus (l : Kˣ) (hodd : Odd (orderOf l)) (hne : l ≠ 1) :
    ∃ x y : PSL(2, K), orderOf x = 3 ∧ orderOf y = 3 ∧ orderOf (x * y) = orderOf l := by
  have hl1 : (1 : K) + l ≠ 0 := by
    intro h
    have hl : (l : K) = -1 := eq_neg_of_add_eq_zero_right h
    have hsq : l ^ 2 = 1 := by
      apply Units.ext
      simp [hl]
    have hd : orderOf l ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have h1 : orderOf l = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    exact hne (orderOf_eq_one_iff.1 h1)
  have hL0 : (l : K) ≠ 0 := l.ne_zero
  obtain ⟨α, δ, γ, hdet, htr, htrb⟩ : ∃ α δ γ : K, α * δ - γ = 1 ∧ α + δ = -1 ∧
      δ * l + α * (l : K)⁻¹ = -1 := by
    refine ⟨-(l : K) / (1 + l), -1 / (1 + (l : K)), -(l : K) / (1 + l) * (-1 / (1 + (l : K))) - 1,
      by ring, ?_, ?_⟩
    · field_simp; ring
    · field_simp; ring
  let a : SL(2, K) := ⟨!![α, 1; γ, δ], by rw [Matrix.det_fin_two_of]; linear_combination hdet⟩
  let b : SL(2, K) := ⟨!![δ * l, -(l : K)⁻¹; -γ * l, α * (l : K)⁻¹], by
    rw [Matrix.det_fin_two_of]; field_simp; linear_combination hdet⟩
  let z : SL(2, K) := diag2Hom K l
  have hab : a * b = z := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, b, z, coe_diag2Hom, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination (l : K) * hdet | linear_combination (l : K)⁻¹ * hdet
  have hatr : (a : Matrix (Fin 2) (Fin 2) K) 0 0 + (a : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 := by
    simpa [a] using htr
  have hbtr : (b : Matrix (Fin 2) (Fin 2) K) 0 0 + (b : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 := by
    simpa [b] using htrb
  have ha_nc : a ∉ Subgroup.center SL(2, K) := not_mem_center_of_entry01 (by simp [a])
  have hb_nc : b ∉ Subgroup.center SL(2, K) :=
    not_mem_center_of_entry01 (by simpa [b] using hL0)
  have hz : orderOf z = orderOf l := orderOf_injective _ (diag2Hom_injective) l
  refine ⟨QuotientGroup.mk a, QuotientGroup.mk b,
    orderOf_mk_eq_three (by rw [cube_eq_one_of_trace a hatr]; exact Subgroup.one_mem _) ha_nc,
    orderOf_mk_eq_three (by rw [cube_eq_one_of_trace b hbtr]; exact Subgroup.one_mem _) hb_nc, ?_⟩
  rw [← QuotientGroup.mk_mul, hab, orderOf_mk_of_odd (hz ▸ hodd), hz]

theorem mul_pow_p {p : ℕ} [CharP K p] (c : Multiplicative K) : c ^ p = 1 := by
  rw [← ofAdd_toAdd c, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero]

noncomputable def rootHom (K : Type*) [Field K] : Multiplicative K →* PSL(2, K) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, K))).comp (unipHom K)

noncomputable def rootGroup (K : Type*) [Field K] : Subgroup PSL(2, K) := (rootHom K).range

theorem rootHom_injective : Function.Injective (rootHom K) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h : unipHom K c ∈ Subgroup.center SL(2, K) := by
    have := hc
    simp only [rootHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  have h0 := (SpecialLinearGroup.transvection_mem_center_iff
    (zero_ne_one : (0 : Fin 2) ≠ 1) c.toAdd).1 h
  exact toAdd_eq_zero.1 h0

theorem rootGroup_isElemAbelian {p : ℕ} [Fact p.Prime] [CharP K p] :
    CFSG.Open.IsElemAbelian p (rootGroup K) := by
  refine ⟨by unfold rootGroup; infer_instance, ?_⟩
  rintro _ ⟨c, rfl⟩
  rw [← map_pow, mul_pow_p, map_one]

theorem card_rootGroup [Finite K] : Nat.card (rootGroup K) = Nat.card K := by
  have h := Nat.card_congr (MonoidHom.ofInjective (rootHom_injective (K := K))).toEquiv
  rw [rootGroup]
  rw [← h]
  exact Nat.card_congr Multiplicative.toAdd

theorem coe_transvection (c : K) :
    (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c :
      Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem conj_transvection (u : Kˣ) (c : K) :
    diag2Hom K u * SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c *
        (diag2Hom K u)⁻¹ =
      SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) ((u : K) ^ 2 * c) := by
  rw [← map_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diag2Hom,
    coe_diag2Hom, coe_transvection, coe_transvection, Matrix.mul_fin_two, Matrix.mul_fin_two]
  have hu : (u : K) ≠ 0 := u.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem conj_rootHom (u : Kˣ) (c : K) :
    (QuotientGroup.mk (diag2Hom K u) : PSL(2, K)) * rootHom K (Multiplicative.ofAdd c) *
      (QuotientGroup.mk (diag2Hom K u))⁻¹ =
      rootHom K (Multiplicative.ofAdd ((u : K) ^ 2 * c)) := by
  simp only [rootHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, unipHom, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_ofAdd]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, conj_transvection]

theorem conj_mem_rootGroup (u : Kˣ) {y : PSL(2, K)} (hy : y ∈ rootGroup K) :
    QuotientGroup.mk (diag2Hom K u) * y * (QuotientGroup.mk (diag2Hom K u))⁻¹ ∈ rootGroup K := by
  obtain ⟨c, rfl⟩ := hy
  rw [← ofAdd_toAdd c, conj_rootHom]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

theorem exists_borel_data [Finite K] {t : Kˣ} (ht : orderOf t = 3) :
    ∃ D : Subgroup PSL(2, K), Nat.card D = 3 ∧
      D ≤ Subgroup.normalizer (rootGroup K : Set PSL(2, K)) ∧ ⁅D, rootGroup K⁆ ≠ ⊥ := by
  set z : PSL(2, K) := QuotientGroup.mk (diag2Hom K t) with hzdef
  have hz3 : orderOf z = 3 := by
    have h1 : orderOf (diag2Hom K t) = 3 := (orderOf_injective _ diag2Hom_injective t).trans ht
    rw [hzdef, orderOf_mk_of_odd (by rw [h1]; decide), h1]
  refine ⟨Subgroup.zpowers z, by rw [Nat.card_zpowers, hz3], ?_, ?_⟩
  · rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_rootGroup t hy, fun hy => ?_⟩
    have h := conj_mem_rootGroup t⁻¹ hy
    have hinv : (QuotientGroup.mk (diag2Hom K t⁻¹) : PSL(2, K)) = z⁻¹ := by
      rw [hzdef, map_inv, QuotientGroup.mk_inv]
    rw [hinv, inv_inv] at h
    simpa [mul_assoc] using h
  · intro hbot
    have hmem : ⁅z, rootHom K (Multiplicative.ofAdd 1)⁆ ∈
        ⁅Subgroup.zpowers z, rootGroup K⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers z)
        (MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd 1, rfl⟩)
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
    have h := conj_rootHom t 1
    rw [← hzdef] at h
    rw [h] at hmem
    have h2 : rootHom K (Multiplicative.ofAdd ((t : K) ^ 2 * 1)) =
        rootHom K (Multiplicative.ofAdd 1) := mul_inv_eq_one.1 hmem
    have h3 : (t : K) ^ 2 * 1 = 1 := by
      have := rootHom_injective h2
      simpa using this
    have h4 : t ^ 2 = 1 := Units.ext (by simpa using h3)
    have h5 : 3 ∣ 2 := ht ▸ orderOf_dvd_of_pow_eq_one h4
    omega

end CFSG.LocalAnalysis.UniquenessCase.UCK.InspPS
