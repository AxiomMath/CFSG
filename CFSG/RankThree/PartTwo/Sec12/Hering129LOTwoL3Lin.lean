module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3

open Module

section Lin

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

def linFixKer (E e : Module.End 𝕜 V) : Submodule 𝕜 V :=
  LinearMap.ker E ⊓ LinearMap.ker (e - (3 : 𝕜) • 1)

theorem mem_linFixKer {E e : Module.End 𝕜 V} {v : V} :
    v ∈ linFixKer E e ↔ E v = 0 ∧ e v = (3 : 𝕜) • v := by
  rw [linFixKer, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

theorem linFixKer_le_ker (h3 : (3 : 𝕜) ≠ 0) {E e e' : Module.End 𝕜 V} (h : e' * e = E) :
    linFixKer E e ≤ LinearMap.ker e' := by
  intro w hw
  rw [mem_linFixKer] at hw
  rw [LinearMap.mem_ker]
  have h3w : (3 : 𝕜) • e' w = 0 := by
    rw [← map_smul, ← hw.2, ← Module.End.mul_apply, h, hw.1]
  exact (smul_eq_zero.mp h3w).resolve_left h3

theorem ker_inf_linFixKer (h3 : (3 : 𝕜) ≠ 0) (E e : Module.End 𝕜 V) :
    LinearMap.ker e ⊓ linFixKer E e = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, LinearMap.mem_ker, mem_linFixKer] at hv
  have h3v : (3 : 𝕜) • v = 0 := by rw [← hv.2.2, hv.1]
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp h3v).resolve_left h3

theorem linFixKer_finrank_add_le [FiniteDimensional 𝕜 V] (h3 : (3 : 𝕜) ≠ 0)
    {E e₁ e₂ e₃ e₄ : Module.End 𝕜 V} (h21 : e₂ * e₁ = E) (h31 : e₃ * e₁ = E)
    (h32 : e₃ * e₂ = E) (h41 : e₄ * e₁ = E) (h42 : e₄ * e₂ = E) (h43 : e₄ * e₃ = E) :
    finrank 𝕜 (linFixKer E e₁) + finrank 𝕜 (linFixKer E e₂) + finrank 𝕜 (linFixKer E e₃) +
      finrank 𝕜 (linFixKer E e₄) ≤ finrank 𝕜 V := by
  have k2 : linFixKer E e₁ ⊓ linFixKer E e₂ = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_right _ (linFixKer_le_ker h3 h21)).trans
      (ker_inf_linFixKer h3 E e₂).le)
  have k3 : (linFixKer E e₁ ⊔ linFixKer E e₂) ⊓ linFixKer E e₃ = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_right _ (sup_le (linFixKer_le_ker h3 h31)
      (linFixKer_le_ker h3 h32))).trans (ker_inf_linFixKer h3 E e₃).le)
  have k4 : (linFixKer E e₁ ⊔ linFixKer E e₂ ⊔ linFixKer E e₃) ⊓ linFixKer E e₄ = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_right _ (sup_le (sup_le (linFixKer_le_ker h3 h41)
      (linFixKer_le_ker h3 h42)) (linFixKer_le_ker h3 h43))).trans
      (ker_inf_linFixKer h3 E e₄).le)
  have s2 := Submodule.finrank_sup_add_finrank_inf_eq (linFixKer E e₁) (linFixKer E e₂)
  have s3 := Submodule.finrank_sup_add_finrank_inf_eq
    (linFixKer E e₁ ⊔ linFixKer E e₂) (linFixKer E e₃)
  have s4 := Submodule.finrank_sup_add_finrank_inf_eq
    (linFixKer E e₁ ⊔ linFixKer E e₂ ⊔ linFixKer E e₃) (linFixKer E e₄)
  rw [k2, finrank_bot] at s2
  rw [k3, finrank_bot] at s3
  rw [k4, finrank_bot] at s4
  have := Submodule.finrank_le
    (linFixKer E e₁ ⊔ linFixKer E e₂ ⊔ linFixKer E e₃ ⊔ linFixKer E e₄)
  omega

theorem linFixKer_mapsTo {E e e' H : Module.End 𝕜 V} (hE : H * E = E * H)
    (he : H * e = e' * H) {v : V} (hv : v ∈ linFixKer E e) : H v ∈ linFixKer E e' := by
  rw [mem_linFixKer] at hv ⊢
  constructor
  · rw [← Module.End.mul_apply, ← hE, Module.End.mul_apply, hv.1, map_zero]
  · rw [← Module.End.mul_apply, ← he, Module.End.mul_apply, hv.2, map_smul]

theorem linFixKer_finrank_le [FiniteDimensional 𝕜 V] {E e e' H : Module.End 𝕜 V}
    (hH : Function.Injective H) (hE : H * E = E * H) (he : H * e = e' * H) :
    finrank 𝕜 (linFixKer E e) ≤ finrank 𝕜 (linFixKer E e') :=
  LinearMap.finrank_le_finrank_of_injective
    (f := H.restrict fun _ hv => linFixKer_mapsTo hE he hv)
    fun x y hxy => Subtype.ext (hH (congrArg Subtype.val hxy))

theorem apply_mem_linFixKer {E e : Module.End 𝕜 V} (hEe : E * e = e * E) (hee : e * e = 3 * e)
    {v : V} (hv : E v = 0) : e v ∈ linFixKer E e := by
  rw [mem_linFixKer]
  constructor
  · rw [← Module.End.mul_apply, hEe, Module.End.mul_apply, hv, map_zero]
  · rw [← Module.End.mul_apply, hee, Module.End.mul_apply, Module.End.ofNat_apply,
      ofNat_smul_eq_nsmul (R := 𝕜)]

theorem linFixKer_finrank_ne_one (h3 : (3 : 𝕜) ≠ 0) {E e R T : Module.End 𝕜 V}
    (hE : E = e * (1 + R + R ^ 2)) (hR : R ^ 3 = 1) (hRE : R * E = E * R)
    (hRe : R * e = e * R) (hTE : T * E = E * T) (hTe : T * e = e * T)
    (hTR : T * R = R ^ 2 * T) (hT : Function.Injective T) :
    finrank 𝕜 (linFixKer E e) ≠ 1 := by
  intro h1
  obtain ⟨u, hu0, hu⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨μ, hμ⟩ := hu ⟨R u, linFixKer_mapsTo hRE hRe u.2⟩
  obtain ⟨ν, hν⟩ := hu ⟨T u, linFixKer_mapsTo hTE hTe u.2⟩
  have hRu : R u = μ • (u : V) := (congrArg Subtype.val hμ).symm
  have hTu : T u = ν • (u : V) := (congrArg Subtype.val hν).symm
  have hu0' : (u : V) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hmem := mem_linFixKer.mp u.2
  have key : μ * ν = ν * (μ * μ) := by
    have h := LinearMap.congr_fun hTR u
    simp only [Module.End.mul_apply, pow_two, hRu, hTu, map_smul, smul_smul] at h
    exact smul_left_injective 𝕜 hu0' h
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_smul, ← map_zero T] at hTu
    exact hu0' (hT hTu)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hRu
    apply hu0'
    calc (u : V) = (R ^ 3) u := by rw [hR, Module.End.one_apply]
      _ = 0 := by rw [pow_succ, Module.End.mul_apply, hRu, map_zero]
  have hμ1 : μ = 1 := by
    have h1 : ν * μ = ν * (μ * μ) := by rw [← key, mul_comm]
    exact mul_left_cancel₀ hμ0 ((mul_left_cancel₀ hν0 h1).symm.trans (mul_one μ).symm)
  have hRu1 : R u = u := by rw [hRu, hμ1, one_smul]
  have h3u : (1 + R + R ^ 2 : Module.End 𝕜 V) u = (3 : 𝕜) • (u : V) := by
    rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, pow_two,
      Module.End.mul_apply, hRu1, hRu1]
    module
  have h9 : ((3 : 𝕜) * 3) • (u : V) = 0 := by
    calc ((3 : 𝕜) * 3) • (u : V) = E u := by
          rw [LinearMap.congr_fun hE, Module.End.mul_apply, h3u, map_smul, hmem.2, smul_smul]
      _ = 0 := hmem.1
  exact hu0' ((smul_eq_zero.mp h9).resolve_left (mul_ne_zero h3 h3))

theorem lin_ring {A : Type*} [CommRing A] {p r e₁ e₂ e₃ e₄ E : A} (hp : p ^ 3 = 1)
    (hr : r ^ 3 = 1) (he₁ : e₁ = 1 + p + p ^ 2) (he₂ : e₂ = 1 + r + r ^ 2)
    (he₃ : e₃ = 1 + p * r + (p * r) ^ 2) (he₄ : e₄ = 1 + p * r ^ 2 + (p * r ^ 2) ^ 2)
    (hE : E = e₁ * e₂) :
    e₂ * e₁ = E ∧ e₃ * e₁ = E ∧ e₃ * e₂ = E ∧ e₄ * e₁ = E ∧ e₄ * e₂ = E ∧ e₄ * e₃ = E ∧
      e₃ * e₄ = E ∧ e₁ * e₁ = 3 * e₁ ∧ e₂ * e₂ = 3 * e₂ ∧ e₃ * e₃ = 3 * e₃ ∧
      e₄ * e₄ = 3 * e₄ ∧ e₁ + e₂ + e₃ + e₄ = E + 3 ∧ p * E = E ∧ r * E = E := by
  subst he₁ he₂ he₃ he₄ hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

theorem lin_ring_conj {A : Type*} [CommRing A] {p r : A} (hp : p ^ 3 = 1) (hr : r ^ 3 = 1) :
    1 + r ^ 2 + (r ^ 2) ^ 2 = 1 + r + r ^ 2 ∧
      1 + p ^ 2 * r ^ 2 + (p ^ 2 * r ^ 2) ^ 2 = 1 + p * r + (p * r) ^ 2 ∧
      1 + p ^ 2 * r + (p ^ 2 * r) ^ 2 = 1 + p * r ^ 2 + (p * r ^ 2) ^ 2 ∧
      p ^ 2 * r ^ 2 * (p ^ 2 * r) = p ∧ p ^ 2 * r ^ 2 * (p ^ 2 * r) ^ 2 = r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

theorem lin_ringHom_eq_one_of_finrank_lt_eight [FiniteDimensional 𝕜 V] {A : Type*} [CommRing A]
    (φ : A →+* Module.End 𝕜 V) (h3 : (3 : 𝕜) ≠ 0) {p r : A} (hp : p ^ 3 = 1)
    (hr : r ^ 3 = 1) {H₁ H₂ : Module.End 𝕜 V} (hH₁ : Function.Injective H₁)
    (hH₂ : Function.Injective H₂) (s11 : H₁ * φ p = φ (r ^ 2) * H₁)
    (s12 : H₁ * φ r = φ p * H₁) (s21 : H₂ * φ p = φ (p ^ 2 * r ^ 2) * H₂)
    (s22 : H₂ * φ r = φ (p ^ 2 * r) * H₂) (hdim : finrank 𝕜 V < 8) : φ p = 1 ∧ φ r = 1 := by
  obtain ⟨g₁, g₂, g₃, g₄, g₅⟩ := lin_ring_conj hp hr
  have tri : ∀ {H : Module.End 𝕜 V} {x y : A}, H * φ x = φ y * H →
      H * φ (1 + x + x ^ 2) = φ (1 + y + y ^ 2) * H := by
    intro H x y h
    rw [map_add, map_add, map_one, map_pow, map_add, map_add, map_one, map_pow]
    exact ((SemiconjBy.one_right H).add_right h).add_right (SemiconjBy.pow_right h 2)
  have s23 : H₂ * φ (p * r) = φ p * H₂ := by
    calc H₂ * φ (p * r) = H₂ * (φ p * φ r) := by rw [map_mul]
      _ = φ (p ^ 2 * r ^ 2) * φ (p ^ 2 * r) * H₂ := SemiconjBy.mul_right s21 s22
      _ = φ p * H₂ := by rw [← map_mul, g₄]
  have s24 : H₂ * φ (p * r ^ 2) = φ r * H₂ := by
    calc H₂ * φ (p * r ^ 2) = H₂ * (φ p * φ r ^ 2) := by rw [map_mul, map_pow]
      _ = φ (p ^ 2 * r ^ 2) * φ (p ^ 2 * r) ^ 2 * H₂ :=
          SemiconjBy.mul_right s21 (SemiconjBy.pow_right s22 2)
      _ = φ r * H₂ := by rw [← map_pow, ← map_mul, g₅]
  obtain ⟨e₁, he₁⟩ : ∃ e : A, e = 1 + p + p ^ 2 := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e : A, e = 1 + r + r ^ 2 := ⟨_, rfl⟩
  obtain ⟨e₃, he₃⟩ : ∃ e : A, e = 1 + p * r + (p * r) ^ 2 := ⟨_, rfl⟩
  obtain ⟨e₄, he₄⟩ : ∃ e : A, e = 1 + p * r ^ 2 + (p * r ^ 2) ^ 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ e : A, e = e₁ * e₂ := ⟨_, rfl⟩
  obtain ⟨i21, i31, i32, i41, i42, i43, i34, i11, i22, i33, i44, isum, ipE, irE⟩ :=
    lin_ring hp hr he₁ he₂ he₃ he₄ hE
  have c11 : H₁ * φ e₁ = φ e₂ * H₁ := by rw [he₁, tri s11, he₂, g₁]
  have c12 : H₁ * φ e₂ = φ e₁ * H₁ := by rw [he₁, he₂, tri s12]
  have c21 : H₂ * φ e₁ = φ e₃ * H₂ := by rw [he₁, tri s21, he₃, g₂]
  have c23 : H₂ * φ e₃ = φ e₁ * H₂ := by rw [he₁, he₃, tri s23]
  have c22 : H₂ * φ e₂ = φ e₄ * H₂ := by rw [he₂, tri s22, he₄, g₃]
  have c24 : H₂ * φ e₄ = φ e₂ * H₂ := by rw [he₂, he₄, tri s24]
  have m : ∀ {x y z : A}, x * y = z → φ x * φ y = φ z := fun h => by rw [← map_mul, h]
  have mc : ∀ x y : A, φ x * φ y = φ y * φ x := fun x y => by
    rw [← map_mul, ← map_mul, mul_comm]
  have c1E : H₁ * φ E = φ E * H₁ := by
    have h := SemiconjBy.mul_right c11 c12
    rwa [m i21, m hE.symm] at h
  have c2E : H₂ * φ E = φ E * H₂ := by
    have h := SemiconjBy.mul_right c21 c22
    rwa [m i34, m hE.symm] at h
  have hsum := linFixKer_finrank_add_le h3 (m i21) (m i31) (m i32) (m i41) (m i42) (m i43)
  have d12 := linFixKer_finrank_le hH₁ c1E c11
  have d21 := linFixKer_finrank_le hH₁ c1E c12
  have d13 := linFixKer_finrank_le hH₂ c2E c21
  have d31 := linFixKer_finrank_le hH₂ c2E c23
  have d24 := linFixKer_finrank_le hH₂ c2E c22
  have d42 := linFixKer_finrank_le hH₂ c2E c24
  have hd1 : finrank 𝕜 (linFixKer (φ E) (φ e₁)) ≠ 1 :=
    linFixKer_finrank_ne_one h3 (R := φ r) (T := H₁ * H₁)
      (by rw [hE, map_mul, he₂, map_add, map_add, map_one, map_pow])
      (by rw [← map_pow, hr, map_one]) (mc r E) (mc r e₁)
      (SemiconjBy.mul_left c1E c1E) (SemiconjBy.mul_left c12 c11)
      (by rw [← map_pow]; exact SemiconjBy.mul_left s11 s12) (hH₁.comp hH₁)
  have hW : ∀ {e : A}, finrank 𝕜 (linFixKer (φ E) (φ e)) = 0 → e * e = 3 * e →
      ∀ v, φ E v = 0 → φ e v = 0 := by
    intro e h0 hee v hv
    have h := apply_mem_linFixKer (mc E e) (by rw [m hee, map_mul, map_ofNat]) hv
    rwa [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot] at h
  have hker : ∀ v, φ E v = 0 → v = 0 := by
    intro v hv
    have hs := LinearMap.congr_fun (show φ e₁ + φ e₂ + φ e₃ + φ e₄ = φ E + 3 by
      rw [← map_add, ← map_add, ← map_add, isum, map_add, map_ofNat]) v
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply,
      hW (by omega) i11 v hv, hW (by omega) i22 v hv, hW (by omega) i33 v hv,
      hW (by omega) i44 v hv, hv, Module.End.ofNat_apply, ← ofNat_smul_eq_nsmul (R := 𝕜)] at hs
    simp only [add_zero, zero_add] at hs
    exact (smul_eq_zero.mp hs.symm).resolve_left h3
  have hsurj : Function.Surjective (φ E) :=
    LinearMap.injective_iff_surjective.mp ((injective_iff_map_eq_zero (φ E)).mpr hker)
  have fix : ∀ {x : A}, x * E = E → φ x = 1 := by
    intro x hx
    ext v
    obtain ⟨w, rfl⟩ := hsurj v
    rw [← Module.End.mul_apply, m hx, Module.End.one_apply]
  exact ⟨fix ipE, fix irE⟩

open scoped IsMulCommutative in
theorem lin_eq_one_of_finrank_lt_eight [FiniteDimensional 𝕜 V] (h3 : (3 : 𝕜) ≠ 0)
    {P R H₁ H₂ : Module.End 𝕜 V} (hP : P ^ 3 = 1) (hR : R ^ 3 = 1) (hPR : P * R = R * P)
    (hH₁ : Function.Injective H₁) (hH₂ : Function.Injective H₂)
    (s11 : H₁ * P = R ^ 2 * H₁) (s12 : H₁ * R = P * H₁)
    (s21 : H₂ * P = P ^ 2 * R ^ 2 * H₂) (s22 : H₂ * R = P ^ 2 * R * H₂)
    (hdim : finrank 𝕜 V < 8) : P = 1 ∧ R = 1 := by
  have hcomm : ({P, R} : Set (Module.End 𝕜 V)).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hPR
    · exact hPR.symm
    · exact Commute.refl _
  haveI := Algebra.isMulCommutative_adjoin 𝕜 hcomm
  let S := Algebra.adjoin 𝕜 ({P, R} : Set (Module.End 𝕜 V))
  let p : S := ⟨P, Algebra.subset_adjoin (Set.mem_insert P {R})⟩
  let r : S := ⟨R, Algebra.subset_adjoin (Set.mem_insert_of_mem P rfl)⟩
  have hp : p ^ 3 = 1 := Subtype.val_injective (by simpa using hP)
  have hr : r ^ 3 = 1 := Subtype.val_injective (by simpa using hR)
  exact lin_ringHom_eq_one_of_finrank_lt_eight (S.val : S →+* Module.End 𝕜 V) h3 hp hr hH₁ hH₂
    (by simpa using s11) (by simpa using s12) (by simpa using s21) (by simpa using s22) hdim

end Lin

theorem rho_eq_one_of_finrank_lt_eight {𝕜 V G : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] [Group G] (h3 : (3 : 𝕜) ≠ 0) (ρ : G →* Module.End 𝕜 V)
    {b₁ b₂ h₁ h₂ : G} (hb₁ : b₁ ^ 3 = 1) (hb₂ : b₂ ^ 3 = 1) (hc : b₁ * b₂ = b₂ * b₁)
    (r11 : h₁ * b₁ * h₁⁻¹ = b₂⁻¹) (r12 : h₁ * b₂ * h₁⁻¹ = b₁)
    (r21 : h₂ * b₁ * h₂⁻¹ = b₁⁻¹ * b₂⁻¹) (r22 : h₂ * b₂ * h₂⁻¹ = b₁⁻¹ * b₂)
    (hdim : Module.finrank 𝕜 V < 8) : ρ b₁ = 1 ∧ ρ b₂ = 1 := by
  have hinv : ∀ {b : G}, b ^ 3 = 1 → b⁻¹ = b ^ 2 := fun hb =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hb])
  have conj : ∀ {h b c : G}, h * b * h⁻¹ = c → ρ h * ρ b = ρ c * ρ h := by
    intro h b c hbc
    rw [← map_mul, ← map_mul, ← hbc, inv_mul_cancel_right]
  have inj : ∀ h : G, Function.Injective (ρ h) := fun h =>
    Function.LeftInverse.injective (g := ρ h⁻¹) fun v => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine lin_eq_one_of_finrank_lt_eight h3 (H₁ := ρ h₁) (H₂ := ρ h₂) ?_ ?_ ?_ (inj h₁) (inj h₂)
    ?_ ?_ ?_ ?_ hdim
  · rw [← map_pow, hb₁, map_one]
  · rw [← map_pow, hb₂, map_one]
  · rw [← map_mul, hc, map_mul]
  · rw [conj r11, hinv hb₂, map_pow]
  · exact conj r12
  · rw [conj r21, hinv hb₁, hinv hb₂, map_mul, map_pow, map_pow]
  · rw [conj r22, hinv hb₁, map_mul, map_pow]

end CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3
