module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartOne.LIT.RankAbstract

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix Module

universe u v

variable {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def glAut (ι : Type v) [Fintype ι] [DecidableEq ι] (K : Type u) [Field K] :
    GL ι K →* ((ι → K) ≃ₗ[K] (ι → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem glAut_injective : Function.Injective (glAut ι K) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).injective.comp
    Matrix.GeneralLinearGroup.toLin.injective

theorem glAut_apply (g : GL ι K) (v : ι → K) :
    glAut ι K g v = (g : Matrix ι ι K) *ᵥ v := by
  simp [glAut]

theorem coe_glAut (g : GL ι K) :
    ((glAut ι K g : (ι → K) ≃ₗ[K] (ι → K)) : (ι → K) →ₗ[K] (ι → K)) =
      Matrix.toLin' (g : Matrix ι ι K) := by
  ext v
  simp [glAut]

theorem det_glAut (g : GL ι K) :
    LinearMap.det ((glAut ι K g : (ι → K) ≃ₗ[K] (ι → K)) : (ι → K) →ₗ[K] (ι → K)) =
      (g : Matrix ι ι K).det := by
  rw [coe_glAut, LinearMap.det_toLin']

theorem card_map_glAut (E : Subgroup (GL ι K)) : Nat.card (E.map (glAut ι K)) = Nat.card E :=
  Subgroup.card_map_of_injective glAut_injective

theorem map_glAut_comm {E : Subgroup (GL ι K)} (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) :
    ∀ g ∈ E.map (glAut ι K), ∀ h ∈ E.map (glAut ι K), g * h = h * g := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hcomm a ha b hb]

theorem map_glAut_exp {E : Subgroup (GL ι K)} {r : ℕ} (hexp : ∀ g ∈ E, g ^ r = 1) :
    ∀ g ∈ E.map (glAut ι K), g ^ r = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, hexp a ha, map_one]

theorem card_le_pow_card_gl {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    (E : Subgroup (GL ι K)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ r = 1) : Nat.card E ≤ r ^ Fintype.card ι := by
  have : Finite (E.map (glAut ι K)) :=
    Finite.of_equiv E (E.equivMapOfInjective (glAut ι K) glAut_injective).toEquiv
  have h := card_le_pow_finrank_sub hr hrK (E.map (glAut ι K)) (map_glAut_comm hcomm)
    (map_glAut_exp hexp)
  rwa [card_map_glAut, Module.finrank_fintype_fun_eq_card] at h

theorem card_le_sq_of_det_gl {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    (hι : Fintype.card ι = 3)
    (E : Subgroup (GL ι K)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ r = 1) (hdet : ∀ g ∈ E, (g : Matrix ι ι K).det = 1) :
    Nat.card E ≤ r ^ 2 := by
  have : Finite (E.map (glAut ι K)) :=
    Finite.of_equiv E (E.equivMapOfInjective (glAut ι K) glAut_injective).toEquiv
  have h := card_le_sq_of_det_eq_one hr hrK
    (by rw [Module.finrank_fintype_fun_eq_card, hι]) (E.map (glAut ι K)) (map_glAut_comm hcomm)
    (map_glAut_exp hexp) (by
      rintro _ ⟨a, ha, rfl⟩
      rw [det_glAut]
      exact hdet a ha)
  rwa [card_map_glAut] at h

theorem card_le_pow_half_of_form_gl {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    (J : Matrix ι ι K) (hJ : J.det ≠ 0) (hAlt : ∀ v : ι → K, v ⬝ᵥ (J *ᵥ v) = 0)
    (E : Subgroup (GL ι K)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ r = 1)
    (hpres : ∀ g ∈ E, (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J) :
    Nat.card E ≤ r ^ (Fintype.card ι / 2) := by
  have : Finite (E.map (glAut ι K)) :=
    Finite.of_equiv E (E.equivMapOfInjective (glAut ι K) glAut_injective).toEquiv
  have h := card_le_pow_half_of_alt hr hrK (Fintype.card ι) (ι → K)
    (by rw [Module.finrank_fintype_fun_eq_card]) (Matrix.toLinearMap₂' K J)
    (by
      intro v hv
      apply Matrix.eq_zero_of_vecMul_eq_zero hJ
      apply dotProduct_eq_zero_iff.mp
      intro w
      have := hv w
      rwa [Matrix.toLinearMap₂'_apply', Matrix.dotProduct_mulVec] at this)
    (by
      intro v
      rw [Matrix.toLinearMap₂'_apply']
      exact hAlt v)
    (E.map (glAut ι K)) (map_glAut_comm hcomm) (map_glAut_exp hexp)
    (by
      rintro _ ⟨a, ha, rfl⟩ u w
      have h1 := congrArg (fun M : Matrix ι ι K => u ⬝ᵥ (M *ᵥ w)) (hpres a ha)
      simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose] at h1
      rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply', glAut_apply, glAut_apply]
      simpa [Matrix.dotProduct_mulVec] using h1)
  rwa [card_map_glAut] at h

theorem pRank_le_of_card_gl [Finite K] {r k : ℕ} (hr : 1 < r) (H : Subgroup (GL ι K))
    (h : ∀ E : Subgroup (GL ι K), E ≤ H → (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) →
      (∀ g ∈ E, g ^ r = 1) → Nat.card E ≤ r ^ k) :
    CFSG.Open.pRank r (⊤ : Subgroup H) ≤ k := by
  refine CFSG.SectionRank.pRank_le hr fun E _ hE => ?_
  have hc : ∀ g ∈ E.map H.subtype, ∀ h ∈ E.map H.subtype, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun x : E => ((x : H) : GL ι K)) this
  have he : ∀ g ∈ E.map H.subtype, g ^ r = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]
  have hle : E.map H.subtype ≤ H := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have := h _ hle hc he
  rwa [Subgroup.card_map_of_injective H.subtype_injective] at this

theorem pRank_le_card_gl [Finite K] {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    (H : Subgroup (GL ι K)) : CFSG.Open.pRank r (⊤ : Subgroup H) ≤ Fintype.card ι :=
  pRank_le_of_card_gl hr.one_lt H fun E _ hc he => card_le_pow_card_gl hr hrK E hc he

theorem pRank_le_two_of_det_gl [Finite K] {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    (hι : Fintype.card ι = 3) (H : Subgroup (GL ι K))
    (hH : ∀ h ∈ H, (h : Matrix ι ι K).det = 1) :
    CFSG.Open.pRank r (⊤ : Subgroup H) ≤ 2 :=
  pRank_le_of_card_gl hr.one_lt H fun E hEH hc he =>
    card_le_sq_of_det_gl hr hrK hι E hc he fun g hg => hH g (hEH hg)

theorem pRank_le_half_of_form_gl [Finite K] {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    (J : Matrix ι ι K) (hJ : J.det ≠ 0) (hAlt : ∀ v : ι → K, v ⬝ᵥ (J *ᵥ v) = 0)
    (H : Subgroup (GL ι K)) (hH : ∀ h ∈ H, (h : Matrix ι ι K)ᵀ * J * (h : Matrix ι ι K) = J) :
    CFSG.Open.pRank r (⊤ : Subgroup H) ≤ Fintype.card ι / 2 :=
  pRank_le_of_card_gl hr.one_lt H fun E hEH hc he =>
    card_le_pow_half_of_form_gl hr hrK J hJ hAlt E hc he fun g hg => hH g (hEH hg)

theorem mem_closure_form {J : Matrix ι ι K} {S : Set (GL ι K)}
    (hS : ∀ g ∈ S, (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J) :
    ∀ h ∈ Subgroup.closure S, (h : Matrix ι ι K)ᵀ * J * (h : Matrix ι ι K) = J := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y _ _ hx hy =>
    calc ((x * y : GL ι K) : Matrix ι ι K)ᵀ * J * ((x * y : GL ι K) : Matrix ι ι K)
        = (y : Matrix ι ι K)ᵀ * ((x : Matrix ι ι K)ᵀ * J * (x : Matrix ι ι K)) *
            (y : Matrix ι ι K) := by
          simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [hx, hy]
  | inv x _ hx =>
    have h1 : (x : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((x⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * J * ((x⁻¹ : GL ι K) : Matrix ι ι K)
        = ((x⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((x : Matrix ι ι K)ᵀ * J * (x : Matrix ι ι K)) *
            ((x⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hx]
      _ = ((x : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K))ᵀ * J *
            ((x : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K)) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [h1]; simp

theorem mem_closure_det {S : Set (GL ι K)}
    (hS : ∀ g ∈ S, (g : Matrix ι ι K).det = 1) :
    ∀ h ∈ Subgroup.closure S, (h : Matrix ι ι K).det = 1 := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y _ _ hx hy => simp [Matrix.det_mul, hx, hy]
  | inv x _ hx =>
    have : (x : Matrix ι ι K).det * ((x⁻¹ : GL ι K) : Matrix ι ι K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rwa [hx, one_mul] at this

theorem natCast_ne_zero_of_charTwo {F : Type*} [Field F] [CharP F 2] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : (r : F) ≠ 0 := by
  intro h
  have h2 : 2 ∣ r := (CharP.cast_eq_zero_iff F 2 r).mp h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2).symm

theorem evenRank_le_two_of_pRank_le_two {G : Type} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 2) :
    CFSG.Assembly.evenRank G ≤ 2 := by
  apply csSup_le'
  rintro k ⟨p, H, hp, hp2, -, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt (le_top : H ≤ ⊤)).trans (h p hp hp2)

end CFSG.RankThree.PartOne.LIT
