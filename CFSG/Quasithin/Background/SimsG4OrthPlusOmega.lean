module

public import CFSG.Quasithin.Background.SimsG4OrthPlusModel
import CFSG.Timmesfeld.RankOne.SL2

public section

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.Quasithin.G11.P3Ortho.Om4

namespace CFSG.Quasithin.SimsG4.OrthPlus

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
  (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)

theorem rhoW_conj_inl
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    rhoW ψ z * rhoW ψ (x, 1) * (rhoW ψ z)⁻¹ = rhoW ψ (z.1 * x * z.1⁻¹, 1) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem rhoW_conj_inr
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (y : Matrix.SpecialLinearGroup (Fin 2) K) :
    rhoW ψ z * rhoW ψ (1, y) * (rhoW ψ z)⁻¹ = rhoW ψ (1, z.2 * y * z.2⁻¹) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

variable {Q : QuadraticForm K W} (hψ : ∀ w, Q w = (ψ w).det)
include hψ

theorem range_rhoW_le : (rhoW ψ).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro _ ⟨z, rfl⟩
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (rhoW_isometry ψ hψ z)

theorem Q_symm_one : Q (ψ.symm 1) = 1 := by
  rw [hψ, LinearEquiv.apply_symm_apply, Matrix.det_one]

variable [CharP K 2]

theorem reflK_conj_inl {r : W} {s : Matrix.SpecialLinearGroup (Fin 2) K} (hr : ψ r = s)
    (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    reflK Q r * rhoW ψ (x, 1) * reflK Q r = rhoW ψ (1, s⁻¹ * x * s) := by
  rw [reflK_mul_rhoW_mul_reflK ψ hψ hr]
  congr 1
  ext <;> simp

theorem reflK_conj_inr {r : W} {s : Matrix.SpecialLinearGroup (Fin 2) K} (hr : ψ r = s)
    (y : Matrix.SpecialLinearGroup (Fin 2) K) :
    reflK Q r * rhoW ψ (1, y) * reflK Q r = rhoW ψ (s * y * s⁻¹, 1) := by
  rw [reflK_mul_rhoW_mul_reflK ψ hψ hr]
  congr 1
  ext <;> simp

variable [Finite K]

theorem index_range_rhoW :
    ((rhoW ψ).range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2 := by
  have hr := Q_symm_one ψ hψ
  have ht : reflK Q (ψ.symm 1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (reflK_isometry Q hr)
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨_, ht⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases mem_range_rhoW_or_mul_reflK ψ hψ hr (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp b.2)
    with h | h
  · refine Or.inr ⟨h, fun h' => ?_⟩
    have h2 := (rhoW ψ).range.mul_mem ((rhoW ψ).range.inv_mem h) h'
    rw [inv_mul_cancel_left] at h2
    exact reflK_not_mem_range_rhoW ψ hψ hr h2
  · refine Or.inl ⟨h, fun h' => ?_⟩
    have h2 := (rhoW ψ).range.mul_mem ((rhoW ψ).range.inv_mem h') h
    rw [inv_mul_cancel_left] at h2
    exact reflK_not_mem_range_rhoW ψ hψ hr h2

theorem eq_one_of_commute_rhoW {g : W ≃ₗ[K] W} (hg : ∀ x, Q (g x) = Q x)
    (hc : ∀ z, g * rhoW ψ z = rhoW ψ z * g) : g = 1 := by
  have hr := Q_symm_one ψ hψ
  have hψ1 : ψ (ψ.symm 1) = ((1 : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) := by
    rw [LinearEquiv.apply_symm_apply, Matrix.SpecialLinearGroup.coe_one]
  set t := reflK Q (ψ.symm 1) with htdef
  have htt : t * t = 1 := reflK_mul_self Q _
  have hswap : ∀ z, t * rhoW ψ z * t = rhoW ψ (z.2, z.1) := fun z => by
    have h := reflK_mul_rhoW_mul_reflK ψ hψ hψ1 z
    simpa using h
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
    CFSG.Timmesfeld.RankOne.center_SL2_eq_bot K
  rcases mem_range_rhoW_or_mul_reflK ψ hψ hr hg with ⟨a, rfl⟩ | ⟨a, ha⟩
  ·
    have hca : ∀ z, a * z = z * a := fun z => rhoW_injective ψ (by rw [map_mul, map_mul, hc z])
    have h1 : a.1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Subgroup.mem_center_iff.mpr fun x => (congrArg Prod.fst (hca (x, 1))).symm
    have h2 : a.2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Subgroup.mem_center_iff.mpr fun x => (congrArg Prod.snd (hca (1, x))).symm
    rw [hcenter, Subgroup.mem_bot] at h1 h2
    rw [show a = 1 from Prod.ext h1 h2, map_one]
  ·
    exfalso
    rw [← htdef] at ha
    have hg' : g = rhoW ψ a * t := by rw [ha, mul_assoc, htt, mul_one]
    have hconj : ∀ z, rhoW ψ (a * (z.2, z.1) * a⁻¹) = rhoW ψ z := fun z => by
      rw [map_mul, map_mul, map_inv, ← hswap z]
      have h := hc z
      rw [hg'] at h
      calc rhoW ψ a * (t * rhoW ψ z * t) * (rhoW ψ a)⁻¹
          = rhoW ψ a * t * rhoW ψ z * (rhoW ψ a * t)⁻¹ := by
            rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right htt]
            group
        _ = rhoW ψ z := by rw [h, mul_inv_cancel_right]
    set x := CFSG.Timmesfeld.RankOne.upperElt K 1
    have hx : x ≠ 1 := fun h => one_ne_zero (CFSG.Timmesfeld.RankOne.upperElt_injective K
      (h.trans (CFSG.Timmesfeld.RankOne.upperElt_zero K).symm))
    have h := congrArg Prod.snd (rhoW_injective ψ (hconj (x, 1)))
    simp only [Prod.snd_mul, Prod.snd_inv, mul_inv_eq_one] at h
    apply hx
    have : a.2 * x = a.2 := h
    exact mul_eq_left.mp this

theorem commutator_eq_range_rhoW (h4 : 4 ≤ Nat.card K) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      (rhoW ψ).range := by
  have hO : (DeterminantIsometries K).map (conjψ ψ).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    ext g
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro h
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro w
      have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp h (ψ w)
      rw [determinantForm_apply, determinantForm_apply, conjψ_symm_apply,
        LinearEquiv.symm_apply_apply] at h1
      rw [hψ, hψ, h1]
    · intro h
      exact conjψ_symm_mem ψ hψ (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp h)
  rw [← hO, ← Subgroup.map_commutator, commutator_eq_range h4, MonoidHom.map_range]
  rfl

theorem reflK_mul_reflK_mem_range_rhoW {r s : W} (hr : Q r = 1) (hs : Q s = 1) :
    reflK Q r * reflK Q s ∈ (rhoW ψ).range := by
  have hr' : (ψ r).det = 1 := by rw [← hψ, hr]
  have hs' : (ψ s).det = 1 := by rw [← hψ, hs]
  exact ⟨_, (reflK_mul_reflK ψ hψ (s := ⟨ψ r, hr'⟩) (s' := ⟨ψ s, hs'⟩) rfl rfl).symm⟩

omit hψ in
theorem exists_omega_plus {Q : QuadraticForm K W} (hdim : Module.finrank K W = 4)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hplus : ∃ U : Submodule K W, Module.finrank K U = 2 ∧ ∀ u ∈ U, Q u = 0) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
        (W ≃ₗ[K] W),
      Function.Injective ρ ∧ ρ.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (ρ.range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2 ∧
      (4 ≤ Nat.card K → ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ = ρ.range) ∧
      (∀ r, Q r = 1 → reflK Q r ∉ ρ.range) ∧
      (∀ r s, Q r = 1 → Q s = 1 → reflK Q r * reflK Q s ∈ ρ.range) ∧
      (∀ z x, ρ z * ρ (x, 1) * (ρ z)⁻¹ = ρ (z.1 * x * z.1⁻¹, 1)) ∧
      (∀ z y, ρ z * ρ (1, y) * (ρ z)⁻¹ = ρ (1, z.2 * y * z.2⁻¹)) ∧
      (∀ r, Q r = 1 → ∀ x, ∃ y, reflK Q r * ρ (x, 1) * reflK Q r = ρ (1, y)) ∧
      (∀ r, Q r = 1 → ∀ y, ∃ x, reflK Q r * ρ (1, y) * reflK Q r = ρ (x, 1)) ∧
      ∀ g : W ≃ₗ[K] W, (∀ x, Q (g x) = Q x) → (∀ z, g * ρ z = ρ z * g) → g = 1 := by
  obtain ⟨ψ, hψ⟩ := exists_detCoords₀ hdim hnd hplus
  have hs : ∀ r, Q r = 1 → (ψ r).det = 1 := fun r hr => by rw [← hψ, hr]
  refine ⟨rhoW ψ, rhoW_injective ψ, range_rhoW_le ψ hψ, index_range_rhoW ψ hψ,
    commutator_eq_range_rhoW ψ hψ, fun r hr => reflK_not_mem_range_rhoW ψ hψ hr,
    fun r s hr hs' => reflK_mul_reflK_mem_range_rhoW ψ hψ hr hs', rhoW_conj_inl ψ,
    rhoW_conj_inr ψ, fun r hr x => ?_, fun r hr y => ?_,
    fun g hg hc => eq_one_of_commute_rhoW ψ hψ hg hc⟩
  · exact ⟨_, reflK_conj_inl ψ hψ (s := ⟨ψ r, hs r hr⟩) rfl x⟩
  · exact ⟨_, reflK_conj_inr ψ hψ (s := ⟨ψ r, hs r hr⟩) rfl y⟩

end CFSG.Quasithin.SimsG4.OrthPlus
