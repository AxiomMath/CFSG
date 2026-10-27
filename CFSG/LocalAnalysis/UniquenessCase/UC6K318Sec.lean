module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K318

open Module
open scoped Matrix

section AlgClosed

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem prime_dvd_of_pow_eq_one {s : ℕ} [hs : Fact s.Prime] {ω : K} (hω1 : ω ≠ 1) {j : ℕ}
    (hωs : ω ^ (s ^ j) = 1) {m : ℕ} (hm : ω ^ m = 1) : s ∣ m := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hs.out).1 (orderOf_dvd_of_pow_eq_one hωs)
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hi
    exact hω1 hi
  calc s ∣ s ^ i := dvd_pow_self s hi0
    _ = orderOf ω := hi.symm
    _ ∣ m := orderOf_dvd_of_pow_eq_one hm

theorem pow_finrank_eq_one {X Y : Module.End K V} (hX : Function.Injective X)
    (hY : Function.Injective Y) {E : Submodule K V} (hXE : ∀ v ∈ E, X v ∈ E)
    (hYE : ∀ v ∈ E, Y v ∈ E) {ω : K} (hrel : ∀ v ∈ E, Y (X v) = ω • X (Y v)) :
    ω ^ finrank K E = 1 := by
  set XE : Module.End K E := X.restrict hXE
  set YE : Module.End K E := Y.restrict hYE
  have hrelE : YE * XE = ω • (XE * YE) := by
    ext v
    simp only [XE, YE, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.restrict_coe_apply,
      SetLike.val_smul]
    exact hrel v v.2
  have hinj : ∀ (Z : Module.End K V) (hZ : ∀ v ∈ E, Z v ∈ E), Function.Injective Z →
      IsUnit (LinearMap.det (Z.restrict hZ)) := by
    intro Z hZ hZi
    rw [← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
    have h1 : Function.Injective (Z.restrict hZ) := by
      intro a b hab
      exact Subtype.ext (hZi (congrArg Subtype.val hab))
    exact ⟨h1, LinearMap.injective_iff_surjective.1 h1⟩
  have hdet := congrArg LinearMap.det hrelE
  rw [LinearMap.det_smul, map_mul, map_mul, mul_comm (LinearMap.det YE)] at hdet
  have hu : IsUnit (LinearMap.det XE * LinearMap.det YE) :=
    (hinj X hXE hX).mul (hinj Y hYE hY)
  have h2 : (1 : K) * (LinearMap.det XE * LinearMap.det YE) =
      ω ^ finrank K E * (LinearMap.det XE * LinearMap.det YE) := by
    rw [one_mul]
    exact hdet
  exact (hu.mul_left_inj.1 h2).symm

theorem dvd_finrank_of_mul_eq_mul {s : ℕ} [hs : Fact s.Prime] {X Y C : Module.End K V}
    (hXY : Y * X = C * (X * Y)) (hCX : C * X = X * C) (hCY : C * Y = Y * C) {j : ℕ}
    (hC : C ^ (s ^ j) = 1) (hX : Function.Injective X) (hY : Function.Injective Y)
    (hfix : ∀ v, C v = v → v = 0) (W : Submodule K V) (hXW : ∀ w ∈ W, X w ∈ W)
    (hYW : ∀ w ∈ W, Y w ∈ W) (hCW : ∀ w ∈ W, C w ∈ W) : s ∣ finrank K W := by
  obtain ⟨n, hn⟩ : ∃ n, finrank K W = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing W with
  | _ n ih =>
  by_cases hW : W = ⊥
  · rw [hW, finrank_bot]
    exact dvd_zero s
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW
  obtain ⟨ω, hω⟩ := Module.End.exists_eigenvalue (C.restrict hCW)
  obtain ⟨w, hw⟩ := hω.exists_hasEigenvector
  have hCw : C (w : V) = ω • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [one_smul] at hCw
    exact hw0 (hfix _ hCw)
  have hωs : ω ^ (s ^ j) = 1 := by
    have hpow : ∀ k : ℕ, (C ^ k) (w : V) = ω ^ k • (w : V) := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ, Module.End.mul_apply, hCw, map_smul, ihk, smul_smul, pow_succ, mul_comm]
    have h1 := hpow (s ^ j)
    rw [hC, Module.End.one_apply] at h1
    have h2 : (ω ^ (s ^ j) - 1) • (w : V) = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hw0)
  set D : Module.End K V := C - ω • 1 with hD
  have hDX : D * X = X * D := by
    rw [hD, sub_mul, mul_sub, hCX, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hDY : D * Y = Y * D := by
    rw [hD, sub_mul, mul_sub, hCY, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hDC : D * C = C * D := by
    rw [hD, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hcomm : ∀ (Z : Module.End K V), D * Z = Z * D → ∀ v, Z (D v) = D (Z v) := by
    intro Z hZ v
    rw [← Module.End.mul_apply, ← hZ, Module.End.mul_apply]
  set E : Submodule K V := W ⊓ LinearMap.ker D with hE
  have hmemE : ∀ v, v ∈ E ↔ v ∈ W ∧ C v = ω • v := by
    intro v
    rw [hE, Submodule.mem_inf, LinearMap.mem_ker, hD, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hinvE : ∀ (Z : Module.End K V), D * Z = Z * D → (∀ v ∈ W, Z v ∈ W) →
      ∀ v ∈ E, Z v ∈ E := by
    intro Z hZ hZW v hv
    refine ⟨hZW v hv.1, ?_⟩
    have hv2 : D v = 0 := hv.2
    show D (Z v) = 0
    rw [← hcomm Z hZ v, hv2, map_zero]
  have hrel : ∀ v ∈ E, Y (X v) = ω • X (Y v) := by
    intro v hv
    have h1 : Y (X v) = C (X (Y v)) := by
      rw [← Module.End.mul_apply, hXY, Module.End.mul_apply, Module.End.mul_apply]
    rw [h1]
    exact ((hmemE _).1 (hinvE X hDX hXW _ (hinvE Y hDY hYW v hv))).2
  have hdvdE : s ∣ finrank K E :=
    prime_dvd_of_pow_eq_one hω1 hωs
      (pow_finrank_eq_one hX hY (hinvE X hDX hXW) (hinvE Y hDY hYW) hrel)
  have hEpos : 0 < finrank K E := by
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨w, (hmemE _).2 ⟨w.2, hCw⟩⟩, ?_⟩
    intro h
    exact hw0 (congrArg Subtype.val h)
  set W' : Submodule K V := W.map D with hW'
  have hrank : finrank K W' + finrank K E = finrank K W := by
    have h := LinearMap.finrank_range_add_finrank_ker (D.domRestrict W)
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
    have h2 : finrank K ((LinearMap.ker D).comap W.subtype) = finrank K E := by
      rw [← Submodule.finrank_map_subtype_eq W, Submodule.map_comap_subtype]
    rw [← h2]
    exact h
  have hinvW' : ∀ (Z : Module.End K V), D * Z = Z * D → (∀ v ∈ W, Z v ∈ W) →
      ∀ v ∈ W', Z v ∈ W' := by
    intro Z hZ hZW v hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hv
    rw [hcomm Z hZ u]
    exact Submodule.mem_map_of_mem (hZW u hu)
  have hW'dvd : s ∣ finrank K W' :=
    ih (finrank K W') (by omega) W' (hinvW' X hDX hXW) (hinvW' Y hDY hYW)
      (hinvW' C hDC hCW) rfl
  rw [← hrank]
  exact dvd_add hW'dvd hdvdE

end AlgClosed

theorem dvd_of_conj_eq_central_mul {F : Type*} [Field F] {n s : ℕ} [Fact s.Prime]
    {x y c : GL (Fin n) F} (hxy : y * x * y⁻¹ = c * x) (hcx : c * x = x * c)
    (hcy : c * y = y * c) {j : ℕ} (hc : c ^ (s ^ j) = 1)
    (hfix : ∀ v, (c : Matrix (Fin n) (Fin n) F) *ᵥ v = v → v = 0) : s ∣ n := by
  classical
  let K := AlgebraicClosure F
  let φ : Matrix (Fin n) (Fin n) F →+* Module.End K (Fin n → K) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K)).toAlgHom
      : Matrix (Fin n) (Fin n) K →+* Module.End K (Fin n → K)).comp (algebraMap F K).mapMatrix
  have hφ : ∀ M : Matrix (Fin n) (Fin n) F, ∀ v, φ M v = (M.map (algebraMap F K)) *ᵥ v :=
    fun M v => rfl
  have hunit : ∀ g : GL (Fin n) F, Function.Injective (φ (g : Matrix (Fin n) (Fin n) F)) := by
    intro g a b hab
    have h1 : φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        φ (g : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    have h2 := congrArg (φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hab
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, h1, Module.End.one_apply,
      Module.End.one_apply] at h2
  have hxy' : (y : Matrix (Fin n) (Fin n) F) * x = c * (x * y) := by
    have h := congrArg (fun g : GL (Fin n) F => ((g * y : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F)) hxy
    simp only [inv_mul_cancel_right, Units.val_mul] at h
    rw [h, Matrix.mul_assoc]
  have hcx' : (c : Matrix (Fin n) (Fin n) F) * x = x * c := by
    simpa only [Units.val_mul] using congrArg Units.val hcx
  have hcy' : (c : Matrix (Fin n) (Fin n) F) * y = y * c := by
    simpa only [Units.val_mul] using congrArg Units.val hcy
  have hc' : φ (c : Matrix (Fin n) (Fin n) F) ^ (s ^ j) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  have hdet : ((c : Matrix (Fin n) (Fin n) F) - 1).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    apply hfix
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have hfixK : ∀ v, φ (c : Matrix (Fin n) (Fin n) F) v = v → v = 0 := by
    intro v hv
    by_contra hv0
    apply hdet
    have hK : ((algebraMap F K).mapMatrix ((c : Matrix (Fin n) (Fin n) F) - 1)).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, ?_⟩
      have hcv : (algebraMap F K).mapMatrix (c : Matrix (Fin n) (Fin n) F) *ᵥ v = v := hv
      rw [map_sub, map_one, Matrix.sub_mulVec, Matrix.one_mulVec, hcv, sub_self]
    rw [← RingHom.map_det] at hK
    exact (algebraMap F K).injective (hK.trans (map_zero _).symm)
  have h := dvd_finrank_of_mul_eq_mul (K := K) (s := s)
    (X := φ (x : Matrix (Fin n) (Fin n) F)) (Y := φ (y : Matrix (Fin n) (Fin n) F))
    (C := φ (c : Matrix (Fin n) (Fin n) F))
    (by rw [← map_mul, ← map_mul, ← map_mul, hxy']) (by rw [← map_mul, ← map_mul, hcx'])
    (by rw [← map_mul, ← map_mul, hcy']) hc' (hunit x) (hunit y) hfixK ⊤
    (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
  rwa [finrank_top, Module.finrank_fin_fun] at h

end CFSG.LocalAnalysis.UniquenessCase.UC6.K318
