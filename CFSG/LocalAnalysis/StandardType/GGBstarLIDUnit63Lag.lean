module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMain
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUBasic
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUFrame
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairPair
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Perp

public section

namespace CFSG.StandardType

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open TypeA.PGLTor

namespace LID63

variable {K : Type} [Field K] {n : ℕ}

section Fix

variable [Finite K]

theorem pow_succ_eq_one_of_cube (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1) {c : K}
    (hc0 : c ≠ 0) (hc3 : (c ^ (2 ^ n + 1)) ^ 3 = 1) : c ^ (2 ^ n + 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ n = r + 1 := ⟨2 ^ n - 1, by omega⟩
  have hcard : Fintype.card K - 1 = (r + 2) * r := by
    rw [← Nat.card_eq_fintype_card, hK, hr]
    exact Nat.sub_eq_of_eq_add (by ring)
  have h1 : (c ^ (2 ^ n + 1)) ^ r = 1 := by
    rw [← pow_mul, hr, show (r + 1 + 1) * r = (r + 2) * r by ring, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one c hc0
  have hpq' : 3 ∣ r + 2 := by
    rw [hr] at hpq
    omega
  have h3 : ¬ 3 ∣ r := by omega
  have hcop : Nat.gcd 3 r = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h2 := (pow_gcd_eq_one (a := c ^ (2 ^ n + 1))).mpr ⟨hc3, h1⟩
  rwa [hcop, pow_one] at h2

theorem eq_one_of_fixes_lagrangian (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hpq : 3 ∣ 2 ^ n + 1) {G : Subgroup (GL (Fin 6) K)} (hG : IsProjElem 3 G)
    (hGu : ∀ x ∈ G, ∃ c : Kˣ,
      Matrix.GeneralLinearGroup.scalar (Fin 6) c * x ∈ primeFormUnitary h (idGram K 6))
    {R : Submodule K (Fin 6 → K)} (hRi : ∀ u ∈ R, ∀ v ∈ R, (h.bar ∘ v) ⬝ᵥ u = 0)
    (hR3 : Module.finrank K R = 3) {x : GL (Fin 6) K} (hx : x ∈ G)
    (hfix : ∀ v ∈ R, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v = v) : x = 1 := by
  classical
  have : CharP K 2 := h.charP
  have hRperp : hperp h R = R := hperp_eq_of_isotropic h hRi (by omega)
  set Xm : Matrix (Fin 6) (Fin 6) K := (x : Matrix (Fin 6) (Fin 6) K) with hXm
  obtain ⟨v₀, hv₀R, hv₀⟩ : ∃ v ∈ R, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : R = ⊥ := (Submodule.eq_bot_iff R).mpr hcon
    rw [this, finrank_bot] at hR3
    omega
  obtain ⟨s, hs⟩ := hG.pow_scalar x hx
  have hpowfix : ∀ k : ℕ, (Xm ^ k) *ᵥ v₀ = v₀ := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_mulVec]
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hfix v₀ hv₀R, ih]
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨i, hi⟩ : ∃ i, v₀ i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv₀ (funext hcon)
    have h1 := congrFun (hpowfix 3) i
    have h2 : ((x ^ 3 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Xm ^ 3 :=
      Units.val_pow_eq_pow_val _ _
    rw [← h2, hs] at h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
      at h1
    have hs1 : s = 1 := by
      apply Units.ext
      rw [Units.val_one]
      exact mul_right_cancel₀ hi (by rw [h1, one_mul])
    rw [hs, hs1, map_one]
  obtain ⟨c, hcB⟩ := hGu x hx
  have hB3 : (Matrix.GeneralLinearGroup.scalar (Fin 6) c * x) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (c ^ 3) := by
    rw [(commute_scalar c x).mul_pow, hx3, map_pow, mul_one]
  have hc3U : Matrix.GeneralLinearGroup.scalar (Fin 6) (c ^ 3) ∈
      primeFormUnitary h (idGram K 6) := by
    rw [← hB3]
    exact (primeFormUnitary h (idGram K 6)).pow_mem hcB 3
  have hc3 := (SUTorus.scalar_mem_primeFormUnitary_iff h (c ^ 3)).mp hc3U
  rw [UnitaryFieldData.bar_apply, Units.val_pow_eq_pow_val] at hc3
  have hν3 : (((c : Kˣ) : K) ^ (2 ^ n + 1)) ^ 3 = 1 := by
    rw [← hc3]
    ring
  have hν := pow_succ_eq_one_of_cube hK hpq c.ne_zero hν3
  have hbarc : h.bar (c : K) * c = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_succ]
    exact hν
  have hmat : ((Matrix.GeneralLinearGroup.scalar (Fin 6) c * x : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = (c : K) • Xm := by
    ext i j
    simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_mul, hXm]
  have hxu : (Xm.map h.bar)ᵀ * Xm = 1 := by
    have h1 := hcB
    rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one, hmat] at h1
    have hmap : ((c : K) • Xm).map h.bar = h.bar (c : K) • Xm.map h.bar := by
      ext i j
      simp
    rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hbarc,
      one_smul] at h1
    exact h1
  have hmem : ∀ b : Fin 6 → K, Xm *ᵥ b - b ∈ R := by
    intro b
    have hb : Xm *ᵥ b - b ∈ hperp h R := by
      intro u hu
      have h1 := SURepair.vecMul_bar_of_mulVec_eq h hxu (hfix u hu)
      rw [dotProduct_sub, dotProduct_mulVec, h1, sub_self]
    rwa [hRperp] at hb
  have hX2 : Xm * Xm = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← mulVec_mulVec, one_mulVec]
    set b : Fin 6 → K := Pi.single i 1 with hb
    have hw := hfix _ (hmem b)
    rw [mulVec_sub] at hw
    funext j
    have h1 := congrFun hw j
    simp only [Pi.sub_apply] at h1
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    simp only [hb] at h1 ⊢
    linear_combination h1 + ((Xm *ᵥ Pi.single i 1) j - (Pi.single i 1 : Fin 6 → K) j) * h2
  have hx2 : x * x = 1 :=
    Units.ext (by rw [Units.val_mul, Units.val_one]; exact hX2)
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [hx3, hx2]; simp

end Fix

section Bound

variable [Finite K] {G : Subgroup (GL (Fin 6) K)} {R : Submodule K (Fin 6 → K)}

@[expose] noncomputable def lagRes (R : Submodule K (Fin 6 → K))
    (hRG : ∀ x ∈ G, ∀ v ∈ R, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v ∈ R) :
    ↥G →* Module.End K R where
  toFun x := LinearMap.restrict (Matrix.toLin' ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
    (fun v hv => by rw [Matrix.toLin'_apply]; exact hRG x x.2 v hv)
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    ext v
    simp [Matrix.mulVec_mulVec]

theorem lagRes_apply (hRG : ∀ x ∈ G, ∀ v ∈ R, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v ∈ R)
    (x : G) (v : R) :
    ((lagRes R hRG x v : R) : Fin 6 → K) =
      ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ (v : Fin 6 → K) := by
  simp [lagRes]

@[expose] noncomputable def lagResMat (b : Module.Basis (Fin 3) K R)
    (hRG : ∀ x ∈ G, ∀ v ∈ R, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v ∈ R) : ↥G →* GL (Fin 3) K :=
  (((LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom).comp (lagRes R hRG)).toHomUnits

theorem coe_lagResMat (b : Module.Basis (Fin 3) K R)
    (hRG : ∀ x ∈ G, ∀ v ∈ R, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v ∈ R) (x : G) :
    ((lagResMat b hRG x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      LinearMap.toMatrixAlgEquiv b (lagRes R hRG x) := by
  simp [lagResMat]

theorem lagResMat_eq_one_iff (b : Module.Basis (Fin 3) K R)
    (hRG : ∀ x ∈ G, ∀ v ∈ R, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v ∈ R) (x : G) :
    lagResMat b hRG x = 1 ↔ ∀ v ∈ R, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v = v := by
  constructor
  · intro h1 v hv
    have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [coe_lagResMat, Units.val_one] at h2
    have h3 : lagRes R hRG x = 1 := by
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [h2, map_one]
    have h4 := congrArg (fun f : Module.End K R => ((f ⟨v, hv⟩ : R) : Fin 6 → K)) h3
    simpa [lagRes_apply] using h4
  · intro hall
    apply Units.ext
    rw [coe_lagResMat, Units.val_one]
    have h3 : lagRes R hRG x = 1 := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [lagRes_apply]
      simpa using hall v v.2
    rw [h3, map_one]

theorem lagResMat_scalar (b : Module.Basis (Fin 3) K R)
    (hRG : ∀ x ∈ G, ∀ v ∈ R, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v ∈ R) (u : Kˣ)
    (hu : Matrix.GeneralLinearGroup.scalar (Fin 6) u ∈ G) :
    lagResMat b hRG ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) u, hu⟩ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
  apply Units.ext
  rw [coe_lagResMat]
  have h3 : lagRes R hRG ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) u, hu⟩ =
      (u : K) • (1 : Module.End K R) := by
    ext v
    rw [lagRes_apply]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [h3, map_smul, map_one, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem card_le_of_lagrangian (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hpq : 3 ∣ 2 ^ n + 1) (hG : IsProjElem 3 G)
    (hGu : ∀ x ∈ G, ∃ c : Kˣ,
      Matrix.GeneralLinearGroup.scalar (Fin 6) c * x ∈ primeFormUnitary h (idGram K 6))
    (hRi : ∀ u ∈ R, ∀ v ∈ R, (h.bar ∘ v) ⬝ᵥ u = 0) (hR3 : Module.finrank K R = 3)
    (hRG : ∀ x ∈ G, ∀ v ∈ R, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v ∈ R) :
    Nat.card G ≤ 9 * (Nat.card K - 1) := by
  classical
  set b : Module.Basis (Fin 3) K R := Module.finBasisOfFinrankEq K R hR3 with hb
  set ρ := lagResMat b hRG with hρ
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 := (lagResMat_eq_one_iff b hRG x).mp hx
    exact Subtype.ext (eq_one_of_fixes_lagrangian h hK hpq hG hGu hRi hR3 x.2 h1)
  have hproj : IsProjElem 3 ρ.range := by
    refine ⟨fun u => ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 6) u, hG.scalar_mem u⟩,
      lagResMat_scalar b hRG u _⟩, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨u, hu⟩ := hG.pow_scalar x x.2
      refine ⟨u, ?_⟩
      rw [← map_pow]
      have h1 : x ^ 3 = ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) u, hG.scalar_mem u⟩ :=
        Subtype.ext hu
      rw [h1, hρ, lagResMat_scalar]
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      obtain ⟨u, hu⟩ := hG.comm_scalar x x.2 y y.2
      refine ⟨u, ?_⟩
      rw [← map_mul, ← map_mul]
      have h1 : x * y = ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) u, hG.scalar_mem u⟩ * (y * x) :=
        Subtype.ext hu
      rw [h1, map_mul, hρ, lagResMat_scalar]
  have hcard : Nat.card G = Nat.card ρ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hle := card_le_of_isProjElem Nat.prime_three (by norm_num)
    (SUTorus.dvd_card_sub_one h hpq) hproj
  rw [Fintype.card_fin] at hle
  omega

end Bound


end LID63

end CFSG.StandardType

end
