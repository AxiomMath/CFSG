module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoCard
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSURoot
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition
open scoped Matrix

private theorem rckRPhr_vecMul_single_rev {F : Type} [Field F] {n : ℕ} (a : Fin n) :
    Matrix.vecMul (Pi.single a (1 : F)) (Unitary.antidiag n) =
      (Pi.single (Fin.rev a) (1 : F) : Fin n → F) := by
  funext i
  rw [CFSG.Timmesfeld.LieEmbed.vecMul_antidiag]
  simp only [Pi.single_apply]
  by_cases h : i = Fin.rev a
  · have h' : Fin.rev i = a := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h']
  · have h' : Fin.rev i ≠ a := fun hh => h (by rw [← hh, Fin.rev_rev])
    rw [if_neg h, if_neg h']

private theorem rckRPhr_single_dot_single {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (a b : ι) :
    (Pi.single a (1 : F) : ι → F) ⬝ᵥ (Pi.single b (1 : F) : ι → F) =
      if a = b then 1 else 0 := by
  classical
  simp only [dotProduct]
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg hab]
      have hba : b ≠ a := fun h => hab h.symm
      simp [hba]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem rckRPhr_vecMul_eq_uForm {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (x y : Fin n → F) :
    Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag n) ⬝ᵥ y =
      CFSG.Timmesfeld.LieEmbed.uForm σ x y := by
  rw [CFSG.Timmesfeld.LieEmbed.uForm, ← Matrix.dotProduct_mulVec]

private theorem rckRPhr_uForm_map {F K : Type} [Field F] [Field K] {n : ℕ}
    (σ : F ≃+* F) (σ' : K ≃+* K) (τ : F ≃+* K)
    (hτ : ∀ c, τ (σ c) = σ' (τ c)) (x y : Fin n → F) :
    CFSG.Timmesfeld.LieEmbed.uForm σ' (fun i => τ (x i)) (fun i => τ (y i)) =
      τ (CFSG.Timmesfeld.LieEmbed.uForm σ x y) := by
  rw [CFSG.Timmesfeld.LieEmbed.uForm_eq, CFSG.Timmesfeld.LieEmbed.uForm_eq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  exact (hτ _).symm

private theorem rckRPhr_uNil_map {F K : Type} [Field F] [Field K] {n : ℕ}
    (σ : F ≃+* F) (σ' : K ≃+* K) (τ : F ≃+* K)
    (hτ : ∀ c, τ (σ c) = σ' (τ c)) (v : Fin n → F) :
    (CFSG.Timmesfeld.LieEmbed.uNil σ v).map (τ : F → K) =
      CFSG.Timmesfeld.LieEmbed.uNil σ' (fun i => τ (v i)) := by
  ext i j
  rw [Matrix.map_apply, CFSG.Timmesfeld.LieEmbed.uNil, CFSG.Timmesfeld.LieEmbed.uNil,
    Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, map_mul,
    CFSG.Timmesfeld.LieEmbed.uRow_apply, CFSG.Timmesfeld.LieEmbed.uRow_apply]
  congr 1
  exact hτ _

private theorem rckRPhr_one_add_smul_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {N : Matrix ι ι F} (hN : N * N = 0) (a b : F) :
    (1 + a • N) * (1 + b • N) = 1 + (a + b) • N := by
  have h : (a • N) * (b • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN, smul_zero]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, h, add_zero, add_assoc,
    ← add_smul]

private theorem rckRPhr_mem_unitTransvGroup_iff {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {σ : F →+* F} {G : Matrix ι ι F} {v : ι → F}
    (hiso : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ v = 0) (g : GL ι F) :
    g ∈ unitTransvGroup σ G v ↔ ∃ c : F, σ c = c ∧
      (g : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) := by
  classical
  let N : Matrix ι ι F := Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G)
  have hN : N * N = 0 := by
    rw [show N = Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) from rfl,
      Matrix.vecMulVec_mul_vecMulVec, hiso, zero_smul, Matrix.vecMulVec_zero]
  let H : Subgroup (GL ι F) :=
    { carrier := {g | ∃ c : F, σ c = c ∧ (g : Matrix ι ι F) = 1 + c • N}
      mul_mem' := by
        rintro g h ⟨a, ha, hga⟩ ⟨b, hb, hgb⟩
        refine ⟨a + b, by rw [map_add, ha, hb], ?_⟩
        rw [Units.val_mul, hga, hgb, rckRPhr_one_add_smul_mul hN]
      one_mem' := ⟨0, map_zero σ, by rw [zero_smul, add_zero, Units.val_one]⟩
      inv_mem' := by
        rintro g ⟨a, ha, hga⟩
        let u : GL ι F := Units.mk (1 + (-a) • N) (1 + a • N)
          (by rw [rckRPhr_one_add_smul_mul hN]; simp)
          (by rw [rckRPhr_one_add_smul_mul hN]; simp)
        have hu : (u : Matrix ι ι F) = 1 + (-a) • N := rfl
        have hmul : g * u = 1 := by
          ext
          rw [Units.val_mul, Units.val_one, hga, hu, rckRPhr_one_add_smul_mul hN]
          simp
        refine ⟨-a, by rw [map_neg, ha], ?_⟩
        rw [show g⁻¹ = u from inv_eq_of_mul_eq_one_right hmul, hu] }
  have hclosure : Subgroup.closure {g : GL ι F | ∃ c : F, σ c = c ∧
      (g : Matrix ι ι F) = 1 + c • N} = H := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      exact hg
    · intro g hg
      exact Subgroup.subset_closure hg
  rw [unitTransvGroup, show Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) = N from rfl,
    hclosure]
  rfl


theorem exists_longRoot_transv_of_suModel {F₀ K W : Type} [Field F₀] [Finite F₀] [CharP F₀ 2]
    [Field K] [AddCommGroup W] [Module K W] {f m : ℕ}
    (hc : Nat.card F₀ = (2 ^ f) ^ 2) (hm : 2 ≤ m) {σ : K ≃+* K}
    (β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K) (τ : F₀ ≃+* K)
    (hτ : ∀ c, τ (CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 f c) = σ (τ c))
    (e : W ≃ₗ[K] (Fin m → K))
    (he : ∀ x y, Matrix.vecMul (fun i => σ (e x i)) (Unitary.antidiag m) ⬝ᵥ e y = β x y)
    (ρ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 f) m) →* (W ≃ₗ[K] W))
    (hρ : ∀ A w, e (ρ A w) =
      (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *ᵥ e w) :
    ∃ (β₀ : Fin (Unitary.rootDatum hc m).rank → ℤ) (v : W),
      β₀ ∈ (Unitary.rootDatum hc m).roots ∧ GGLongRoot (Unitary.rootDatum hc m) β₀ ∧
      Nat.card ((Unitary.rootDatum hc m).rootGroup β₀) = 2 ^ f ∧ v ≠ 0 ∧ β v v = 0 ∧
      ∀ y ∈ (Unitary.rootDatum hc m).rootGroup β₀, ∃ c : K, σ c = c ∧
        ∀ w, ρ y w = w + (c * β v w) • v := by
  classical
  let σ₀ : F₀ ≃+* F₀ := CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 f
  let J : Matrix (Fin m) (Fin m) F₀ := Unitary.antidiag m
  let i₀ : Fin m := ⟨0, by omega⟩
  let v₀ : Fin m → F₀ := Pi.single i₀ 1
  let w₀ : Fin m → F₀ := Pi.single (Fin.rev i₀) 1
  have hrev0 : Fin.rev i₀ ≠ i₀ := by
    intro h
    have hval := congrArg Fin.val h
    rw [Fin.val_rev] at hval
    simp [i₀] at hval
    omega
  have hσ₀v₀ : (fun i => σ₀ (v₀ i)) = v₀ := by
    funext i
    by_cases hi : i = i₀
    · subst hi
      simp [v₀]
    · simp [v₀, Pi.single_eq_of_ne hi]
  have hσ₀w₀ : (fun i => σ₀ (w₀ i)) = w₀ := by
    funext i
    by_cases hi : i = Fin.rev i₀
    · subst hi
      simp [w₀]
    · simp [w₀, Pi.single_eq_of_ne hi]
  have hv₀ : Matrix.vecMul (fun i => σ₀ (v₀ i)) J ⬝ᵥ v₀ = 0 := by
    rw [hσ₀v₀, show v₀ = Pi.single i₀ (1 : F₀) from rfl,
      rckRPhr_vecMul_single_rev (F := F₀) (n := m) i₀, rckRPhr_single_dot_single]
    rw [if_neg hrev0]
  have hw₀ : Matrix.vecMul (fun i => σ₀ (w₀ i)) J ⬝ᵥ w₀ = 0 := by
    rw [hσ₀w₀, show w₀ = Pi.single (Fin.rev i₀) (1 : F₀) from rfl,
      rckRPhr_vecMul_single_rev (F := F₀) (n := m) (Fin.rev i₀), Fin.rev_rev,
      rckRPhr_single_dot_single]
    rw [if_neg (Ne.symm hrev0)]
  have hvw₀ : Matrix.vecMul (fun i => σ₀ (v₀ i)) J ⬝ᵥ w₀ = 1 := by
    rw [hσ₀v₀, show v₀ = Pi.single i₀ (1 : F₀) from rfl,
      rckRPhr_vecMul_single_rev (F := F₀) (n := m) i₀, rckRPhr_single_dot_single]
    simp
  obtain ⟨β₀, hβ₀, hlong, u, -, -⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_conj_rootGroup_eq_unitTransvGroup_PSU
      hc m hm v₀ w₀ hv₀ hw₀ hvw₀
  let R : Subgroup ↥(Unitary.SU σ₀ m) := (Unitary.rootDatum hc m).rootGroup β₀
  obtain ⟨v₁, w₁, hv₁, hw₁, hvw₁, hR₁, -⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_unitTransvGroup_eq_conj_rootGroup_SU
      (F := F₀) hc m hβ₀ hlong (1 : ↥(Unitary.SU σ₀ m))
  have hR : R.map (Unitary.SU σ₀ m).subtype =
      unitTransvGroup σ₀.toRingHom J v₁ := by
    have hmapid : Subgroup.map (MulEquiv.toMonoidHom
        (MulAut.conj (1 : ↥(Unitary.SU σ₀ m))))
        ((Unitary.rootDatum hc m).rootGroup β₀) =
        (Unitary.rootDatum hc m).rootGroup β₀ := by
      have h1 : (MulEquiv.toMonoidHom
          (MulAut.conj (1 : ↥(Unitary.SU σ₀ m)))) = MonoidHom.id _ := by
        ext x
        simp
      rw [h1, Subgroup.map_id]
    rw [hmapid] at hR₁
    simpa [R, J, σ₀] using hR₁
  have hv₁0 : v₁ ≠ 0 := by
    intro hzero
    have hz : (fun i => σ₀ (v₁ i)) = (0 : Fin m → F₀) := by
      rw [hzero]
      funext i
      simp
    rw [hz] at hvw₁
    simpa using hvw₁
  let v : W := e.symm (fun i => τ (v₁ i))
  have hev : e v = fun i => τ (v₁ i) := by
    simp [v]
  have hv0 : v ≠ 0 := by
    intro hv
    apply hv₁0
    have h1 : (fun i => τ (v₁ i)) = 0 := by
      have h2 : e v = e 0 := by rw [hv]
      simpa [hev] using h2
    funext i
    have hi : τ (v₁ i) = τ 0 := by simpa using congrFun h1 i
    exact τ.injective hi
  have hβvv : β v v = 0 := by
    rw [← he v v, hev, rckRPhr_vecMul_eq_uForm]
    rw [rckRPhr_uForm_map σ₀ σ τ hτ v₁ v₁]
    have hv₁u : CFSG.Timmesfeld.LieEmbed.uForm σ₀ v₁ v₁ = 0 := by
      rw [← rckRPhr_vecMul_eq_uForm σ₀ v₁ v₁]
      exact hv₁
    rw [hv₁u, map_zero]
  have hfix : Nat.card {c : F₀ // σ₀.toRingHom c = c} = 2 ^ f := by
    let sf : Subfield F₀ := CFSG.LieType.Steinberg.fixedSubfield F₀ 2 f
    have hmem : ∀ c : F₀, (c ∈ sf ↔ σ₀.toRingHom c = c) := by
      intro c
      rw [show sf = CFSG.LieType.Steinberg.fixedSubfield F₀ 2 f from rfl,
        CFSG.LieType.Steinberg.mem_fixedSubfield]
      rfl
    calc Nat.card {c : F₀ // σ₀.toRingHom c = c}
        = Nat.card sf := Nat.card_congr (Equiv.subtypeEquivRight (fun c => (hmem c).symm))
      _ = 2 ^ f := CFSG.LieType.Steinberg.card_fixedSubfield hc
  have hcard : Nat.card R = 2 ^ f := by
    have hJ : IsUnit J.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero m)
    calc Nat.card R = Nat.card (R.map (Unitary.SU σ₀ m).subtype) :=
          (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
      _ = Nat.card (unitTransvGroup σ₀.toRingHom J v₁) := by rw [hR]
      _ = Nat.card {c : F₀ // σ₀.toRingHom c = c} :=
          CFSG.StandardType.RCKRP.card_unitTransvGroup σ₀.toRingHom hJ hv₁0 hv₁
      _ = 2 ^ f := hfix
  have haction : ∀ y ∈ R, ∃ c : K, σ c = c ∧
      ∀ w, ρ y w = w + (c * β v w) • v := by
    intro y hy
    have hyT : ((y : GL (Fin m) F₀)) ∈ unitTransvGroup σ₀.toRingHom J v₁ := by
      rw [← hR]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    obtain ⟨c, hcσ, hyMat⟩ :=
      (rckRPhr_mem_unitTransvGroup_iff (σ := σ₀.toRingHom) (G := J) (v := v₁) hv₁
        ((y : GL (Fin m) F₀))).1 hyT
    have hyMat' : (((y : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀)) =
        1 + c • CFSG.Timmesfeld.LieEmbed.uNil σ₀ v₁ := hyMat
    refine ⟨τ c, ?_, ?_⟩
    · have hcσ' : σ₀ c = c := hcσ
      rw [← hτ c]
      exact congrArg τ hcσ'
    · intro w
      apply e.injective
      have hmapy : (((y : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map
          (τ : F₀ → K)) =
          1 + (τ c) • CFSG.Timmesfeld.LieEmbed.uNil σ (fun i => τ (v₁ i)) := by
        rw [hyMat']
        rw [Matrix.map_add (τ : F₀ → K) (map_add τ) 1
          (c • CFSG.Timmesfeld.LieEmbed.uNil σ₀ v₁)]
        rw [Matrix.map_one (τ : F₀ → K) (map_zero τ) (map_one τ)]
        rw [Matrix.map_smul' (τ : F₀ → K) c (CFSG.Timmesfeld.LieEmbed.uNil σ₀ v₁)
          (map_mul τ)]
        rw [rckRPhr_uNil_map σ₀ σ τ hτ v₁]
      have hβeq : CFSG.Timmesfeld.LieEmbed.uForm σ (fun i => τ (v₁ i)) (e w) = β v w := by
        rw [← hev, ← rckRPhr_vecMul_eq_uForm σ (e v) (e w)]
        exact he v w
      have hmain : e (ρ y w) = e (w + (τ c * β v w) • v) := by
        rw [hρ y w, hmapy, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
          CFSG.Timmesfeld.LieEmbed.uNil_mulVec, hβeq, smul_smul, map_add, map_smul, hev]
      exact hmain
  exact ⟨β₀, v, hβ₀, hlong, hcard, hv0, hβvv, haction⟩

end CFSG.StandardType.RCKRP
