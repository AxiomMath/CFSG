module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotGenTwoWindows
public import TauCeti.GroupTheory.Sylow

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly Matrix CFSG.SeitzReduction.UnitaryPilot
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {K : Type} [Field K]

@[expose] noncomputable def tZeroSU (hK : Nat.card K = 4) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  CFSG.SeitzReduction.UnitaryPilot.permSU (fieldDataFour hK) (Equiv.swap 0 1)

@[expose] noncomputable def tZero (hK : Nat.card K = 4) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  LargeEvenProjMk _ (tZeroSU hK)

theorem finite_of_card_eq_four (hK : Nat.card K = 4) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)

theorem permMatrix_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ.permMatrix K i j = if σ i = j then 1 else 0 := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]

theorem coe_permSU_eq_permutationGL {n : ℕ} (h : UnitaryFieldData 2 1 K)
    (σ : Equiv.Perm (Fin n)) :
    (permSU h σ : GL (Fin n) K) = TauCeti.permutationGL (k := K) σ⁻¹ := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [show ((TauCeti.permutationGL (k := K) σ⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i j =
      ((1 : GL (Fin n) K) * TauCeti.permutationGL (k := K) σ⁻¹ : GL (Fin n) K) i j from by
    rw [one_mul],
    TauCeti.coe_mul_permutationGL_apply]
  rw [coe_permSU, permMatrix_apply]
  simp only [Units.val_one, Matrix.one_apply]
  by_cases h : σ i = j
  · have h' : i = σ⁻¹ j := by
      rw [← h]
      exact (Equiv.symm_apply_apply σ i).symm
    rw [if_pos h, if_pos h']
  · have h' : ¬ i = σ⁻¹ j := by
      intro hij
      apply h
      rw [hij]
      exact Equiv.apply_symm_apply σ j
    rw [if_neg h, if_neg h']

theorem isDiag_permMatrix_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix K).IsDiag ↔ σ = 1 := by
  constructor
  · intro h
    refine Equiv.ext fun j => ?_
    show σ j = j
    by_contra hne
    have hne' : j ≠ σ j := fun hc => hne hc.symm
    have h1 : σ.permMatrix K j (σ j) = 0 := h (i := j) (j := σ j) hne'
    rw [permMatrix_apply, if_pos rfl] at h1
    exact one_ne_zero h1
  · rintro rfl
    intro i j hij
    rw [permMatrix_apply]
    simp [hij]

@[expose] noncomputable def permGLSU (hK : Nat.card K = 4) (ρ : Equiv.Perm (Fin 6)) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  permSU (fieldDataFour hK) ρ⁻¹

theorem coe_permGLSU (hK : Nat.card K = 4) (ρ : Equiv.Perm (Fin 6)) :
    (permGLSU hK ρ : GL (Fin 6) K) = TauCeti.permutationGL (k := K) ρ := by
  simp [permGLSU, coe_permSU_eq_permutationGL]

theorem permGLSU_mul (hK : Nat.card K = 4) (ρ σ : Equiv.Perm (Fin 6)) :
    permGLSU hK ρ * permGLSU hK σ = permGLSU hK (ρ * σ) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_permGLSU, coe_permGLSU, coe_permGLSU, ← map_mul]

theorem permGLSU_one (hK : Nat.card K = 4) : permGLSU hK (1 : Equiv.Perm (Fin 6)) = 1 := by
  apply Subtype.ext
  rw [coe_permGLSU, map_one]
  rfl

theorem permGLSU_inv (hK : Nat.card K = 4) (ρ : Equiv.Perm (Fin 6)) :
    permGLSU hK ρ⁻¹ = (permGLSU hK ρ)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, coe_permGLSU, coe_permGLSU, ← map_inv]

theorem tZeroSU_eq_permGLSU (hK : Nat.card K = 4) :
    tZeroSU hK = permGLSU hK (Equiv.swap 0 1) := by
  rw [tZeroSU, permGLSU, Equiv.swap_inv]

theorem diagGL_mem_SU_of_prod_eq_one (hK : Nat.card K = 4) {t : Fin 6 → Kˣ}
    (ht : ∏ i, t i = 1) :
    TauCeti.diagGL t ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
  haveI : Finite K := finite_of_card_eq_four hK
  rw [mem_SU_iff (fieldDataFour hK)]
  constructor
  · have h := congrArg (fun u : Kˣ => (u : K)) (TauCeti.det_diagGL t)
    rw [ht, Units.val_one] at h
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h
  · rw [TauCeti.diagGL_coe]
    exact diagonal_map_transpose_mul_eq_one _ (fun i => by
      rw [← Units.val_pow_eq_pow_val, cube_unit_eq_one hK (t i)]
      rfl)

theorem diagGL_mem_torSU_of_prod_eq_one (hK : Nat.card K = 4) {t : Fin 6 → Kˣ}
    (ht : ∏ i, t i = 1) :
    (⟨TauCeti.diagGL t, diagGL_mem_SU_of_prod_eq_one hK ht⟩ :
      ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) ∈ torSU K := by
  exact TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨t, rfl⟩

@[expose] noncomputable def torToDiag :
    torSU K →* ↥(TauCeti.diagonalTorus K 6) where
  toFun D := ⟨(D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))), D.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def torParamHom : torSU K →* (Fin 6 → Kˣ) :=
  (TauCeti.diagonalTorusEquiv K 6).symm.toMonoidHom.comp (torToDiag (K := K))

theorem diagGL_torParamHom (D : torSU K) :
    TauCeti.diagGL (torParamHom (K := K) D) = (D : GL (Fin 6) K) := by
  have h2 := TauCeti.coe_diagonalTorusEquiv_apply (k := K)
    ((TauCeti.diagonalTorusEquiv K 6).symm (torToDiag (K := K) D))
  rw [MulEquiv.apply_symm_apply] at h2
  change TauCeti.diagGL
    ((TauCeti.diagonalTorusEquiv K 6).symm (torToDiag (K := K) D)) = (D : GL (Fin 6) K)
  exact h2.symm

theorem torParamHom_eq_of_diagGL_eq {D : torSU K} {t : Fin 6 → Kˣ}
    (h : TauCeti.diagGL t = (D : GL (Fin 6) K)) : torParamHom (K := K) D = t := by
  apply TauCeti.diagGL_injective
  rw [diagGL_torParamHom, h]

theorem prod_torParamHom (hK : Nat.card K = 4) (D : torSU K) :
    ∏ i, torParamHom (K := K) D i = 1 := by
  haveI : Finite K := finite_of_card_eq_four hK
  have hdet := (mem_SU_iff (fieldDataFour hK)).mp
    (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))).2 |>.1
  have h := congrArg (fun u : Kˣ => (u : K)) (TauCeti.det_diagGL (torParamHom (K := K) D))
  rw [diagGL_torParamHom, Matrix.GeneralLinearGroup.val_det_apply, hdet] at h
  exact Units.ext h.symm

theorem torParamHom_injective : Function.Injective (torParamHom (K := K)) := by
  intro D E h
  have h' : (D : GL (Fin 6) K) = (E : GL (Fin 6) K) := by
    have hh := congrArg (fun t => TauCeti.diagGL t) h
    rwa [diagGL_torParamHom D, diagGL_torParamHom E] at hh
  exact Subtype.ext (Subtype.ext h')

theorem permGLSU_mul_mem_torSU (hK : Nat.card K = 4) (ρ : Equiv.Perm (Fin 6))
    {D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))} (hD : D ∈ torSU K) :
    permGLSU hK ρ * D * (permGLSU hK ρ)⁻¹ ∈ torSU K := by
  haveI : Finite K := finite_of_card_eq_four hK
  have hdiag : (D : GL (Fin 6) K) ∈ TauCeti.diagonalTorus K 6 := hD
  obtain ⟨t, ht⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp hdiag
  have ht' : torParamHom (K := K) ⟨D, hD⟩ = t := by
    apply TauCeti.diagGL_injective
    rw [diagGL_torParamHom]
    exact ht.symm
  have hprod : ∏ i, t i = 1 := by
    rw [← ht']
    exact prod_torParamHom hK ⟨D, hD⟩
  have hprod' : ∏ i, t (ρ⁻¹ i) = 1 := by
    rw [Equiv.prod_comp ρ⁻¹ t, hprod]
  have hconjGL : (permGLSU hK ρ : GL (Fin 6) K) * (D : GL (Fin 6) K) *
      ((permGLSU hK ρ : GL (Fin 6) K))⁻¹ = TauCeti.diagGL (fun i => t (ρ⁻¹ i)) := by
    rw [coe_permGLSU, ← ht]
    exact TauCeti.permutationGL_mul_diagGL_mul_inv ρ t
  show ((permGLSU hK ρ * D * (permGLSU hK ρ)⁻¹ : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
    GL (Fin 6) K) ∈ TauCeti.diagonalTorus K 6
  rw [show ((permGLSU hK ρ * D * (permGLSU hK ρ)⁻¹ : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
      GL (Fin 6) K) = (permGLSU hK ρ : GL (Fin 6) K) * (D : GL (Fin 6) K) *
        ((permGLSU hK ρ : GL (Fin 6) K))⁻¹ from rfl, hconjGL]
  exact TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨_, rfl⟩

theorem permGLSU_mem_normalizer_torSU (hK : Nat.card K = 4) (ρ : Equiv.Perm (Fin 6)) :
    permGLSU hK ρ ∈ Subgroup.normalizer (torSU K : Set ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro D
  constructor
  · intro hD
    exact permGLSU_mul_mem_torSU hK ρ hD
  · intro hD
    have h1 := permGLSU_mul_mem_torSU hK ρ⁻¹ hD
    rw [permGLSU_inv, inv_inv] at h1
    have h2 : (permGLSU hK ρ)⁻¹ * (permGLSU hK ρ * D * (permGLSU hK ρ)⁻¹) *
        (permGLSU hK ρ) = D := by
      group
    rwa [h2] at h1

theorem orderOf_tZero (hK : Nat.card K = 4) : orderOf (tZero hK) = 2 := by
  haveI : Finite K := finite_of_card_eq_four hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : tZero hK ^ 2 = 1 := by
    rw [pow_two]
    have h1 : tZeroSU hK * tZeroSU hK = 1 := by
      rw [tZeroSU_eq_permGLSU, permGLSU_mul, Equiv.swap_mul_self, permGLSU_one]
    change LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (tZeroSU hK) *
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (tZeroSU hK) = 1
    rw [← map_mul, h1, map_one]
  have hne : tZero hK ≠ 1 := by
    intro h
    have hker : tZeroSU hK ∈ (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).ker := by
      rw [MonoidHom.mem_ker]
      exact h
    rw [QuotientGroup.ker_mk'] at hker
    rw [Subgroup.mem_subgroupOf] at hker
    obtain ⟨c, hc⟩ := hker
    have h00 : (((tZeroSU hK : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) 0 0 = 0 := by
      rw [tZeroSU, coe_permSU, permMatrix_apply]
      simp
    have hval := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K) 0 0)) hc
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      if_pos rfl, h00] at hval
    exact c.ne_zero hval
  exact orderOf_eq_prime hsq hne

theorem tZero_mem_normalizer_torU (hK : Nat.card K = 4) :
    tZero hK ∈ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by
  have hP : permGLSU hK (Equiv.swap 0 1) ∈
      Subgroup.normalizer (torSU K : Set ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    permGLSU_mem_normalizer_torSU hK _
  have hmem : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (permGLSU hK (Equiv.swap 0 1)) ∈
      Subgroup.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (Subgroup.normalizer (torSU K : Set ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) :=
    Subgroup.mem_map.mpr ⟨_, hP, rfl⟩
  have hle := Subgroup.le_normalizer_map
    (f := LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (H := torSU K) hmem
  rw [tZero, tZeroSU_eq_permGLSU]
  exact hle

theorem scalar_eq_diagGL_const (c : Kˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) K) =
      TauCeti.diagGL (fun _ => c) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, TauCeti.diagGL_coe]

theorem proj_eq_iff_exists_scalar [Finite K] (hK : Nat.card K = 4)
    {A B : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))} :
    LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) A =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) B ↔
      ∃ c : Kˣ, (B : GL (Fin 6) K) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c * (A : GL (Fin 6) K) := by
  constructor
  · intro h
    rw [QuotientGroup.mk'_eq_mk'] at h
    obtain ⟨z, hz, hzAB⟩ := h
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨c, hc⟩ := hz
    refine ⟨c, ?_⟩
    calc (B : GL (Fin 6) K) = ((A * z : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
          GL (Fin 6) K) := by rw [hzAB]
      _ = (A : GL (Fin 6) K) * (z : GL (Fin 6) K) := Subgroup.coe_mul ..
      _ = (A : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) c := by rw [hc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c * (A : GL (Fin 6) K) :=
        (Matrix.GeneralLinearGroup.scalar_commute c (A : GL (Fin 6) K)).symm
  · rintro ⟨c, hc⟩
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, scalar_mem_SU hK c⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact ⟨c, rfl⟩
    · apply Subtype.ext
      show (A : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) c = (B : GL (Fin 6) K)
      rw [hc]
      exact (Matrix.GeneralLinearGroup.scalar_commute c (A : GL (Fin 6) K)).symm

@[expose] def ratioHom (a b : Fin 6) : (Fin 6 → Kˣ) →* Kˣ where
  toFun t := t a / t b
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, div_eq_mul_inv, _root_.mul_inv_rev]
    ac_rfl

theorem ratioHom_apply (a b : Fin 6) (t : Fin 6 → Kˣ) : ratioHom a b t = t a / t b := rfl

theorem exists_ne_ne {a b : Fin 6} (hab : a ≠ b) : ∃ c : Fin 6, c ≠ a ∧ c ≠ b := by
  have hcard : ({a, b}ᶜ : Finset (Fin 6)).card = 4 := by
    rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
  have hpos : 0 < ({a, b}ᶜ : Finset (Fin 6)).card := by rw [hcard]; norm_num
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1, hc.2⟩

theorem exists_ratio_eq_prod_eq_one [Finite K] {a b : Fin 6} (hab : a ≠ b) (μ : Kˣ) :
    ∃ t : Fin 6 → Kˣ, ratioHom a b t = μ ∧ ∏ i, t i = 1 := by
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne hab
  refine ⟨Function.update (Function.update (1 : Fin 6 → Kˣ) a μ) c μ⁻¹, ?_, ?_⟩
  · rw [ratioHom_apply, Function.update_of_ne (Ne.symm hca), Function.update_self,
      Function.update_of_ne (Ne.symm hcb), Function.update_of_ne (Ne.symm hab), Pi.one_apply,
      div_one]
  · have hfun : Function.update (Function.update (1 : Fin 6 → Kˣ) a μ) c μ⁻¹ =
        (fun i => Function.update (1 : Fin 6 → Kˣ) a μ i *
          Function.update (1 : Fin 6 → Kˣ) c μ⁻¹ i) := by
      funext i
      by_cases hic : i = c
      · subst hic
        rw [Function.update_self, Function.update_of_ne hca, Pi.one_apply, one_mul,
          Function.update_self]
      · rw [Function.update_of_ne hic, Function.update_of_ne hic, Pi.one_apply, mul_one]
    rw [hfun, Finset.prod_mul_distrib, prod_update_one a μ, prod_update_one c μ⁻¹,
      mul_inv_cancel]

@[expose] noncomputable def torPairEq (a b : Fin 6) : Subgroup (torSU K) :=
  ((ratioHom a b).comp (torParamHom (K := K))).ker

theorem mem_torPairEq {a b : Fin 6} {D : torSU K} :
    D ∈ torPairEq (K := K) a b ↔
      torParamHom (K := K) D a = torParamHom (K := K) D b := by
  rw [torPairEq, MonoidHom.mem_ker, MonoidHom.comp_apply, ratioHom_apply, div_eq_one]

theorem card_torPairEq (hK : Nat.card K = 4) {a b : Fin 6} (hab : a ≠ b) :
    Nat.card ↥(torPairEq (K := K) a b) = 3 ^ 4 := by
  haveI : Finite K := finite_of_card_eq_four hK
  have hsurj : Function.Surjective ((ratioHom a b).comp (torParamHom (K := K))) := by
    intro μ
    obtain ⟨t, ht, hprod⟩ := exists_ratio_eq_prod_eq_one hab μ
    have hp : torParamHom (K := K)
        ⟨⟨TauCeti.diagGL t, diagGL_mem_SU_of_prod_eq_one hK hprod⟩,
          diagGL_mem_torSU_of_prod_eq_one hK hprod⟩ = t := torParamHom_eq_of_diagGL_eq rfl
    exact ⟨_, by rw [MonoidHom.comp_apply, hp, ht]⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [card_torSU hK] at hcard
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [hu] at hcard
  have h243 : Nat.card ↥(torPairEq (K := K) a b) * 3 = 243 := by
    rw [show (243 : ℕ) = 3 ^ 5 by norm_num]
    exact hcard
  have h81 : Nat.card ↥(torPairEq (K := K) a b) = 81 := by omega
  rw [h81]
  norm_num

theorem torParamHom_permGLSU_conj (hK : Nat.card K = 4) (ρ : Equiv.Perm (Fin 6)) (D : torSU K) :
    torParamHom (K := K)
        ⟨permGLSU hK ρ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * (permGLSU hK ρ)⁻¹,
          permGLSU_mul_mem_torSU hK ρ D.2⟩ =
      fun i => torParamHom (K := K) D (ρ⁻¹ i) := by
  apply TauCeti.diagGL_injective
  rw [diagGL_torParamHom]
  have hconj : (permGLSU hK ρ : GL (Fin 6) K) * (D : GL (Fin 6) K) *
      ((permGLSU hK ρ : GL (Fin 6) K))⁻¹ =
      TauCeti.diagGL (fun i => torParamHom (K := K) D (ρ⁻¹ i)) := by
    rw [coe_permGLSU, ← diagGL_torParamHom D]
    exact TauCeti.permutationGL_mul_diagGL_mul_inv ρ _
  rw [show ((⟨permGLSU hK ρ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * (permGLSU hK ρ)⁻¹,
      permGLSU_mul_mem_torSU hK ρ D.2⟩ : torSU K) : GL (Fin 6) K) =
      (permGLSU hK ρ : GL (Fin 6) K) * (D : GL (Fin 6) K) *
        ((permGLSU hK ρ : GL (Fin 6) K))⁻¹ from rfl, hconj]

theorem scalar_mul_diagGL_apply (c : Kˣ) (t : Fin 6 → Kˣ) (i : Fin 6) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 6) c * TauCeti.diagGL t : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) i i = (c : K) * (t i : K) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    TauCeti.diagGL_coe, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, if_pos rfl]

theorem ker_proj_comp_subtype (hK : Nat.card K = 4) :
    (((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp (torSU K).subtype).ker) =
      ((LargeEvenScalars (Fin 6) K).subgroupOf
        (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).subgroupOf (torSU K) := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    ← MonoidHom.mem_ker (f := LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
    QuotientGroup.ker_mk']
  exact Iff.rfl

@[expose] noncomputable def permU (hK : Nat.card K = 4) (ρ : Equiv.Perm (Fin 6)) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  LargeEvenProjMk _ (permGLSU hK ρ)

theorem permU_mem_normalizer_torU (hK : Nat.card K = 4) (ρ : Equiv.Perm (Fin 6)) :
    permU hK ρ ∈ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by
  have hmem : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (permGLSU hK ρ) ∈
      Subgroup.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (Subgroup.normalizer (torSU K : Set ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) :=
    Subgroup.mem_map.mpr ⟨_, permGLSU_mem_normalizer_torSU hK ρ, rfl⟩
  exact Subgroup.le_normalizer_map _ hmem

theorem permMatrix_eq_coe_permutationGL {n : ℕ} (h : UnitaryFieldData 2 1 K)
    (ρ : Equiv.Perm (Fin n)) :
    ρ.permMatrix K = ((TauCeti.permutationGL (k := K) ρ⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) := by
  rw [← coe_permSU (h := h) ρ, coe_permSU_eq_permutationGL]

theorem isDiag_permutationGL_iff {n : ℕ} (h : UnitaryFieldData 2 1 K)
    (ρ : Equiv.Perm (Fin n)) :
    (((TauCeti.permutationGL (k := K) ρ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).IsDiag ↔
      ρ = 1 := by
  have hiff : (((TauCeti.permutationGL (k := K) ρ : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K).IsDiag ↔ ρ⁻¹ = 1 := by
    rw [show ((TauCeti.permutationGL (k := K) ρ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (ρ⁻¹).permMatrix K from
      (permMatrix_eq_coe_permutationGL h ρ⁻¹).symm, isDiag_permMatrix_iff]
  rw [hiff]
  exact ⟨fun h' => by rw [← inv_inv ρ, h', inv_one], fun h' => by rw [h', inv_one]⟩

theorem exists_diagGL_mul_permutationGL_of_mem_normalizer (hK : Nat.card K = 4)
    {g : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hN : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g ∈ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) :
    ∃ d : Fin 6 → Kˣ, ∃ σ : Equiv.Perm (Fin 6),
      (g : GL (Fin 6) K) = TauCeti.diagGL d * TauCeti.permutationGL σ := by
  haveI : Finite K := finite_of_card_eq_four hK
  obtain ⟨ω, hω⟩ := exists_root_omega hK
  refine TauCeti.exists_eq_diagGL_mul_permutationGL_of_forall_ne (n := 6)
    (g := (g : GL (Fin 6) K)) ?_
  intro i j hij
  let T : torSU K := ⟨diagTwoSU (ω := ω) hω hij, diagTwoSU_mem_torSU hω hij⟩
  refine ⟨torParamHom (K := K) T, ?_, ?_⟩
  · have hTU : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
        (T : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) ∈ torU K :=
      Subgroup.mem_map.mpr ⟨_, T.2, rfl⟩
    have h1 : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
        (g * (T : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * g⁻¹) ∈ torU K := by
      rw [map_mul, map_mul, map_inv]
      exact ((Subgroup.mem_normalizer_iff.mp hN) _).mp hTU
    obtain ⟨D', hD'tor, hD'eq⟩ := Subgroup.mem_map.mp h1
    obtain ⟨c, hc⟩ := (proj_eq_iff_exists_scalar hK
      (A := (g * (T : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * g⁻¹)) (B := D')).mp hD'eq.symm
    have h3 : (D' : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) c *
        ((g : GL (Fin 6) K) * (T : GL (Fin 6) K) * (g : GL (Fin 6) K)⁻¹) := by
      rw [hc]
      rfl
    have hprodGL : (g : GL (Fin 6) K) * (T : GL (Fin 6) K) * (g : GL (Fin 6) K)⁻¹ =
        (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ * (D' : GL (Fin 6) K) := by
      calc (g : GL (Fin 6) K) * (T : GL (Fin 6) K) * (g : GL (Fin 6) K)⁻¹ =
          (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ *
            (Matrix.GeneralLinearGroup.scalar (Fin 6) c *
              ((g : GL (Fin 6) K) * (T : GL (Fin 6) K) * (g : GL (Fin 6) K)⁻¹)) := by group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ * (D' : GL (Fin 6) K) := by rw [← h3]
    show (g : GL (Fin 6) K) * TauCeti.diagGL (torParamHom (K := K) T) *
        (g : GL (Fin 6) K)⁻¹ ∈ TauCeti.diagonalTorus K 6
    rw [show TauCeti.diagGL (torParamHom (K := K) T) = (T : GL (Fin 6) K) from
      diagGL_torParamHom T, hprodGL]
    rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ : GL (Fin 6) K) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c⁻¹ from by rw [← map_inv]]
    rw [scalar_eq_diagGL_const,
      show (D' : GL (Fin 6) K) = TauCeti.diagGL (torParamHom (K := K) ⟨D', hD'tor⟩) from
        (diagGL_torParamHom (D := ⟨D', hD'tor⟩)).symm, ← map_mul,
      TauCeti.mem_diagonalTorus_iff_exists_diagGL]
    exact ⟨_, rfl⟩
  · have hti : (torParamHom (K := K) T i : K) = ω := by
      have h := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K) i i))
        (diagGL_torParamHom T)
      rw [TauCeti.diagGL_apply, if_pos rfl] at h
      rw [show (T : GL (Fin 6) K) = ((diagTwoSU (ω := ω) hω hij :
        ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) from rfl,
        coe_diagTwoSU] at h
      refine h.trans ?_
      rw [diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagTwo,
        Matrix.diagonal_apply, if_pos rfl]
      exact diagVec_self hij
    have htj : (torParamHom (K := K) T j : K) = ω ^ 2 := by
      have h := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K) j j))
        (diagGL_torParamHom T)
      rw [TauCeti.diagGL_apply, if_pos rfl] at h
      rw [show (T : GL (Fin 6) K) = ((diagTwoSU (ω := ω) hω hij :
        ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) from rfl,
        coe_diagTwoSU] at h
      refine h.trans ?_
      rw [diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagTwo,
        Matrix.diagonal_apply, if_pos rfl]
      exact diagVec_other hij
    intro hEq
    have h2 := congrArg (fun u : Kˣ => (u : K)) hEq
    rw [hti, htj] at h2
    exact omega_sq_ne_omega hK hω h2.symm

theorem monomial_mul_self (d : Fin 6 → Kˣ) (σ : Equiv.Perm (Fin 6)) :
    (TauCeti.diagGL d * TauCeti.permutationGL σ) *
      (TauCeti.diagGL d * TauCeti.permutationGL σ) =
      TauCeti.diagGL (fun i => d i * d (σ⁻¹ i)) * TauCeti.permutationGL (σ * σ) := by
  have hcomm : TauCeti.permutationGL σ * TauCeti.diagGL d =
      TauCeti.diagGL (fun i => d (σ⁻¹ i)) * TauCeti.permutationGL σ := by
    have h := congrArg (fun g => g * TauCeti.permutationGL σ)
      (TauCeti.permutationGL_mul_diagGL_mul_inv σ d)
    simpa [mul_assoc] using h
  calc (TauCeti.diagGL d * TauCeti.permutationGL σ) *
        (TauCeti.diagGL d * TauCeti.permutationGL σ)
      = TauCeti.diagGL d * (TauCeti.permutationGL σ * TauCeti.diagGL d) *
          TauCeti.permutationGL σ := by group
    _ = TauCeti.diagGL d * (TauCeti.diagGL (fun i => d (σ⁻¹ i)) * TauCeti.permutationGL σ) *
          TauCeti.permutationGL σ := by rw [hcomm]
    _ = (TauCeti.diagGL d * TauCeti.diagGL (fun i => d (σ⁻¹ i))) *
          (TauCeti.permutationGL σ * TauCeti.permutationGL σ) := by group
    _ = TauCeti.diagGL (fun i => d i * d (σ⁻¹ i)) * TauCeti.permutationGL (σ * σ) := by
        rw [← map_mul, ← map_mul]
        rfl

theorem permutation_mul_self_eq_one_of_monomial_sq (hK : Nat.card K = 4) {d : Fin 6 → Kˣ}
    {σ : Equiv.Perm (Fin 6)} {c : Kˣ}
    (h : (TauCeti.diagGL d * TauCeti.permutationGL σ) *
      (TauCeti.diagGL d * TauCeti.permutationGL σ) = Matrix.GeneralLinearGroup.scalar (Fin 6) c) :
    σ * σ = 1 := by
  have hsq := monomial_mul_self d σ
  rw [hsq] at h
  have hdiag : (((TauCeti.permutationGL (k := K) (σ * σ) : GL (Fin 6) K)) :
      Matrix (Fin 6) (Fin 6) K).IsDiag := by
    have h1 : (TauCeti.permutationGL (k := K) (σ * σ) : GL (Fin 6) K) =
        (TauCeti.diagGL (fun i => d i * d (σ⁻¹ i)))⁻¹ *
          Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      calc (TauCeti.permutationGL (k := K) (σ * σ) : GL (Fin 6) K)
          = (TauCeti.diagGL (fun i => d i * d (σ⁻¹ i)))⁻¹ *
            (TauCeti.diagGL (fun i => d i * d (σ⁻¹ i)) *
              TauCeti.permutationGL (σ * σ)) := by group
        _ = (TauCeti.diagGL (fun i => d i * d (σ⁻¹ i)))⁻¹ *
              Matrix.GeneralLinearGroup.scalar (Fin 6) c := by rw [h]
    rw [h1, show ((TauCeti.diagGL (fun i => d i * d (σ⁻¹ i)))⁻¹ : GL (Fin 6) K) =
        TauCeti.diagGL (fun i => (d i * d (σ⁻¹ i))⁻¹) from by rw [← map_inv]; rfl,
      scalar_eq_diagGL_const, ← map_mul]
    rw [TauCeti.diagGL_coe]
    exact Matrix.isDiag_diagonal _
  exact (isDiag_permutationGL_iff (fieldDataFour hK) (σ * σ)).mp hdiag

@[expose] noncomputable def torDiffHom (σ : Equiv.Perm (Fin 6)) :
    torSU K →* (Fin 6 → Kˣ) where
  toFun D := fun i => torParamHom (K := K) D (σ i) / torParamHom (K := K) D i
  map_one' := by
    funext i
    simp
  map_mul' x y := by
    funext i
    simp only [Pi.mul_apply, map_mul, Pi.div_apply, div_eq_mul_inv, _root_.mul_inv_rev]
    ac_rfl

@[expose] noncomputable def torFix (σ : Equiv.Perm (Fin 6)) : Subgroup (torSU K) :=
  (torDiffHom (K := K) σ).ker

theorem mem_torFix {σ : Equiv.Perm (Fin 6)} {D : torSU K} :
    D ∈ torFix (K := K) σ ↔ ∀ i, torParamHom (K := K) D (σ i) = torParamHom (K := K) D i := by
  rw [torFix, MonoidHom.mem_ker]
  constructor
  · intro h i
    have h2 := congrFun h i
    change torParamHom (K := K) D (σ i) / torParamHom (K := K) D i = 1 at h2
    rw [div_eq_one] at h2
    exact h2
  · intro h
    funext i
    change torParamHom (K := K) D (σ i) / torParamHom (K := K) D i = 1
    rw [div_eq_one]
    exact h i

theorem mem_torFix_of_conj_eq (hK : Nat.card K = 4) {σ : Equiv.Perm (Fin 6)} (hσ : σ * σ = 1)
    {D : torSU K}
    (h : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
        (permGLSU hK σ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * (permGLSU hK σ)⁻¹) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
        (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) :
    D ∈ torFix (K := K) σ := by
  haveI : Finite K := finite_of_card_eq_four hK
  obtain ⟨c, hc⟩ := (proj_eq_iff_exists_scalar hK
    (A := (permGLSU hK σ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * (permGLSU hK σ)⁻¹))
    (B := (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))))).mp h
  have hconj : ((permGLSU hK σ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
      (permGLSU hK σ)⁻¹ : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) =
      TauCeti.diagGL (fun i => torParamHom (K := K) D (σ⁻¹ i)) := by
    rw [show ((permGLSU hK σ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
        (permGLSU hK σ)⁻¹ : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) =
        (permGLSU hK σ : GL (Fin 6) K) * (D : GL (Fin 6) K) *
          ((permGLSU hK σ : GL (Fin 6) K))⁻¹ from rfl,
      coe_permGLSU, ← diagGL_torParamHom D]
    exact TauCeti.permutationGL_mul_diagGL_mul_inv σ _
  have hrel : ∀ i, torParamHom (K := K) D i = c * torParamHom (K := K) D (σ⁻¹ i) := by
    intro i
    have hh := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K) i i)) hc
    rw [hconj] at hh
    rw [← diagGL_torParamHom D, TauCeti.diagGL_apply, if_pos rfl] at hh
    rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 6) c *
        TauCeti.diagGL (fun i => torParamHom (K := K) D (σ⁻¹ i)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) i i =
        (c : K) * (torParamHom (K := K) D (σ⁻¹ i) : K) from
      scalar_mul_diagGL_apply c _ i] at hh
    exact Units.ext hh
  have hσinv : σ⁻¹ = σ := by
    calc σ⁻¹ = σ⁻¹ * (σ * σ) := by rw [hσ, mul_one]
      _ = σ := by group
  have hc1 : c = 1 := by
    by_cases hfixed : ∃ i, σ i = i
    · obtain ⟨i, hi⟩ := hfixed
      have h := hrel i
      rw [hσinv, hi] at h
      have h' : (c : K) * (torParamHom (K := K) D i : K) = 1 * (torParamHom (K := K) D i : K) := by
        rw [one_mul]
        exact congrArg (fun u : Kˣ => (u : K)) h.symm
      exact Units.ext (mul_right_cancel₀ (Units.ne_zero (torParamHom (K := K) D i)) h')
    · push Not at hfixed
      have h1u := hrel ⟨0, by norm_num⟩
      have h2u := hrel (σ ⟨0, by norm_num⟩)
      rw [hσinv] at h1u h2u
      have hσσ : σ (σ ⟨0, by norm_num⟩) = ⟨0, by norm_num⟩ := by
        have h3 := congrFun (congrArg (fun e : Equiv.Perm (Fin 6) => (e : Fin 6 → Fin 6)) hσ)
          ⟨0, by norm_num⟩
        simpa using h3
      rw [hσσ] at h2u
      have h1 : (torParamHom (K := K) D ⟨0, by norm_num⟩ : K) =
          (c : K) * (torParamHom (K := K) D (σ ⟨0, by norm_num⟩) : K) :=
        congrArg (fun u : Kˣ => (u : K)) h1u
      have h2 : (torParamHom (K := K) D (σ ⟨0, by norm_num⟩) : K) =
          (c : K) * (torParamHom (K := K) D ⟨0, by norm_num⟩ : K) :=
        congrArg (fun u : Kˣ => (u : K)) h2u
      have h3 : (torParamHom (K := K) D ⟨0, by norm_num⟩ : K) =
          (c : K) ^ 2 * (torParamHom (K := K) D ⟨0, by norm_num⟩ : K) := by
        calc (torParamHom (K := K) D ⟨0, by norm_num⟩ : K) =
              (c : K) * (torParamHom (K := K) D (σ ⟨0, by norm_num⟩) : K) := by rw [h1]
          _ = (c : K) * ((c : K) * (torParamHom (K := K) D ⟨0, by norm_num⟩ : K)) := by rw [h2]
          _ = (c : K) ^ 2 * (torParamHom (K := K) D ⟨0, by norm_num⟩ : K) := by ring
      have h4 : (c : K) ^ 2 * (torParamHom (K := K) D ⟨0, by norm_num⟩ : K) =
          1 * (torParamHom (K := K) D ⟨0, by norm_num⟩ : K) := by
        rw [one_mul]
        exact h3.symm
      have hc2 : c ^ 2 = 1 :=
        Units.ext (mul_right_cancel₀ (Units.ne_zero (torParamHom (K := K) D ⟨0, by norm_num⟩)) h4)
      have hc3 : c ^ 3 = 1 := cube_unit_eq_one hK c
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 * 1⁻¹ := by rw [hc3, hc2]
        _ = 1 := by simp
  rw [mem_torFix]
  intro i
  have h := hrel i
  rw [hσinv, hc1, one_mul] at h
  exact h.symm

theorem conj_eq_self_of_mem_torFix (hK : Nat.card K = 4) {σ : Equiv.Perm (Fin 6)} (hσ : σ * σ = 1)
    {D : torSU K} (hD : D ∈ torFix (K := K) σ) :
    permGLSU hK σ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
        (permGLSU hK σ)⁻¹ = (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
  have hfix := (mem_torFix (K := K)).mp hD
  have hσinv : σ⁻¹ = σ := by
    calc σ⁻¹ = σ⁻¹ * (σ * σ) := by rw [hσ, mul_one]
      _ = σ := by group
  have hE : (⟨permGLSU hK σ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
      (permGLSU hK σ)⁻¹,
      permGLSU_mul_mem_torSU hK σ D.2⟩ : torSU K) = D := by
    apply torParamHom_injective
    rw [torParamHom_permGLSU_conj]
    funext i
    rw [hσinv]
    exact hfix i
  exact congrArg (fun x : torSU K => (x : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) hE

theorem scalars_subgroupOf_le_torFix (hK : Nat.card K = 4) (σ : Equiv.Perm (Fin 6)) :
    Subgroup.comap (torSU K).subtype
      ((LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) ≤
      torFix (K := K) σ := by
  intro D hD
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hD
  obtain ⟨c, hc⟩ := hD
  rw [mem_torFix]
  have ht : torParamHom (K := K) D = fun _ => c := by
    apply TauCeti.diagGL_injective
    rw [diagGL_torParamHom]
    exact hc.symm.trans (scalar_eq_diagGL_const c)
  rw [ht]
  intro i
  rfl

theorem card_ker_domRestrict_torFix (hK : Nat.card K = 4) (σ : Equiv.Perm (Fin 6)) :
    Nat.card ↥((((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp
      (torSU K).subtype)).domRestrict (torFix (K := K) σ)).ker = 3 := by
  haveI : Finite K := finite_of_card_eq_four hK
  rw [MonoidHom.ker_domRestrict]
  have hle : (((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp
      (torSU K).subtype)).ker ≤ torFix (K := K) σ := by
    rw [ker_proj_comp_subtype hK]
    exact scalars_subgroupOf_le_torFix hK σ
  have himg : Subgroup.map (torFix (K := K) σ).subtype
      (((((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp
        (torSU K).subtype)).ker).subgroupOf (torFix (K := K) σ)) =
      ((((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp
        (torSU K).subtype)).ker) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
  rw [← Subgroup.card_subtype (torFix (K := K) σ)
      (((((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp
        (torSU K).subtype)).ker).subgroupOf (torFix (K := K) σ)), himg,
    ker_proj_comp_subtype hK]
  have hN : Subgroup.map (torSU K).subtype
      (((LargeEvenScalars (Fin 6) K).subgroupOf
        (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).subgroupOf (torSU K)) =
      ((LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (scalars_subgroupOf_le_torSU hK)]
  rw [← Subgroup.card_subtype (torSU K) (((LargeEvenScalars (Fin 6) K).subgroupOf
      (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).subgroupOf (torSU K)), hN]
  exact card_scalars_subgroupOf_SU hK

theorem card_torFix (hK : Nat.card K = 4) (σ : Equiv.Perm (Fin 6))
    (hfix : Nat.card ↥((torFix (K := K) σ).map
      ((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp (torSU K).subtype)) =
      3 ^ 3) :
    Nat.card ↥(torFix (K := K) σ) = 3 ^ 4 := by
  haveI : Finite K := finite_of_card_eq_four hK
  have hcard := Subgroup.card_ker_mul_card_range
    ((((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp (torSU K).subtype)).domRestrict
      (torFix (K := K) σ))
  rw [MonoidHom.domRestrict_range, card_ker_domRestrict_torFix hK σ] at hcard
  rw [hfix] at hcard
  rw [← hcard]
  norm_num

theorem inf_centralizer_eq_map_torFix (hK : Nat.card K = 4)
    {g : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    {d : Fin 6 → Kˣ} {σ : Equiv.Perm (Fin 6)}
    (hmon : (g : GL (Fin 6) K) = TauCeti.diagGL d * TauCeti.permutationGL σ)
    (hσ : σ * σ = 1) :
    torU K ⊓ Subgroup.centralizer
        {LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g} =
      (torFix (K := K) σ).map
        ((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp (torSU K).subtype) := by
  haveI : Finite K := finite_of_card_eq_four hK
  obtain ⟨P, hP⟩ : ∃ P : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)), P = permGLSU hK σ := ⟨_, rfl⟩
  have hPGL : (P : GL (Fin 6) K) = TauCeti.permutationGL σ := by
    rw [hP]; exact coe_permGLSU hK σ
  have hPP : P * P = 1 := by
    rw [hP, permGLSU_mul, hσ, permGLSU_one]
  have hPinv : P⁻¹ = P := by
    calc P⁻¹ = P⁻¹ * (P * P) := by rw [hPP, mul_one]
      _ = P := by group
  obtain ⟨Z, hZ⟩ : ∃ Z : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)), Z = g * P⁻¹ := ⟨_, rfl⟩
  have hZGL : (Z : GL (Fin 6) K) = TauCeti.diagGL d := by
    rw [hZ, Subgroup.coe_mul, Subgroup.coe_inv, hPGL, hmon]
    group
  have hgZ : g = Z * P := by
    calc g = g * P⁻¹ * P := by group
      _ = Z * P := by rw [← hZ]
  have hZD : ∀ D : torSU K, Z * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =
      (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * Z := by
    intro D
    apply Subtype.ext
    show (Z : GL (Fin 6) K) * (D : GL (Fin 6) K) = (D : GL (Fin 6) K) * (Z : GL (Fin 6) K)
    rw [hZGL, show (D : GL (Fin 6) K) = TauCeti.diagGL (torParamHom (K := K) D) from
      (diagGL_torParamHom D).symm, ← map_mul, ← map_mul]
    congr 1
    funext i
    exact mul_comm (d i) (torParamHom (K := K) D i)
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨D0, hD0, hD0x⟩ := Subgroup.mem_map.mp hx1
    have hcomm : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g * x =
        x * LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g :=
      (Subgroup.mem_centralizer_iff.mp hx2) _ (by simp)
    have h1 : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (g * D0) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (D0 * g) := by
      rw [map_mul, map_mul, hD0x]
      exact hcomm
    have hcomm' : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) D0 =
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g)⁻¹ *
          LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) D0 *
          LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g := by
      have h2 := h1
      rw [map_mul, map_mul] at h2
      calc LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) D0
          = (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g)⁻¹ *
              (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g *
                LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) D0) := by group
        _ = (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g)⁻¹ *
              (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) D0 *
                LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g) := by rw [← h2]
        _ = (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g)⁻¹ *
              LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) D0 *
              LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g := by group
    have h2 : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (g⁻¹ * D0 * g) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) D0 := by
      rw [map_mul, map_mul, map_inv]
      exact hcomm'.symm
    have hZD0 : Z * D0 = D0 * Z := hZD ⟨D0, hD0⟩
    have hZZ : Z⁻¹ * D0 * Z = D0 := by
      calc Z⁻¹ * D0 * Z = Z⁻¹ * (D0 * Z) := by group
        _ = Z⁻¹ * (Z * D0) := by rw [hZD0]
        _ = D0 := by group
    have hconj : g⁻¹ * D0 * g = P * D0 * P⁻¹ := by
      calc g⁻¹ * D0 * g = (Z * P)⁻¹ * D0 * (Z * P) := by rw [hgZ]
        _ = P⁻¹ * (Z⁻¹ * D0 * Z) * P := by group
        _ = P⁻¹ * D0 * P := by rw [hZZ]
        _ = P * D0 * P⁻¹ := by rw [hPinv]
    have h2P : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (P * D0 * P⁻¹) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) D0 := by
      rw [← hconj]
      exact h2
    have h2' : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
        (permGLSU hK σ * D0 * (permGLSU hK σ)⁻¹) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) D0 := by
      rw [← hP]
      exact h2P
    exact Subgroup.mem_map.mpr ⟨⟨D0, hD0⟩, mem_torFix_of_conj_eq hK hσ h2', hD0x⟩
  · intro hx
    obtain ⟨D, hD, hDx⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map.mpr ⟨(D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))), D.2, hDx⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hself : P * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * P⁻¹ =
        (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
      rw [hP]
      exact conj_eq_self_of_mem_torFix hK hσ hD
    have hPD : P * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =
        (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * P := by
      have h3 := congrArg (fun z => z * P) hself
      simpa [mul_assoc] using h3
    have hZD' : Z * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =
        (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * Z := hZD D
    have hZZ : Z⁻¹ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * Z =
        (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
      calc Z⁻¹ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * Z =
            Z⁻¹ * ((D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * Z) := by group
        _ = Z⁻¹ * (Z * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by rw [hZD']
        _ = (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by group
    have hgdg : g⁻¹ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * g =
        (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
      calc g⁻¹ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * g =
            (Z * P)⁻¹ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * (Z * P) := by rw [hgZ]
        _ = P⁻¹ * (Z⁻¹ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * Z) * P := by group
        _ = P⁻¹ * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * P := by rw [hZZ]
        _ = P * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * P := by rw [hPinv]
        _ = (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by rw [hPD, mul_assoc, hPP, mul_one]
    have hDg : (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * g =
        g * (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
      have h3 := congrArg (fun z => g * z) hgdg
      simpa [mul_assoc] using h3
    rw [← hDx]
    show LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g *
        LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
          (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
        (D : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
        LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g
    rw [← map_mul, ← map_mul, hDg]

theorem eq_swap_of_torFix_eq (hK : Nat.card K = 4) {σ : Equiv.Perm (Fin 6)} (hσ : σ * σ = 1)
    {a b : Fin 6} (hab : a ≠ b) (hσa : σ a = b)
    (heq : torFix (K := K) σ = torPairEq (K := K) a b) : σ = Equiv.swap a b := by
  haveI : Finite K := finite_of_card_eq_four hK
  obtain ⟨ω, hω⟩ := exists_root_omega hK
  set ωu : Kˣ := Units.mk0 ω (omega_ne_zero hω) with hωu_def
  have hωu_ne : ωu ≠ 1 := by
    intro h
    exact omega_ne_one hK hω (by simpa [hωu_def] using congrArg Units.val h)
  have hω3 : ωu * ωu ^ 2 = 1 := by
    rw [← pow_succ']
    exact cube_unit_eq_one hK ωu
  have hσb : σ b = a := by
    have h := congrFun (congrArg (fun e : Equiv.Perm (Fin 6) => (e : Fin 6 → Fin 6)) hσ) a
    simpa [hσa] using h
  have hfixed : ∀ c, c ≠ a → c ≠ b → σ c = c := by
    intro c hca hcb
    by_contra hne
    have hca' : σ c ≠ a := by
      intro h
      have h1 : σ c = σ b := by rw [h, hσb]
      exact hcb (σ.injective h1)
    have hcb' : σ c ≠ b := by
      intro h
      have h1 : σ c = σ a := by rw [h, hσa]
      exact hca (σ.injective h1)
    have hce : ({a, b, c, σ c} : Finset (Fin 6)).card ≤ 4 := by
      have h := Finset.card_insert_le a ({b, c, σ c} : Finset (Fin 6))
      have h' := Finset.card_insert_le b ({c, σ c} : Finset (Fin 6))
      have h'' := Finset.card_insert_le c ({σ c} : Finset (Fin 6))
      simp only [Finset.card_singleton] at h''
      omega
    have hcomp : 0 < ({a, b, c, σ c} : Finset (Fin 6))ᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hcomp
    rw [Finset.mem_compl] at he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    obtain ⟨hea, heb, hec, heσc⟩ := he
    let t : Fin 6 → Kˣ :=
      fun i => Function.update (1 : Fin 6 → Kˣ) c ωu i *
        Function.update (1 : Fin 6 → Kˣ) e (ωu ^ 2) i
    have htprod : ∏ i, t i = 1 := by
      have h : t = fun i => Function.update (1 : Fin 6 → Kˣ) c ωu i *
          Function.update (1 : Fin 6 → Kˣ) e (ωu ^ 2) i := rfl
      rw [h, Finset.prod_mul_distrib, prod_update_one, prod_update_one, hω3]
    let D : torSU K := ⟨⟨TauCeti.diagGL t, diagGL_mem_SU_of_prod_eq_one hK htprod⟩,
      diagGL_mem_torSU_of_prod_eq_one hK htprod⟩
    have hDparam : torParamHom (K := K) D = t := torParamHom_eq_of_diagGL_eq rfl
    have hDa : torParamHom (K := K) D a = 1 := by
      rw [hDparam]
      show Function.update (1 : Fin 6 → Kˣ) c ωu a *
        Function.update (1 : Fin 6 → Kˣ) e (ωu ^ 2) a = 1
      rw [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hea),
        Pi.one_apply, one_mul]
    have hDb : torParamHom (K := K) D b = 1 := by
      rw [hDparam]
      show Function.update (1 : Fin 6 → Kˣ) c ωu b *
        Function.update (1 : Fin 6 → Kˣ) e (ωu ^ 2) b = 1
      rw [Function.update_of_ne (Ne.symm hcb), Function.update_of_ne (Ne.symm heb),
        Pi.one_apply, one_mul]
    have hDc : torParamHom (K := K) D c = ωu := by
      rw [hDparam]
      show Function.update (1 : Fin 6 → Kˣ) c ωu c *
        Function.update (1 : Fin 6 → Kˣ) e (ωu ^ 2) c = ωu
      rw [Function.update_self, Function.update_of_ne (Ne.symm hec), Pi.one_apply, mul_one]
    have hDσc : torParamHom (K := K) D (σ c) = 1 := by
      rw [hDparam]
      show Function.update (1 : Fin 6 → Kˣ) c ωu (σ c) *
        Function.update (1 : Fin 6 → Kˣ) e (ωu ^ 2) (σ c) = 1
      rw [Function.update_of_ne hne, Function.update_of_ne (Ne.symm heσc), Pi.one_apply, one_mul]
    have hpair : D ∈ torPairEq (K := K) a b := by
      rw [mem_torPairEq, hDa, hDb]
    have hfix' : D ∈ torFix (K := K) σ := by
      rw [heq]
      exact hpair
    have h := (mem_torFix (K := K)).mp hfix' c
    rw [hDσc, hDc] at h
    exact hωu_ne h.symm
  ext x
  by_cases hxa : x = a
  · rw [hxa, hσa, Equiv.swap_apply_left]
  · by_cases hxb : x = b
    · rw [hxb, hσb, Equiv.swap_apply_right]
    · rw [hfixed x hxa hxb, Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem exists_mem_normalizer_conj_eq_tZero' (hK : Nat.card K = 4)
    {u : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hu : u ∈ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))))
    (hu2 : orderOf u = 2) (hfix : Nat.card ↥(torU K ⊓ Subgroup.centralizer {u}) = 3 ^ 3) :
    ∃ g ∈ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))),
      g * u * g⁻¹ = tZero hK := by
  haveI : Finite K := finite_of_card_eq_four hK
  classical
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) u
  have hgN : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) g ∈
      Subgroup.normalizer
        (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by
    rw [hg]
    exact hu
  obtain ⟨d, σ, hmon⟩ := exists_diagGL_mul_permutationGL_of_mem_normalizer hK hgN
  have hu_sq : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu2] at h
    simpa [pow_two] using h
  obtain ⟨c, hgg⟩ : ∃ c : Kˣ, (g : GL (Fin 6) K) * (g : GL (Fin 6) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    have h1 : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
        (1 : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (g * g) := by
      rw [map_mul, hg, hu_sq, map_one]
    obtain ⟨c, hc⟩ := (proj_eq_iff_exists_scalar hK
      (A := (1 : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) (B := g * g)).mp h1
    refine ⟨c, ?_⟩
    rw [show ((1 : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) = 1 from rfl,
      mul_one] at hc
    rwa [show ((g * g : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) =
      (g : GL (Fin 6) K) * (g : GL (Fin 6) K) from rfl] at hc
  have hσ : σ * σ = 1 := by
    refine permutation_mul_self_eq_one_of_monomial_sq hK (d := d) (σ := σ) (c := c) ?_
    rw [← hmon]
    exact hgg
  have hC : torU K ⊓ Subgroup.centralizer {u} =
      (torFix (K := K) σ).map
        ((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).comp (torSU K).subtype) := by
    rw [← hg]
    exact inf_centralizer_eq_map_torFix hK hmon hσ
  have hcardfix : Nat.card ↥(torFix (K := K) σ) = 3 ^ 4 :=
    card_torFix hK σ (hC ▸ hfix)
  have hσne : σ ≠ 1 := by
    intro h1
    have htop : torFix (K := K) σ = ⊤ := by
      ext D
      rw [mem_torFix]
      simp [h1]
    rw [htop, Subgroup.card_top, card_torSU hK] at hcardfix
    norm_num at hcardfix
  obtain ⟨a, ha⟩ : ∃ a : Fin 6, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσne (Equiv.ext h)
  obtain ⟨b, hb⟩ : ∃ b : Fin 6, σ a = b := ⟨_, rfl⟩
  have hab : a ≠ b := by
    intro h
    exact ha (hb ▸ h.symm)
  have hle : torFix (K := K) σ ≤ torPairEq (K := K) a b := by
    intro D hD
    rw [mem_torPairEq]
    have h := (mem_torFix (K := K)).mp hD a
    rw [hb] at h
    exact h.symm
  have hFixEq : torFix (K := K) σ = torPairEq (K := K) a b := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_torPairEq hK hab, hcardfix]
  have hσswap : σ = Equiv.swap a b :=
    eq_swap_of_torFix_eq hK hσ hab hb hFixEq
  obtain ⟨ρ, hρa, hρb⟩ := CFSG.SeitzReduction.LinearPilot.exists_perm_apply_eq_apply_eq
    (n := 6) (a := a) (b := b) (c := 0) (d := 1) hab (by norm_num : (0 : Fin 6) ≠ 1)
  have hρσ : ρ * σ * ρ⁻¹ = Equiv.swap (0 : Fin 6) 1 := by
    rw [hσswap, ← Equiv.swap_apply_apply ρ a b, hρa, hρb]
  obtain ⟨Pρ, hPρ⟩ : ∃ Pρ : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)), Pρ = permGLSU hK ρ := ⟨_, rfl⟩
  obtain ⟨Pσ, hPσ⟩ : ∃ Pσ : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)), Pσ = permGLSU hK σ := ⟨_, rfl⟩
  obtain ⟨Dd, hDd⟩ : ∃ Dd : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)), Dd = g * Pσ⁻¹ := ⟨_, rfl⟩
  have hPσGL : (Pσ : GL (Fin 6) K) = TauCeti.permutationGL σ := by
    rw [hPσ]; exact coe_permGLSU hK σ
  have hDdGL : TauCeti.diagGL d = (Dd : GL (Fin 6) K) := by
    rw [hDd, Subgroup.coe_mul, Subgroup.coe_inv, hPσGL, hmon]
    group
  have hDdtor : Dd ∈ torSU K := by
    rw [torSU, Subgroup.mem_comap]
    exact TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, hDdGL⟩
  have hg_eq : g = Dd * Pσ := by
    calc g = g * Pσ⁻¹ * Pσ := by group
      _ = Dd * Pσ := by rw [← hDd]
  have hPPconj : Pρ * Pσ * Pρ⁻¹ = permGLSU hK (Equiv.swap 0 1) := by
    rw [hPρ, hPσ, ← permGLSU_inv hK ρ, permGLSU_mul, permGLSU_mul, hρσ]
  have hEtor : Pρ * Dd * Pρ⁻¹ ∈ torSU K := by
    rw [hPρ]
    exact permGLSU_mul_mem_torSU hK ρ hDdtor
  obtain ⟨E, hE⟩ : ∃ E : torSU K,
      (E : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = Pρ * Dd * Pρ⁻¹ := ⟨⟨_, hEtor⟩, rfl⟩
  have hh : Pρ * g * Pρ⁻¹ =
      (E : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * tZeroSU hK := by
    rw [hg_eq, tZeroSU_eq_permGLSU]
    have h1 : Pρ * (Dd * Pσ) * Pρ⁻¹ =
        (Pρ * Dd * Pρ⁻¹) * (Pρ * Pσ * Pρ⁻¹) := by group
    rw [h1, ← hE, hPPconj]
  let w : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := permU hK ρ
  have hwN : w ∈ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) :=
    permU_mem_normalizer_torU hK ρ
  have hwP : w = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) Pρ := by
    show LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (permGLSU hK ρ) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) Pρ
    rw [← hPρ]
  let u' : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := w * u * w⁻¹
  have hu'2 : orderOf u' = 2 := by
    have hsc : SemiconjBy w u u' := by
      show w * u = u' * w
      rw [show u' = w * u * w⁻¹ from rfl]
      group
    have h := SemiconjBy.orderOf_eq w hsc
    rw [hu2] at h
    exact h.symm
  have hu'eq : u' = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (Pρ * g * Pρ⁻¹) := by
    show w * u * w⁻¹ = _
    rw [hwP, ← hg, ← map_mul, ← map_inv, ← map_mul]
  have hu'eq2 : u' = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
      (E : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * tZero hK := by
    rw [hu'eq, hh, map_mul]
    rfl
  have hu'X : u' ∈ torU K ⊔ Subgroup.zpowers (tZero hK) := by
    rw [hu'eq2]
    refine Subgroup.mul_mem _ ?_ ?_
    · exact Subgroup.mem_sup_left
        (Subgroup.mem_map.mpr ⟨E, E.2, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (tZero hK))
  obtain ⟨X, hX⟩ : ∃ X : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
      X = torU K ⊔ Subgroup.zpowers (tZero hK) := ⟨_, rfl⟩
  have hu'X' : u' ∈ X := hX ▸ hu'X
  haveI : Finite ↥X := Subtype.finite
  have hX0 : tZero hK ∈ X := by
    rw [hX]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (tZero hK))
  have hXleN : X ≤ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by
    rw [hX]
    exact sup_le Subgroup.le_normalizer
      (Subgroup.zpowers_le.mpr (tZero_mem_normalizer_torU hK))
  have hcardX : Nat.card ↥X = 2 * 81 := by
    have hlep : Subgroup.zpowers (tZero hK) ≤
        Subgroup.normalizer (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) :=
      Subgroup.zpowers_le.mpr (tZero_mem_normalizer_torU hK)
    have hcoe : (↑X : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) =
        (↑(Subgroup.zpowers (tZero hK)) :
          Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) *
          ((↑(torU K) : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) := by
      rw [hX, sup_comm]
      exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hlep
    have hinf : Subgroup.zpowers (tZero hK) ⊓ torU K = ⊥ := by
      apply Subgroup.inf_eq_bot_of_coprime
      rw [Nat.card_zpowers, orderOf_tZero hK, card_torU hK]
      norm_num
    let f : ↥(Subgroup.zpowers (tZero hK)) × ↥(torU K) → ↥X := fun x =>
      ⟨x.1.1 * x.2.1, by
        rw [hX]
        exact mul_mem (Subgroup.mem_sup_right x.1.2) (Subgroup.mem_sup_left x.2.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨⟨z1, hz1⟩, ⟨x1, hx1⟩⟩ ⟨⟨z2, hz2⟩, ⟨x2, hx2⟩⟩ heq
        have heq' : z1 * x1 = z2 * x2 := congrArg Subtype.val heq
        have hmem : z2⁻¹ * z1 ∈ Subgroup.zpowers (tZero hK) ⊓ torU K := by
          refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hz2) hz1, ?_⟩
          have h1 : z2⁻¹ * z1 = x2 * x1⁻¹ := by
            calc z2⁻¹ * z1 = z2⁻¹ * (z1 * x1) * x1⁻¹ := by group
              _ = z2⁻¹ * (z2 * x2) * x1⁻¹ := by rw [heq']
              _ = x2 * x1⁻¹ := by group
          rw [h1]
          exact Subgroup.mul_mem _ hx2 (Subgroup.inv_mem _ hx1)
        rw [hinf, Subgroup.mem_bot] at hmem
        have hz : z1 = z2 := (inv_mul_eq_one.mp hmem).symm
        have hx : x1 = x2 := by
          rw [hz] at heq'
          exact mul_left_cancel heq'
        exact Prod.ext (Subtype.ext hz) (Subtype.ext hx)
      · intro y
        have hy : (y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) ∈
            (↑(Subgroup.zpowers (tZero hK)) :
              Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) *
              ((↑(torU K) : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) := by
          rw [← hcoe]
          exact y.2
        obtain ⟨z, hz, x, hx, hzx⟩ := hy
        exact ⟨(⟨z, hz⟩, ⟨x, hx⟩), Subtype.ext hzx⟩
    have hcard := Nat.card_congr (Equiv.ofBijective f hf)
    rw [← hcard, Nat.card_prod, Nat.card_zpowers, orderOf_tZero hK, card_torU hK]
    norm_num
  have h4 : ¬ 2 ^ 2 ∣ Nat.card ↥X := by
    rw [hcardX]
    norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen2 : orderOf (⟨tZero hK, hX0⟩ : ↥X) = 2 := by
    rw [Subgroup.orderOf_mk, orderOf_tZero hK]
  have hu'X2 : orderOf (⟨u', hu'X'⟩ : ↥X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hu'2
  obtain ⟨y, hy⟩ := TauCeti.exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd
    (p := 2) (G := ↥X) (g := ⟨tZero hK, hX0⟩) (h := ⟨u', hu'X'⟩) h4 hgen2 hu'X2
  have hyz : y * (⟨u', hu'X'⟩ : ↥X) * y⁻¹ ∈ Subgroup.zpowers (⟨tZero hK, hX0⟩ : ↥X) := hy
  have hord : orderOf (y * (⟨u', hu'X'⟩ : ↥X) * y⁻¹) = 2 := by
    have hsc : SemiconjBy y (⟨u', hu'X'⟩ : ↥X) (y * (⟨u', hu'X'⟩ : ↥X) * y⁻¹) := by
      show y * (⟨u', hu'X'⟩ : ↥X) = (y * (⟨u', hu'X'⟩ : ↥X) * y⁻¹) * y
      group
    have h := SemiconjBy.orderOf_eq y hsc
    rw [hu'X2] at h
    exact h.symm
  have hne1 : y * (⟨u', hu'X'⟩ : ↥X) * y⁻¹ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  rw [Subgroup.mem_zpowers_iff] at hyz
  obtain ⟨k, hk⟩ := hyz
  have hgen2' : (⟨tZero hK, hX0⟩ : ↥X) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (⟨tZero hK, hX0⟩ : ↥X)
    rwa [hgen2] at h
  have hk' : (⟨tZero hK, hX0⟩ : ↥X) ^ k =
      (⟨tZero hK, hX0⟩ : ↥X) ^ (k % 2) := zpow_eq_zpow_emod' k hgen2'
  have hconjX : y * (⟨u', hu'X'⟩ : ↥X) * y⁻¹ = ⟨tZero hK, hX0⟩ := by
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exact absurd (by rw [← hk, hk', h0, zpow_zero]) hne1
    · rw [← hk, hk', h1, zpow_one]
  have hconjU : (y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * u' *
      (y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))⁻¹ = tZero hK := by
    have h := congrArg
      (fun z : ↥X => (z : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) hconjX
    simpa using h
  refine ⟨(y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * w, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (hXleN y.2) hwN
  · calc ((y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * w) * u *
          ((y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * w)⁻¹ =
        (y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * (w * u * w⁻¹) *
          (y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))⁻¹ := by group
    _ = (y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * u' *
          (y : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))⁻¹ := by
        rw [show u' = w * u * w⁻¹ from rfl]
    _ = tZero hK := hconjU

theorem exists_conj_eq_tZero (hK : Nat.card K = 4)
    {u : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hu : u ∈ Subgroup.normalizer
      (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))))
    (hu2 : orderOf u = 2) (hfix : Nat.card ↥(torU K ⊓ Subgroup.centralizer {u}) = 3 ^ 3) :
    ∃ g : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)), g * u * g⁻¹ = tZero hK := by
  obtain ⟨g, -, hg⟩ := exists_mem_normalizer_conj_eq_tZero' hK hu hu2 hfix
  exact ⟨g, hg⟩

end CFSG.StandardType.USixTwo

end
