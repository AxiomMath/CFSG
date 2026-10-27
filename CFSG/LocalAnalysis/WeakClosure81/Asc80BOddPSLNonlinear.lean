module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSL
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSLField
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSLGraphUnip
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSLGraphFieldUnip
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSLOrthSplit
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSLOrthNonsplit
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSLOrthGen
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LieType.SeitzGeneration.OuterNarrowClassical
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.WeakClosure81.FiveFive
public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSLOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma matrix_scalar_eq_smul_one {K : Type*} [Semiring K] {m : Type*}
    [Fintype m] [DecidableEq m] (a : K) :
    Matrix.scalar m a = a • (1 : Matrix m m K) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

private lemma map_nonsing_inv {K : Type*} [Field K] {n : ℕ} (σ : K ≃+* K)
    {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det) :
    M⁻¹.map σ = (M.map σ)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  calc M.map σ * M⁻¹.map σ = (M * M⁻¹).map σ := by rw [Matrix.map_mul]
    _ = (1 : Matrix (Fin n) (Fin n) K).map σ := by rw [Matrix.mul_nonsing_inv M hM]
    _ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)

private lemma mul_standard_form_dualAut {n : ℕ} {F : Type} [Field F]
    (B B' : GL (Fin n) F) (σ σ' : F ≃+* F) :
    (conjAut n F B * fieldAut n F σ * dualAut n F) *
      (conjAut n F B' * fieldAut n F σ' * dualAut n F) =
    conjAut n F (B * GeneralLinearGroup.map (σ : F →+* F)
      (GeneralLinearGroup.inverseTranspose B')) * fieldAut n F (σ * σ') := by
  have hdd : dualAut n F * dualAut n F = 1 :=
    (standard_automorphism_transport (K := F) (n := n)).2.2.2.1
  calc (conjAut n F B * fieldAut n F σ * dualAut n F) *
        (conjAut n F B' * fieldAut n F σ' * dualAut n F)
      = conjAut n F B * fieldAut n F σ *
          (dualAut n F * conjAut n F B') * fieldAut n F σ' * dualAut n F := by group
    _ = conjAut n F B * fieldAut n F σ *
          (conjAut n F (GeneralLinearGroup.inverseTranspose B') * dualAut n F) *
            fieldAut n F σ' * dualAut n F := by rw [dualAut_mul_conjAut]
    _ = conjAut n F B * (fieldAut n F σ *
          conjAut n F (GeneralLinearGroup.inverseTranspose B')) *
            (dualAut n F * fieldAut n F σ') * dualAut n F := by group
    _ = conjAut n F B * (conjAut n F (GeneralLinearGroup.map (σ : F →+* F)
          (GeneralLinearGroup.inverseTranspose B')) * fieldAut n F σ) *
            (fieldAut n F σ' * dualAut n F) * dualAut n F := by
          rw [fieldAut_mul_conjAut, dualAut_mul_fieldAut]
    _ = conjAut n F B * conjAut n F (GeneralLinearGroup.map (σ : F →+* F)
          (GeneralLinearGroup.inverseTranspose B')) *
            (fieldAut n F σ * fieldAut n F σ') * (dualAut n F * dualAut n F) := by
          group
    _ = conjAut n F (B * GeneralLinearGroup.map (σ : F →+* F)
          (GeneralLinearGroup.inverseTranspose B')) * fieldAut n F (σ * σ') := by
          rw [hdd, map_mul, map_mul, mul_one]

theorem graphField_proj_eq_of_isometry {F : Type} [Field F] {n : ℕ} (Φ : GL (Fin n) F)
    (σ : F ≃+* F) (X : SpecialLinearGroup (Fin n) F)
    (hX : ((X : Matrix (Fin n) (Fin n) F).map σ)ᵀ * Φ * X = Φ) :
    (conjAut n F Φ⁻¹ * fieldAut n F σ * dualAut n F) (proj n F X) = proj n F X := by
  classical
  have hmapGL : ∀ Y : GL (Fin n) F,
      ((GeneralLinearGroup.map (σ : F →+* F) Y : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = (Y : Matrix (Fin n) (Fin n) F).map σ := fun _ => rfl
  set x : Matrix (Fin n) (Fin n) F := (X : Matrix (Fin n) (Fin n) F) with hx
  have hxdet : x.det = 1 := by rw [hx]; exact X.2
  have hxdetu : IsUnit x.det := by rw [hxdet]; exact isUnit_one
  have hΦdetu : IsUnit ((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det :=
    Matrix.isUnits_det_units Φ
  have hΦinv : ((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)⁻¹ *
      ((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 :=
    Matrix.nonsing_inv_mul _ hΦdetu
  have hΦinv' : ((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hΦdetu
  set T : Matrix (Fin n) (Fin n) F := (x.map σ)ᵀ with hT
  have hXT : T * (Φ : Matrix (Fin n) (Fin n) F) * x = (Φ : Matrix (Fin n) (Fin n) F) := by
    simpa [hT, hx] using hX
  have h1 : T * (Φ : Matrix (Fin n) (Fin n) F) =
      (Φ : Matrix (Fin n) (Fin n) F) * x⁻¹ := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M * x⁻¹) hXT
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv x hxdetu, Matrix.mul_one] at h
  have hT_eq : T = (Φ : Matrix (Fin n) (Fin n) F) * x⁻¹ *
      ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ := by
    calc T = T * ((Φ : Matrix (Fin n) (Fin n) F) * ((Φ : Matrix (Fin n) (Fin n) F))⁻¹) := by
          rw [hΦinv', Matrix.mul_one]
      _ = (T * (Φ : Matrix (Fin n) (Fin n) F)) * ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ := by
          rw [Matrix.mul_assoc]
      _ = ((Φ : Matrix (Fin n) (Fin n) F) * x⁻¹) *
            ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ := by rw [h1]
  have hTinv : T⁻¹ = (Φ : Matrix (Fin n) (Fin n) F) * x *
      ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ := by
    have hxinvinv : (x⁻¹)⁻¹ = x := Matrix.inv_eq_left_inv (Matrix.mul_nonsing_inv x hxdetu)
    have hΦinvinv : (((Φ : Matrix (Fin n) (Fin n) F))⁻¹)⁻¹ = (Φ : Matrix (Fin n) (Fin n) F) :=
      Matrix.inv_eq_left_inv hΦinv'
    rw [hT_eq, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hΦinvinv, hxinvinv,
      Matrix.mul_assoc]
  have hxmap_inv : (x⁻¹).map σ = (x.map σ)⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    calc (x.map σ) * (x⁻¹).map σ = (x * x⁻¹).map σ := by rw [Matrix.map_mul]
      _ = (1 : Matrix (Fin n) (Fin n) F).map σ := by rw [Matrix.mul_nonsing_inv x hxdetu]
      _ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)
  have hT_eq : (x⁻¹)ᵀ.map σ = T⁻¹ := by
    rw [Matrix.transpose_map, hxmap_inv, Matrix.transpose_nonsing_inv, hT]
  have hxadj : x⁻¹ = x.adjugate := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.adjugate_mul, hxdet, one_smul]
  have hmat : ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ * (x⁻¹)ᵀ.map σ *
      (Φ : Matrix (Fin n) (Fin n) F) = x := by
    rw [hT_eq, hTinv]
    calc ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ *
          ((Φ : Matrix (Fin n) (Fin n) F) * x *
            ((Φ : Matrix (Fin n) (Fin n) F))⁻¹) * (Φ : Matrix (Fin n) (Fin n) F)
        = (((Φ : Matrix (Fin n) (Fin n) F))⁻¹ *
            (Φ : Matrix (Fin n) (Fin n) F)) * (x *
              (((Φ : Matrix (Fin n) (Fin n) F))⁻¹ *
                (Φ : Matrix (Fin n) (Fin n) F))) := by noncomm_ring
      _ = x := by rw [hΦinv, Matrix.one_mul, Matrix.mul_one]
  have hSL : (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F Φ⁻¹
      (SpecialLinearGroup.map (σ : F →+* F) (X⁻¹).transpose)) = X := by
    apply Subtype.ext
    rw [coe_slConjugation]
    rw [show (Φ⁻¹ : GL (Fin n) F)⁻¹ = Φ from inv_inv Φ]
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
      GeneralLinearGroup.coe_inv]
    rw [← hxadj]
    exact hmat
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]
  exact congrArg (proj n F) hSL

theorem exists_graph_pair_of_not_semilinear {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 3 ≤ n) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (hNL : ¬ E ≤ linearAutGroup n F)
    (hsemi : ∀ e ∈ E, e ∈ semilinearAutGroup n F → e ∈ linearAutGroup n F) :
    ∃ (A Φ : GL (Fin n) F) (σ : F ≃+* F) (μ c κ : F),
      E = Subgroup.zpowers (conjAut n F A) ⊔
        Subgroup.zpowers (conjAut n F Φ⁻¹ * fieldAut n F σ * dualAut n F) ∧
      σ * σ = 1 ∧ (A : Matrix (Fin n) (Fin n) F) * A = μ • 1 ∧
      (∀ d : F, (A : Matrix (Fin n) (Fin n) F) ≠ d • 1) ∧
      (Φ : Matrix (Fin n) (Fin n) F) = c • ((Φ : Matrix (Fin n) (Fin n) F).map σ)ᵀ ∧
      ((A : Matrix (Fin n) (Fin n) F).map σ)ᵀ * Φ * A = κ • (Φ : Matrix (Fin n) (Fin n) F) := by
  classical
  have h4' : Nat.card E = 2 ^ 2 := by rw [h4]; norm_num
  obtain ⟨t₀, ht₀E, ht₀L⟩ : ∃ t₀ ∈ E, t₀ ∉ linearAutGroup n F := by
    by_contra h
    push Not at h
    exact hNL h
  have ht₀S : t₀ ∉ semilinearAutGroup n F := fun h => ht₀L (hsemi t₀ ht₀E h)
  have ht₀1 : t₀ ≠ 1 := fun h => ht₀L (h ▸ Subgroup.one_mem _)
  have ht₀sq : t₀ * t₀ = 1 := by
    have h := hE.2 t₀ ht₀E
    simpa [pow_two] using h
  have ht₀inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀sq
  obtain ⟨B, σ, ε, hε, ht₀form⟩ := (automorphism_generation (K := F) hn).2 t₀
  have hε1 : ε = 1 := by
    rcases (by omega : ε = 0 ∨ ε = 1) with h | h
    · exfalso
      apply ht₀S
      rw [ht₀form, h, pow_zero, mul_one]
      exact mem_semilinearAutGroup_iff.mpr ⟨B, σ, rfl⟩
    · exact h
  have ht₀' : t₀ = conjAut n F B * fieldAut n F σ * dualAut n F := by
    rw [ht₀form, hε1, pow_one]
  obtain ⟨x, hxE, hxz⟩ :=
    exists_notMem_zpowers_of_card_sq Nat.prime_two hE.2 h4' ht₀E ht₀1
  have hx1 : x ≠ 1 := fun h => hxz (by rw [h]; exact Subgroup.one_mem _)
  have hu_exists : ∃ u ∈ E, u ∈ linearAutGroup n F ∧ u ≠ 1 := by
    by_cases hxsemi : x ∈ semilinearAutGroup n F
    · exact ⟨x, hxE, hsemi x hxE hxsemi, hx1⟩
    · obtain ⟨B', σ', ε', hε', hxform⟩ := (automorphism_generation (K := F) hn).2 x
      have hε'1 : ε' = 1 := by
        rcases (by omega : ε' = 0 ∨ ε' = 1) with h | h
        · exfalso
          apply hxsemi
          rw [hxform, h, pow_zero, mul_one]
          exact mem_semilinearAutGroup_iff.mpr ⟨B', σ', rfl⟩
        · exact h
      have hx' : x = conjAut n F B' * fieldAut n F σ' * dualAut n F := by
        rw [hxform, hε'1, pow_one]
      have hprodSemi : t₀ * x ∈ semilinearAutGroup n F := by
        rw [ht₀', hx']
        exact mem_semilinearAutGroup_iff.mpr
          ⟨_, _, mul_standard_form_dualAut B B' σ σ'⟩
      have hprod1 : t₀ * x ≠ 1 := by
        intro h
        apply hxz
        have h1 : x = t₀ := by
          have h2 : x = t₀⁻¹ := eq_inv_of_mul_eq_one_right h
          rwa [ht₀inv] at h2
        rw [h1]
        exact Subgroup.mem_zpowers t₀
      exact ⟨t₀ * x, mul_mem ht₀E hxE,
        hsemi _ (mul_mem ht₀E hxE) hprodSemi, hprod1⟩
  obtain ⟨u, huE, huLin, hu1⟩ := hu_exists
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp huLin
  have hnotzp : t₀ ∉ Subgroup.zpowers u := by
    intro h
    exact ht₀L ((Subgroup.zpowers_le.mpr huLin) h)
  have hgen0 : E = Subgroup.zpowers u ⊔ Subgroup.zpowers t₀ :=
    (zpowers_sup_zpowers_eq_of_card_sq Nat.prime_two hE.2 h4' huE hu1 ht₀E hnotzp).symm
  let Φ : GL (Fin n) F := B⁻¹
  have ht₀Φ : conjAut n F Φ⁻¹ * fieldAut n F σ * dualAut n F = t₀ := by
    rw [show Φ⁻¹ = B from by simp [Φ], ht₀']
  have hgen : E = Subgroup.zpowers (conjAut n F A) ⊔
      Subgroup.zpowers (conjAut n F Φ⁻¹ * fieldAut n F σ * dualAut n F) := by
    rw [hA, ht₀Φ]
    exact hgen0
  have hu2 : u * u = 1 := by
    have h := hE.2 u huE
    simpa [pow_two] using h
  have hA2eq : conjAut n F (A * A) = 1 := by
    rw [map_mul, hA]
    exact hu2
  obtain ⟨c₀, hc₀⟩ :=
    (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn (A * A)).mp hA2eq
  have hA2 : (A : Matrix (Fin n) (Fin n) F) * A = (c₀ : F) • 1 := by
    have h := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hc₀
    rw [GeneralLinearGroup.coe_scalar, Units.val_mul, matrix_scalar_eq_smul_one] at h
    exact h.symm
  have hAne : conjAut n F A ≠ 1 := by
    rw [hA]
    exact hu1
  have hAscal : ∀ d : F, (A : Matrix (Fin n) (Fin n) F) ≠ d • 1 :=
    fun d => CFSG.LocalAnalysis.WeakClosure81.LinSeitz.coe_ne_smul_one_of_conjAut_ne_one
      hn hAne d
  have hsq : (conjAut n F B * fieldAut n F σ * dualAut n F) ^ 2 = 1 := by
    rw [← ht₀', pow_two]
    exact ht₀sq
  rw [sq_conjAut_fieldAut_dualAut] at hsq
  obtain ⟨hσ2, c₁, hc₁⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ hsq
  have hmapGL : ∀ Y : GL (Fin n) F,
      ((GeneralLinearGroup.map (σ : F →+* F) Y : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = (Y : Matrix (Fin n) (Fin n) F).map σ := fun _ => rfl
  have hBunit : IsUnit ((B : Matrix (Fin n) (Fin n) F).det) := Matrix.isUnits_det_units B
  have hΦcoe : (Φ : Matrix (Fin n) (Fin n) F) = ((B : Matrix (Fin n) (Fin n) F))⁻¹ := by
    simp [Φ]
  have hBtunit : IsUnit (((B : Matrix (Fin n) (Fin n) F))ᵀ).det := by
    rwa [Matrix.det_transpose]
  have hBmat : (B : Matrix (Fin n) (Fin n) F) *
      (((((B : Matrix (Fin n) (Fin n) F)).map σ)ᵀ))⁻¹ = (c₁ : F) • 1 := by
    have h := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hc₁
    rw [GeneralLinearGroup.coe_scalar, Units.val_mul, matrix_scalar_eq_smul_one] at h
    rw [hmapGL, GeneralLinearGroup.coe_inverseTranspose, GeneralLinearGroup.coe_inv,
      Matrix.transpose_nonsing_inv] at h
    rw [map_nonsing_inv σ hBtunit, Matrix.transpose_map] at h
    exact h.symm
  have hΦB : (Φ : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [hΦcoe]
    exact Matrix.nonsing_inv_mul (A := (B : Matrix (Fin n) (Fin n) F)) hBunit
  have hΦmap : (((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ)ᵀ =
      (((((B : Matrix (Fin n) (Fin n) F)).map σ)ᵀ))⁻¹ := by
    rw [hΦcoe, map_nonsing_inv σ hBunit, Matrix.transpose_nonsing_inv]
  have hΦT : (((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ)ᵀ =
      (c₁ : F) • (Φ : Matrix (Fin n) (Fin n) F) := by
    rw [hΦmap]
    calc (((((B : Matrix (Fin n) (Fin n) F)).map σ)ᵀ))⁻¹
        = ((Φ : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
            (((((B : Matrix (Fin n) (Fin n) F)).map σ)ᵀ))⁻¹ := by
          rw [hΦB, Matrix.one_mul]
      _ = (Φ : Matrix (Fin n) (Fin n) F) *
            ((B : Matrix (Fin n) (Fin n) F) *
              (((((B : Matrix (Fin n) (Fin n) F)).map σ)ᵀ))⁻¹) := by
          rw [Matrix.mul_assoc]
      _ = (Φ : Matrix (Fin n) (Fin n) F) * ((c₁ : F) • 1) := by rw [hBmat]
      _ = (c₁ : F) • (Φ : Matrix (Fin n) (Fin n) F) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
  have hΦherm : (Φ : Matrix (Fin n) (Fin n) F) = (c₁ : F)⁻¹ •
      (((Φ : Matrix (Fin n) (Fin n) F)).map σ)ᵀ := by
    rw [hΦT, smul_smul, inv_mul_cancel₀ c₁.ne_zero, one_smul]
  have hcomm : u * t₀ = t₀ * u := by
    simpa using hE.1.is_comm.comm ⟨u, huE⟩ ⟨t₀, ht₀E⟩
  have hL : u * t₀ = conjAut n F (A * Φ⁻¹) * fieldAut n F σ * dualAut n F := by
    rw [← ht₀Φ, ← hA, map_mul]
    group
  have hR : t₀ * u =
      conjAut n F (Φ⁻¹ * GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose A)) * fieldAut n F σ * dualAut n F := by
    rw [← ht₀Φ, ← hA]
    calc conjAut n F Φ⁻¹ * fieldAut n F σ * dualAut n F * conjAut n F A
        = conjAut n F Φ⁻¹ * fieldAut n F σ * (dualAut n F * conjAut n F A) := by group
      _ = conjAut n F Φ⁻¹ * fieldAut n F σ *
            (conjAut n F (GeneralLinearGroup.inverseTranspose A) * dualAut n F) := by
          rw [dualAut_mul_conjAut]
      _ = conjAut n F Φ⁻¹ * (fieldAut n F σ *
            conjAut n F (GeneralLinearGroup.inverseTranspose A)) * dualAut n F := by group
      _ = conjAut n F Φ⁻¹ * (conjAut n F (GeneralLinearGroup.map (σ : F →+* F)
            (GeneralLinearGroup.inverseTranspose A)) * fieldAut n F σ) * dualAut n F := by
          rw [fieldAut_mul_conjAut]
      _ = conjAut n F (Φ⁻¹ * GeneralLinearGroup.map (σ : F →+* F)
            (GeneralLinearGroup.inverseTranspose A)) * fieldAut n F σ * dualAut n F := by
          rw [map_mul]
          group
  have hconj : conjAut n F (A * Φ⁻¹) =
      conjAut n F (Φ⁻¹ * GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose A)) := by
    have hformeq : conjAut n F (A * Φ⁻¹) * fieldAut n F σ * dualAut n F =
        conjAut n F (Φ⁻¹ * GeneralLinearGroup.map (σ : F →+* F)
          (GeneralLinearGroup.inverseTranspose A)) * fieldAut n F σ * dualAut n F := by
      rw [← hL, ← hR]
      exact hcomm
    exact mul_right_cancel (mul_right_cancel hformeq)
  have hZ : conjAut n F ((A * Φ⁻¹)⁻¹ * (Φ⁻¹ * GeneralLinearGroup.map (σ : F →+* F)
      (GeneralLinearGroup.inverseTranspose A))) = 1 := by
    rw [map_mul, map_inv, hconj]
    group
  obtain ⟨e, he⟩ :=
    (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn _).mp hZ
  let S : Matrix (Fin n) (Fin n) F := (((A : Matrix (Fin n) (Fin n) F))ᵀ)⁻¹.map σ
  have hAunit : IsUnit ((A : Matrix (Fin n) (Fin n) F).det) := Matrix.isUnits_det_units A
  have hAtunit : IsUnit (((A : Matrix (Fin n) (Fin n) F))ᵀ.det) := by
    rwa [Matrix.det_transpose]
  have hTdet : IsUnit (((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ).det) := by
    rw [Matrix.det_transpose, ← RingEquiv.mapMatrix_apply, ← RingEquiv.map_det]
    exact IsUnit.map (σ : F →+* F) hAunit
  have hS_eq : S = ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ)⁻¹ := by
    rw [show S = ((((A : Matrix (Fin n) (Fin n) F))ᵀ)⁻¹.map σ) from rfl,
      map_nonsing_inv σ hAtunit, Matrix.transpose_map]
  have hSinv : S * ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ) = 1 := by
    rw [hS_eq, Matrix.nonsing_inv_mul _ hTdet]
  have hΦinvinv : (((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))⁻¹⁻¹ =
      (Φ : Matrix (Fin n) (Fin n) F) :=
    Matrix.inv_eq_left_inv (A := ((Φ : Matrix (Fin n) (Fin n) F))⁻¹)
      (B := (Φ : Matrix (Fin n) (Fin n) F)) (Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units Φ))
  have hΦinv : (((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))⁻¹ *
      ((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 :=
    Matrix.nonsing_inv_mul _ (Matrix.isUnits_det_units Φ)
  have hΦinv' : ((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((Φ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units Φ)
  have hscal : (e : F) • (1 : Matrix (Fin n) (Fin n) F) =
      (Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹ *
        ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ * S := by
    have h := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) he
    simp only [GeneralLinearGroup.coe_scalar, matrix_scalar_eq_smul_one, Units.val_mul,
      GeneralLinearGroup.coe_inv, hmapGL, GeneralLinearGroup.coe_inverseTranspose,
      Matrix.transpose_nonsing_inv, Matrix.mul_inv_rev, hΦinvinv] at h
    calc (e : F) • (1 : Matrix (Fin n) (Fin n) F)
        = (Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹ *
            (((Φ : Matrix (Fin n) (Fin n) F))⁻¹ * S) := h
      _ = (Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹ *
            ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ * S := by noncomm_ring
  have h1 : (e : F) • ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ) =
      (Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹ *
        ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ := by
    calc (e : F) • ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ)
        = ((e : F) • (1 : Matrix (Fin n) (Fin n) F)) *
            ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ) := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = ((Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹ *
            ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ * S) *
              ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ) := by rw [hscal]
      _ = (Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹ *
            ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ * (S *
              ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ)) := by noncomm_ring
      _ = (Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹ *
            ((Φ : Matrix (Fin n) (Fin n) F))⁻¹ := by rw [hSinv, Matrix.mul_one]
  have h2 : (e : F) • ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ *
      (Φ : Matrix (Fin n) (Fin n) F)) = (Φ : Matrix (Fin n) (Fin n) F) *
        ((A : Matrix (Fin n) (Fin n) F))⁻¹ := by
    calc (e : F) • ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ *
          (Φ : Matrix (Fin n) (Fin n) F))
        = ((e : F) • ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ)) *
            (Φ : Matrix (Fin n) (Fin n) F) := by rw [Matrix.smul_mul]
      _ = ((Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹ *
            ((Φ : Matrix (Fin n) (Fin n) F))⁻¹) * (Φ : Matrix (Fin n) (Fin n) F) := by
          rw [h1]
      _ = (Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹ := by
          rw [Matrix.mul_assoc, hΦinv, Matrix.mul_one]
  have h3 : (e : F) • ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ *
      (Φ : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) =
        (Φ : Matrix (Fin n) (Fin n) F) := by
    calc (e : F) • ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ *
          (Φ : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F))
        = ((e : F) • ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ *
            (Φ : Matrix (Fin n) (Fin n) F))) * (A : Matrix (Fin n) (Fin n) F) := by
          rw [Matrix.smul_mul]
      _ = ((Φ : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹) *
            (A : Matrix (Fin n) (Fin n) F) := by rw [h2]
      _ = (Φ : Matrix (Fin n) (Fin n) F) := by
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAunit, Matrix.mul_one]
  have h4 : ((((A : Matrix (Fin n) (Fin n) F)).map σ)ᵀ) *
      (Φ : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) =
        (e : F)⁻¹ • (Φ : Matrix (Fin n) (Fin n) F) := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => (e : F)⁻¹ • M) h3
    rw [smul_smul, inv_mul_cancel₀ e.ne_zero, one_smul] at h
    exact h
  exact ⟨A, Φ, σ, (c₀ : F), (c₁ : F)⁻¹, (e : F)⁻¹, hgen, hσ2, hA2, hAscal, hΦherm, h4⟩

private lemma smul_ne_zero_of_mul_self_eq_smul_one {F : Type} [Field F] {n : ℕ} (hn : 3 ≤ n)
    {A : GL (Fin n) F} {μ : F}
    (hA2 : (A : Matrix (Fin n) (Fin n) F) * A = μ • 1) : μ ≠ 0 := by
  intro hμ0
  have hAdet : IsUnit ((A : Matrix (Fin n) (Fin n) F).det) := Matrix.isUnits_det_units A
  have hAA : (A : Matrix (Fin n) (Fin n) F) * A = 0 := by rw [hA2, hμ0, zero_smul]
  have hA0 : (A : Matrix (Fin n) (Fin n) F) = 0 := by
    calc (A : Matrix (Fin n) (Fin n) F)
        = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            ((A : Matrix (Fin n) (Fin n) F) * A) := by
          rw [← Matrix.mul_assoc, GeneralLinearGroup.coe_inv,
            Matrix.nonsing_inv_mul _ hAdet, Matrix.one_mul]
      _ = 0 := by rw [hAA, Matrix.mul_zero]
  have h1 : (1 : Matrix (Fin n) (Fin n) F) = 0 := by
    calc (1 : Matrix (Fin n) (Fin n) F)
        = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (A : Matrix (Fin n) (Fin n) F) := by
          rw [GeneralLinearGroup.coe_inv, Matrix.nonsing_inv_mul _ hAdet]
      _ = 0 := by rw [hA0, Matrix.mul_zero]
  exact one_ne_zero (congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩)

private lemma isometry_one_add {F : Type} [Field F] {n : ℕ} {σ : F ≃+* F}
    {N Φ : Matrix (Fin n) (Fin n) F} (hN2 : N * N = 0)
    (hNΦ : (N.map σ)ᵀ * Φ + Φ * N = 0) :
    (((1 + N : Matrix (Fin n) (Fin n) F).map σ))ᵀ * Φ * (1 + N) = Φ := by
  have hmap : ((1 + N : Matrix (Fin n) (Fin n) F).map σ) = 1 + N.map σ := by
    rw [Matrix.map_add σ (map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hNΦ' : (N.map σ)ᵀ * Φ = -(Φ * N) := eq_neg_of_add_eq_zero_left hNΦ
  have hNΦN : (N.map σ)ᵀ * Φ * N = 0 := by
    calc (N.map σ)ᵀ * Φ * N = ((N.map σ)ᵀ * Φ) * N := rfl
      _ = (-(Φ * N)) * N := by rw [hNΦ']
      _ = -((Φ * N) * N) := by rw [Matrix.neg_mul]
      _ = -(Φ * (N * N)) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hN2, Matrix.mul_zero, neg_zero]
  have hexp : (1 + (N.map σ)ᵀ) * Φ * (1 + N) =
      Φ + ((N.map σ)ᵀ * Φ + Φ * N) + (N.map σ)ᵀ * Φ * N := by
    noncomm_ring
  rw [hmap, Matrix.transpose_add, Matrix.transpose_one, hexp, hNΦ, hNΦN]
  simp

private lemma planeGen_of_sq_zero_commute {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4)
    {A Φ : GL (Fin n) F} {σ : F ≃+* F}
    (hgen : E = Subgroup.zpowers (conjAut n F A) ⊔
      Subgroup.zpowers (conjAut n F Φ⁻¹ * fieldAut n F σ * dualAut n F))
    {N : Matrix (Fin n) (Fin n) F} (hN0 : N ≠ 0) (hN2 : N * N = 0)
    (hAN : (A : Matrix (Fin n) (Fin n) F) * N = N * A)
    (hXiso : (((1 + N : Matrix (Fin n) (Fin n) F).map σ))ᵀ * Φ * (1 + N) = Φ) :
    PlaneGen E := by
  classical
  let X : Matrix (Fin n) (Fin n) F := 1 + N
  have hXdet : X.det = 1 := by
    rw [show X = 1 + N from rfl]
    exact det_one_add_eq_one hN2
  let Xsl : SpecialLinearGroup (Fin n) F := ⟨X, hXdet⟩
  have hXsl : (Xsl : Matrix (Fin n) (Fin n) F) = X := rfl
  have hX1 : (Xsl : Matrix (Fin n) (Fin n) F) ≠ 1 := by
    intro h
    apply hN0
    have h' : (1 : Matrix (Fin n) (Fin n) F) + N = (1 : Matrix (Fin n) (Fin n) F) + 0 := by
      rw [add_zero]
      exact h
    exact add_left_cancel h'
  have hX3 : ((Xsl : Matrix (Fin n) (Fin n) F) - 1) ^ 3 = 0 := by
    have hXsub : (Xsl : Matrix (Fin n) (Fin n) F) - 1 = N := by
      change (1 + N : Matrix (Fin n) (Fin n) F) - 1 = N
      abel
    rw [hXsub]
    calc N ^ 3 = N ^ 2 * N := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
      _ = 0 := by rw [pow_two, hN2, Matrix.zero_mul]
  have hAdet : IsUnit ((A : Matrix (Fin n) (Fin n) F).det) := Matrix.isUnits_det_units A
  have hAX : (A : Matrix (Fin n) (Fin n) F) * X = X * (A : Matrix (Fin n) (Fin n) F) := by
    change (A : Matrix (Fin n) (Fin n) F) * (1 + N) =
      (1 + N) * (A : Matrix (Fin n) (Fin n) F)
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hAN]
  have hfixA : conjAut n F A (proj n F Xsl) = proj n F Xsl := by
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, GeneralLinearGroup.coe_inv]
    have hAX' : (A : Matrix (Fin n) (Fin n) F) * (Xsl : Matrix (Fin n) (Fin n) F) =
        (Xsl : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) := by
      simpa using hAX
    calc (A : Matrix (Fin n) (Fin n) F) * (Xsl : Matrix (Fin n) (Fin n) F) *
          ((A : Matrix (Fin n) (Fin n) F))⁻¹
        = ((Xsl : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) *
            ((A : Matrix (Fin n) (Fin n) F))⁻¹ := by rw [hAX']
      _ = (Xsl : Matrix (Fin n) (Fin n) F) *
            ((A : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F))⁻¹) := by
          rw [Matrix.mul_assoc]
      _ = (Xsl : Matrix (Fin n) (Fin n) F) * 1 := by
          rw [Matrix.mul_nonsing_inv _ hAdet]
      _ = (Xsl : Matrix (Fin n) (Fin n) F) := by rw [Matrix.mul_one]
  have hfixG : (conjAut n F Φ⁻¹ * fieldAut n F σ * dualAut n F) (proj n F Xsl) =
      proj n F Xsl :=
    graphField_proj_eq_of_isometry Φ σ Xsl (by simpa [hXsl] using hXiso)
  have hstab : E ≤ MulAction.stabilizer (MulAut (projectiveSL n F)) (proj n F Xsl) := by
    rw [hgen]
    exact sup_le
      (Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hfixA))
      (Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hfixG))
  have hfix : ∀ e ∈ E, e (proj n F Xsl) = proj n F Xsl := by
    intro e he
    have := hstab he
    simpa [MulAction.mem_stabilizer_iff] using this
  exact planeGen_of_fixed_unipotent hF hE h4 Xsl hX1 hX3 hfix

theorem planeGen_of_graph_orth {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n)
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (A Φ : GL (Fin n) F) {μ : F}
    (hA2 : (A : Matrix (Fin n) (Fin n) F) * A = μ • 1)
    (hAs : ∀ c : F, (A : Matrix (Fin n) (Fin n) F) ≠ c • 1)
    (hΦt : (Φ : Matrix (Fin n) (Fin n) F)ᵀ = Φ)
    (hAΦ : (A : Matrix (Fin n) (Fin n) F)ᵀ * Φ = Φ * A)
    (hgen : E = Subgroup.zpowers (conjAut n F A) ⊔
      Subgroup.zpowers (conjAut n F Φ⁻¹ * dualAut n F)) : PlaneGen E := by
  classical
  have hAdet : IsUnit ((A : Matrix (Fin n) (Fin n) F).det) := Matrix.isUnits_det_units A
  have hΦdet : IsUnit ((Φ : Matrix (Fin n) (Fin n) F).det) := Matrix.isUnits_det_units Φ
  have hμ : μ ≠ 0 := smul_ne_zero_of_mul_self_eq_smul_one hn hA2
  by_cases hsq : IsSquare μ
  · obtain ⟨c, hc⟩ := (isSquare_iff_exists_sq μ).mp hsq
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hμ (by rw [hc]; simp)
    let u : Fˣ := Units.mk0 c⁻¹ (inv_ne_zero hc0)
    let A₀ : GL (Fin n) F := GeneralLinearGroup.scalar (Fin n) u * A
    have hA₀mat : (A₀ : Matrix (Fin n) (Fin n) F) = c⁻¹ • (A : Matrix (Fin n) (Fin n) F) := by
      rw [show A₀ = GeneralLinearGroup.scalar (Fin n) u * A from rfl, Units.val_mul,
        GeneralLinearGroup.coe_scalar, matrix_scalar_eq_smul_one, Matrix.smul_mul,
        Matrix.one_mul, Units.val_mk0]
    have hconjAut : conjAut n F A₀ = conjAut n F A := by
      rw [show A₀ = GeneralLinearGroup.scalar (Fin n) u * A from rfl, map_mul, conjAut_scalar,
        one_mul]
    have hcoef : c⁻¹ * c⁻¹ * μ = 1 := by
      rw [hc]
      field_simp [hc0]
    have hA₀2 : (A₀ : Matrix (Fin n) (Fin n) F) * A₀ = 1 := by
      calc (A₀ : Matrix (Fin n) (Fin n) F) * A₀
          = (c⁻¹ • (A : Matrix (Fin n) (Fin n) F)) *
              (c⁻¹ • (A : Matrix (Fin n) (Fin n) F)) := by rw [hA₀mat]
        _ = (c⁻¹ * c⁻¹) • ((A : Matrix (Fin n) (Fin n) F) * A) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = (c⁻¹ * c⁻¹) • (μ • 1) := by rw [hA2]
        _ = ((c⁻¹ * c⁻¹) * μ) • 1 := by rw [smul_smul]
        _ = 1 := by rw [hcoef, one_smul]
    have hA₀s : ∀ d : F, (A₀ : Matrix (Fin n) (Fin n) F) ≠ d • 1 := by
      intro d hd
      apply hAs (c * d)
      calc (A : Matrix (Fin n) (Fin n) F)
          = c • (c⁻¹ • (A : Matrix (Fin n) (Fin n) F)) := by
              rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
        _ = c • (A₀ : Matrix (Fin n) (Fin n) F) := by rw [← hA₀mat]
        _ = c • (d • 1) := by rw [hd]
        _ = (c * d) • 1 := by rw [smul_smul]
    have hA₀Φ : (A₀ : Matrix (Fin n) (Fin n) F)ᵀ * Φ = Φ * A₀ := by
      calc (A₀ : Matrix (Fin n) (Fin n) F)ᵀ * (Φ : Matrix (Fin n) (Fin n) F)
          = (c⁻¹ • (A : Matrix (Fin n) (Fin n) F))ᵀ * Φ := by rw [hA₀mat]
        _ = (c⁻¹ • ((A : Matrix (Fin n) (Fin n) F)ᵀ)) * Φ := by rw [Matrix.transpose_smul]
        _ = c⁻¹ • (((A : Matrix (Fin n) (Fin n) F)ᵀ) * Φ) := by rw [Matrix.smul_mul]
        _ = c⁻¹ • ((Φ : Matrix (Fin n) (Fin n) F) * A) := by rw [hAΦ]
        _ = (Φ : Matrix (Fin n) (Fin n) F) * (c⁻¹ • (A : Matrix (Fin n) (Fin n) F)) := by
              rw [Matrix.mul_smul]
        _ = (Φ : Matrix (Fin n) (Fin n) F) * A₀ := by rw [hA₀mat]
    have hgen₀ : E = Subgroup.zpowers (conjAut n F A₀) ⊔
        Subgroup.zpowers (conjAut n F Φ⁻¹ * dualAut n F) := by
      rw [hconjAut]
      exact hgen
    rcases orth_conj_or_inverted_unipotent_of_sq hF hn hΦdet hΦt hA₀2 hA₀s hA₀Φ with
      ⟨g, hgΦ, hg1, hgc, hgne⟩ | ⟨Y, hY1, hY3, hYΦ, hAY⟩
    · exact planeGen_of_graph_orth_conj (μ := (1 : F)) hn hF hE h4 A₀ Φ
        (by simpa using hA₀2) hgen₀ g
        hgΦ hg1 hgc hgne
    · exact planeGen_of_graph_orth_inverted hn hF hE h4 A₀ Φ hgen₀ Y hY1 hY3 hYΦ hAY
  · rcases orth_conj_or_inverted_unipotent_of_not_sq hF hn hΦdet hΦt hA2 hsq hAΦ with
      ⟨g, hgΦ, hg1, hgc, hgne⟩ | ⟨Y, hY1, hY3, hYΦ, hAY⟩
    · exact planeGen_of_graph_orth_conj hn hF hE h4 A Φ hA2 hgen g hgΦ hg1 hgc hgne
    · exact planeGen_of_graph_orth_inverted hn hF hE h4 A Φ hgen Y hY1 hY3 hYΦ hAY

theorem planeGen_of_not_linear {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n)
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (hNL : ¬ E ≤ linearAutGroup n F) : PlaneGen E := by
  classical
  by_cases hsem : ∃ e ∈ E, e ∈ semilinearAutGroup n F ∧ e ∉ linearAutGroup n F
  · exact planeGen_of_semilinear_not_linear hn hF hE h4 hsem
  · have hsemi' : ∀ e ∈ E, e ∈ semilinearAutGroup n F → e ∈ linearAutGroup n F := by
      intro e he hes
      by_contra h
      exact hsem ⟨e, he, hes, h⟩
    obtain ⟨A, Φ, σ, μ, c, κ, hgen, hσ2, hA2, hAs, hΦc, hAΦ⟩ :=
      exists_graph_pair_of_not_semilinear hn hE h4 hNL hsemi'
    have hμ : μ ≠ 0 := smul_ne_zero_of_mul_self_eq_smul_one hn hA2
    have hΦdet : IsUnit ((Φ : Matrix (Fin n) (Fin n) F).det) := Matrix.isUnits_det_units Φ
    by_cases hσ1 : σ = 1
    · subst σ
      have hΦc' : (Φ : Matrix (Fin n) (Fin n) F) = c • ((Φ : Matrix (Fin n) (Fin n) F))ᵀ := by
        simpa using hΦc
      have hAΦ' : ((A : Matrix (Fin n) (Fin n) F))ᵀ * Φ * A =
          κ • (Φ : Matrix (Fin n) (Fin n) F) := by
        simpa using hAΦ
      have hgen' : E = Subgroup.zpowers (conjAut n F A) ⊔
          Subgroup.zpowers (conjAut n F Φ⁻¹ * dualAut n F) := by
        simpa using hgen
      obtain ⟨ε, δ, hε, hδ, hΦt, hAΦ''⟩ :=
        graph_sign_normal_form hΦdet hμ hA2 hΦc' hAΦ'
      by_cases horth : ε = 1 ∧ δ = 1
      · have hΦsym : (Φ : Matrix (Fin n) (Fin n) F)ᵀ = Φ := by
          rw [hΦt, horth.1, one_smul]
        have hAΦsym : (A : Matrix (Fin n) (Fin n) F)ᵀ * Φ = Φ * A := by
          rw [hAΦ'', horth.2, one_smul]
        exact planeGen_of_graph_orth hn hF hE h4 A Φ hA2 hAs hΦsym hAΦsym hgen'
      · obtain ⟨N, hN0, hN2, hAN, hNΦ⟩ :=
          exists_sq_zero_commute_isometry_of_not_orth hF hn hΦdet hμ hA2 hε hδ hΦt hAΦ''
            horth
        have hNΦ' : (N.map (1 : F ≃+* F))ᵀ * (Φ : Matrix (Fin n) (Fin n) F) +
            (Φ : Matrix (Fin n) (Fin n) F) * N = 0 := by simpa using hNΦ
        exact planeGen_of_sq_zero_commute hF hE h4 hgen hN0 hN2 hAN
          (isometry_one_add hN2 hNΦ')
    · obtain ⟨N, hN0, hN2, hAN, hNΦ⟩ :=
        exists_sq_zero_commute_unitary hF hn hσ2 hσ1 hΦdet hμ hA2 hΦc hAΦ
      exact planeGen_of_sq_zero_commute hF hE h4 hgen hN0 hN2 hAN
        (isometry_one_add hN2 hNΦ)

theorem seitzFourPSLNonlinear_holds : SeitzFourPSLNonlinear := by
  intro K _ _ hZ hperf F _ _ n hn hF θ E hE h4 hNL
  let E' : Subgroup (MulAut (projectiveSL n F)) := E.map (QuasiHigh2.modelAut θ)
  have hinj : Function.Injective (QuasiHigh2.modelAut θ) := QuasiHigh2.modelAut_injective hperf θ
  have hE' : IsElemAbelian 2 E' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 2 hE _
  have h4' : Nat.card E' = 4 := by
    rw [show E' = E.map (QuasiHigh2.modelAut θ) from rfl,
      Subgroup.card_map_of_injective hinj, h4]
  have hNL' : ¬ E' ≤ linearAutGroup n F := hNL
  exact seitzHyperGamma_two_of_planeGen_modelAut hZ θ h4
    (planeGen_of_not_linear hn hF hE' h4' hNL')

theorem seitzFour_psl :
    SeitzFour fun X _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSL n p f :=
  seitzFour_psl_of_nonlinear seitzFourPSLNonlinear_holds

end CFSG.LocalAnalysis.WeakClosure81.PSLOuter
