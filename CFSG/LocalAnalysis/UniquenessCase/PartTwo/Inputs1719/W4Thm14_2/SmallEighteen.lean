module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.SmallEighteenGraphField
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.Quasithin.Background.SmithB42SL3Aut
public import CFSG.LargeExtraspecial.OrthoF2PairsFpf
import CFSG.HardMathSupport.Curtis.UnitaryLevi.SemilinearPm
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOLinkPSLAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open scoped MatrixGroups Matrix

section Rep
variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

private lemma repEquiv_pow (ρ : Representation (ZMod 2) SL(3, F) U) (x : SL(3, F)) (n : ℕ) :
    X7a.repEquiv ρ x ^ n = X7a.repEquiv ρ (x ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, repEquiv_one]
  | succ n ih =>
    rw [pow_succ, ih]
    refine LinearEquiv.ext fun u => ?_
    change ρ (x ^ n) (ρ x u) = ρ (x ^ n * x) u
    rw [map_mul, Module.End.mul_apply]

private lemma scalarElement_pow_three (ω : Fˣ) (hω : ω ^ 3 = 1) :
    (LinearFlag.scalarElement ω hω : SL(3, F)) ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, LinearFlag.coe_scalarElement, ← map_pow]
  have h3 : ((ω : F)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω, Units.val_one]
  rw [h3, map_one, Matrix.SpecialLinearGroup.coe_one]

private lemma scalarElement_ne_one (ω : Fˣ) (hω : ω ^ 3 = 1) (hω1 : (ω : F) ≠ 1) :
    LinearFlag.scalarElement ω hω ≠ 1 := by
  intro h
  have hcoeff : ((LinearFlag.scalarElement ω hω : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 =
      (ω : F) := by
    rw [LinearFlag.coe_scalarElement]
    change (Matrix.diagonal (fun _ : Fin 3 => (ω : F))) 0 0 = (ω : F)
    simp [Matrix.diagonal]
  rw [h, Matrix.SpecialLinearGroup.coe_one] at hcoeff
  simp [Matrix.one_apply] at hcoeff
  exact hω1 hcoeff.symm

private lemma fixSpace_repEquiv_eq_bot (ρ : Representation (ZMod 2) SL(3, F) U)
    {x : SL(3, F)} (hx : x ∈ LinearFlag.scalars 3 F) (hx1 : x ≠ 1)
    (hz : ∀ x ∈ LinearFlag.scalars 3 F, x ≠ 1 → ∀ u, ρ x u = u → u = 0) :
    CFSG.RankThree.OrthogonalInvolutions.fixSpace (X7a.repEquiv ρ x) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  rw [CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace] at hu
  exact hz x hx hx1 u hu

private lemma coe_stdAut_zero_scalarElement (M : GL (Fin 3) F) (σ : F ≃+* F)
    (ω : Fˣ) (hω : ω ^ 3 = 1) :
    ((CFSG.QuasithinUnique.K1.stdAut M σ 0 (LinearFlag.scalarElement ω hω) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal (fun _ : Fin 3 => σ (ω : F)) := by
  rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero, LinearFlag.coe_scalarElement]
  change (M : Matrix (Fin 3) (Fin 3) F) *
    ((Matrix.diagonal (fun _ : Fin 3 => (ω : F))).map σ) *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    Matrix.diagonal (fun _ : Fin 3 => σ (ω : F))
  have hmap : (Matrix.diagonal (fun _ : Fin 3 => (ω : F))).map σ =
      Matrix.diagonal (fun _ : Fin 3 => σ (ω : F)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [hmap]
  have hm : (M : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal (fun _ : Fin 3 => σ (ω : F)) *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.diagonal (fun _ : Fin 3 => σ (ω : F)) := by
    change (M : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (σ (ω : F)) *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (σ (ω : F))
    rw [← (Matrix.scalar_commute (σ (ω : F)) (fun r' => Commute.all _ r')
      (M : Matrix (Fin 3) (Fin 3) F)).eq, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_one]
  exact hm

private lemma coe_stdAut_one_scalarElement (M : GL (Fin 3) F) (σ : F ≃+* F)
    (ω : Fˣ) (hω : ω ^ 3 = 1) :
    ((CFSG.QuasithinUnique.K1.stdAut M σ 1 (LinearFlag.scalarElement ω hω) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal (fun _ : Fin 3 => (σ (ω : F))⁻¹) := by
  rw [CFSG.QuasithinUnique.K1.coe_stdAut_one]
  have hωinv : ((LinearFlag.scalarElement ω hω)⁻¹ : SL(3, F)) =
      LinearFlag.scalarElement ω⁻¹ (by rw [inv_pow, hω, inv_one]) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.scalarElement_inv (n := 3) ω hω
  rw [hωinv, LinearFlag.coe_scalarElement]
  change (M : Matrix (Fin 3) (Fin 3) F) *
    ((Matrix.diagonal (fun _ : Fin 3 => ((ω⁻¹ : Fˣ) : F)))ᵀ.map σ) *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    Matrix.diagonal (fun _ : Fin 3 => (σ (ω : F))⁻¹)
  have hmap : (Matrix.diagonal (fun _ : Fin 3 => ((ω⁻¹ : Fˣ) : F))).map σ =
      Matrix.diagonal (fun _ : Fin 3 => (σ (ω : F))⁻¹) := by
    ext i j
    by_cases h : i = j
    · simp [Matrix.diagonal, h, Units.val_inv_eq_inv_val, map_inv₀]
    · simp [Matrix.diagonal, h]
  rw [Matrix.diagonal_transpose, hmap]
  have hm : (M : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal (fun _ : Fin 3 => (σ (ω : F))⁻¹) *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.diagonal (fun _ : Fin 3 => (σ (ω : F))⁻¹) := by
    change (M : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) ((σ (ω : F))⁻¹) *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) ((σ (ω : F))⁻¹)
    rw [← (Matrix.scalar_commute ((σ (ω : F))⁻¹) (fun r' => Commute.all _ r')
      (M : Matrix (Fin 3) (Fin 3) F)).eq, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_one]
  exact hm

private lemma omega_sq_eq_inv (ω : Fˣ) (hω : ω ^ 3 = 1) :
    (ω : F) ^ 2 = ((ω⁻¹ : Fˣ) : F) := by
  rw [← Units.val_pow_eq_pow_val, CFSG.Fischer.Classification.sq_eq_inv_of_pow_three hω,
    Units.val_inv_eq_inv_val]

private lemma stdAut_zero_scalarElement_eq_inv (M : GL (Fin 3) F) (σ : F ≃+* F)
    (ω : Fˣ) (hω : ω ^ 3 = 1) (hσω : σ (ω : F) = ((ω⁻¹ : Fˣ) : F)) :
    CFSG.QuasithinUnique.K1.stdAut M σ 0 (LinearFlag.scalarElement ω hω) =
      (LinearFlag.scalarElement ω hω)⁻¹ := by
  apply Subtype.ext
  rw [coe_stdAut_zero_scalarElement, hσω,
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.scalarElement_inv (n := 3),
    LinearFlag.coe_scalarElement]
  rfl

private lemma stdAut_one_scalarElement_eq_inv (M : GL (Fin 3) F) (ω : Fˣ) (hω : ω ^ 3 = 1) :
    CFSG.QuasithinUnique.K1.stdAut M 1 1 (LinearFlag.scalarElement ω hω) =
      (LinearFlag.scalarElement ω hω)⁻¹ := by
  apply Subtype.ext
  rw [coe_stdAut_one_scalarElement,
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.scalarElement_inv (n := 3),
    LinearFlag.coe_scalarElement]
  simp [Units.val_inv_eq_inv_val]

private lemma stdAut_one_eq_graphFieldHom_one (M : GL (Fin 3) F) (σ : F ≃+* F)
    (hσ : ∀ y, σ y = y ^ 2) :
    ∀ x : SL(3, F),
      CFSG.QuasithinUnique.K1.stdAut M σ 1 x = X7Sec.graphFieldHom M 1 x := by
  intro x
  show CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F M
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F x)) =
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F M
      ((X7a.tauSL F) ((X7a.frobPow F 1) x))
  congr 1
  apply Subtype.ext
  have h1 : ((CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F x) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) = ((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ).map σ) := rfl
  rw [h1, X7a.tauSL_coe, X7a.trInvMat, ← map_inv, X7Sec.frobPow_coe, Matrix.transpose_map]
  ext a b
  simp [Matrix.map_apply, hσ]

private lemma five_le_rank_of_inverts (hdim : Module.finrank (ZMod 2) U = 18)
    (a z : U ≃ₗ[ZMod 2] U) (ha2 : a * a = 1) (hz3 : z ^ 3 = 1)
    (hfpf : CFSG.RankThree.OrthogonalInvolutions.fixSpace z = ⊥)
    (hinv : a * z * a⁻¹ = z⁻¹) :
    5 ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  have h := CFSG.LargeExtraspecial.two_mul_finrank_commSpace_of_inverts_fpf
    (V := U) (x := a) (z := z) ha2 hz3 hfpf hinv
  have hcomm : CFSG.RankThree.OrthogonalInvolutions.commSpace a =
      LinearMap.range (a.toLinearMap - 1) := rfl
  rw [hcomm] at h
  omega

theorem five_le_rank_of_finrank_eighteen (hF : Fintype.card F = 2 ^ 2)
    (ρ : Representation (ZMod 2) SL(3, F) U) (hirr : ρ.IsIrreducible)
    (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ LinearFlag.scalars 3 F)
    (hz : ∀ x ∈ LinearFlag.scalars 3 F, x ≠ 1 → ∀ u, ρ x u = u → u = 0)
    (hdim : Module.finrank (ZMod 2) U = 18)
    (hR : 8 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (X7a.up3 0 0 1) - 1)))
    (a : U ≃ₗ[ZMod 2] U) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haN : ∀ x : SL(3, F), ∃ y, X7a.Intertwines ρ a x y) :
    5 ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  classical
  have hk4 : Nat.card F = 4 := by
    rw [Nat.card_eq_fintype_card, hF]
    norm_num
  have hU : Nontrivial U := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    haveI : Subsingleton U := hsub
    have h0 : Module.finrank (ZMod 2) U = 0 := Module.finrank_zero_of_subsingleton
    omega
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    have hxyE : X7a.repEquiv ρ x = X7a.repEquiv ρ y := by
      refine LinearEquiv.ext fun u => ?_
      change ρ x u = ρ y u
      rw [hxy]
    have h1 : X7a.repEquiv ρ (x * y⁻¹) = 1 := by
      rw [repEquiv_mul, hxyE, repEquiv_inv]
      simp
    have hρ1 : ρ (x * y⁻¹) = 1 := by
      have hcoe := congrArg (fun e : U ≃ₗ[ZMod 2] U => (e : U →ₗ[ZMod 2] U)) h1
      have hcoe' : ρ (x * y⁻¹) = LinearMap.id := by
        simpa [X7a.repEquiv, LinearEquiv.coe_one] using hcoe
      rw [Module.End.one_eq_id]
      exact hcoe'
    have hs : x * y⁻¹ ∈ LinearFlag.scalars 3 F := hker _ hρ1
    have h2 : x * y⁻¹ = 1 := by
      by_contra hne
      obtain ⟨u, hu⟩ := exists_ne (0 : U)
      exact hu (hz _ hs hne u (by rw [hρ1]; simp))
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [h2]
      _ = y := one_mul y
  let A : Subgroup (U ≃ₗ[ZMod 2] U) := Subgroup.zpowers a
  have hmem_cases : ∀ b ∈ A, b = 1 ∨ b = a := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have h2 : a ^ (2 : ℤ) = 1 := by
      rw [show a ^ (2 : ℤ) = a ^ (2 : ℕ) by rfl, pow_two, ha2]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [zpow_eq_zpow_emod k h2, hk]
      simp
    · right
      rw [zpow_eq_zpow_emod k h2, hk]
      simp
  have hA : ∀ b ∈ A, ∀ x : SL(3, F), ∃ y, X7a.Intertwines ρ b x y := by
    intro b hb x
    rcases hmem_cases b hb with rfl | rfl
    · exact ⟨x, fun u => rfl⟩
    · exact haN x
  haveI hEA : CFSG.IsElementaryAbelian 2 A :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (x := a) (by simpa [pow_two] using ha2)
  let aA : ↥A := ⟨a, Subgroup.mem_zpowers a⟩
  have hν2 : X7a.normalizerHom ρ hker A hA aA * X7a.normalizerHom ρ hker A hA aA = 1 := by
    rw [← map_mul, B42SL3.elem_mul_self A aA, map_one]
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := F) (n := 3) (by norm_num)
  obtain ⟨M, σ, ε, hε, hν_eq⟩ := hgen (X7a.normalizerHom ρ hker A hA aA)
  have hψ : LinearFlag.descendAut 3 F (CFSG.QuasithinUnique.K1.stdAut M σ ε) =
      X7a.normalizerHom ρ hker A hA aA := by
    rw [CFSG.QuasithinUnique.K1.descendAut_stdAut, hν_eq]
  have hint : ∀ x : SL(3, F),
      X7a.Intertwines ρ a x (CFSG.QuasithinUnique.K1.stdAut M σ ε x) :=
    X7a.intertwines_psi ρ (X7a.normalizerHom ρ hker A hA aA)
      (CFSG.QuasithinUnique.K1.stdAut M σ ε) hψ a
      (X7a.exists_induced ρ hker A hA aA)
  have hε01 : ε = 0 ∨ ε = 1 := by omega
  rcases hε01 with rfl | rfl
  ·
    have hν0 : X7a.normalizerHom ρ hker A hA aA =
        LinearFlag.conjAut 3 F M * LinearFlag.fieldAut 3 F σ := by
      simpa using hν_eq
    by_cases hσ1 : σ = 1
    ·
      have hνM : X7a.normalizerHom ρ hker A hA aA = LinearFlag.conjAut 3 F M := by
        simpa [hσ1] using hν0
      have hMM : LinearFlag.conjAut 3 F (M * M) = 1 := by
        rw [map_mul, ← hνM]
        exact hν2
      obtain ⟨c, hc⟩ := (LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (K := F) (n := 3)
        le_rfl (M * M) 1 (by rw [map_one, mul_one]; exact hMM)).2
      have hdetMM : Matrix.GeneralLinearGroup.det (M * M) = 1 := by
        rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
        have hc3 : c ^ 3 = 1 := by
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, Units.val_one]
          exact LinearFieldFour.pow_three_eq_one hk4 (Units.ne_zero c)
        rw [hc3]
      have hdetM2 : Matrix.GeneralLinearGroup.det M ^ 2 = 1 := by
        rw [map_mul] at hdetMM
        simpa [pow_two] using hdetMM
      have hdetM3 : Matrix.GeneralLinearGroup.det M ^ 3 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact LinearFieldFour.pow_three_eq_one hk4 (Units.ne_zero _)
      have hdet1 : Matrix.GeneralLinearGroup.det M = 1 := by
        have h2 : orderOf (Matrix.GeneralLinearGroup.det M) ∣ 2 :=
          orderOf_dvd_of_pow_eq_one hdetM2
        have h3 : orderOf (Matrix.GeneralLinearGroup.det M) ∣ 3 :=
          orderOf_dvd_of_pow_eq_one hdetM3
        have h1 : orderOf (Matrix.GeneralLinearGroup.det M) ∣ 1 := by
          have hg := Nat.dvd_gcd h2 h3
          simpa using hg
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
      have hrange : LinearFlag.conjAut 3 F M ∈
          (MulAut.conj : LinearFlag.projectiveSL 3 F →*
            MulAut (LinearFlag.projectiveSL 3 F)).range := by
        refine LinearFlag.conjAut_mem_range_conj_of_det_eq_pow (K := F) (n := 3)
          (A := M) (μ := 1) ?_
        simpa using hdet1
      have haInner : aA ∈ B42SL3.innerPart ρ hker A hA := by
        rw [B42SL3.mem_innerPart, hνM]
        exact hrange
      obtain ⟨t, ht2, htρ⟩ := B42SL3.exists_lift_of_inner ρ hker A hA (f := 2)
        (by norm_num) (by rw [Nat.card_eq_fintype_card, hF]) hirr aA haInner
      have ht1 : t ≠ 1 := by
        intro ht
        apply ha1
        refine LinearEquiv.ext fun u => ?_
        rw [htρ u, ht]
        simp
      have hrank := B42SL3.finrank_range_involution ρ ht1 ht2
      have haEq : a.toLinearMap = ρ t := LinearMap.ext fun u => by simpa using htρ u
      rw [haEq, hrank]
      exact le_trans (by norm_num : 5 ≤ 8) hR
    ·
      obtain ⟨ω0, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hk4
      let ω : Fˣ := Units.mk0 ω0 hω0
      have hω3 : ω ^ 3 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact LinearFieldFour.pow_three_eq_one hk4 hω0
      have hω1u : (ω : F) ≠ 1 := hω1
      have hσ_sq : ∀ y, σ y = y ^ 2 :=
        CFSG.HardMathSupport.Curtis.UnitaryLevi.ringEquiv_apply_eq_sq_of_card_four hk4 hσ1
      have hσω : σ (ω : F) = ((ω⁻¹ : Fˣ) : F) := by
        rw [hσ_sq, omega_sq_eq_inv ω hω3]
      let x : SL(3, F) := LinearFlag.scalarElement ω hω3
      have hψx : CFSG.QuasithinUnique.K1.stdAut M σ 0 x = x⁻¹ :=
        stdAut_zero_scalarElement_eq_inv M σ ω hω3 hσω
      have hx_mem : x ∈ LinearFlag.scalars 3 F :=
        LinearFlag.scalarElement_mem_scalars ω hω3
      have hx_ne : x ≠ 1 := scalarElement_ne_one ω hω3 hω1u
      have hfpf := fixSpace_repEquiv_eq_bot ρ hx_mem hx_ne hz
      have hz3 : (X7a.repEquiv ρ x) ^ 3 = 1 := by
        rw [repEquiv_pow, scalarElement_pow_three ω hω3, repEquiv_one]
      have hconj : a * X7a.repEquiv ρ x * a⁻¹ = (X7a.repEquiv ρ x)⁻¹ := by
        have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [ha_inv]
        have h1 : a * X7a.repEquiv ρ x * a = X7a.repEquiv ρ (x⁻¹) := by
          rw [conj_repEquiv_of_intertwines ρ ha2 (hint x), hψx]
        rw [h1, repEquiv_inv]
      exact five_le_rank_of_inverts hdim a (X7a.repEquiv ρ x) ha2 hz3 hfpf hconj
  ·
    by_cases hσ1 : σ = 1
    ·
      subst hσ1
      obtain ⟨ω0, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hk4
      let ω : Fˣ := Units.mk0 ω0 hω0
      have hω3 : ω ^ 3 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact LinearFieldFour.pow_three_eq_one hk4 hω0
      have hω1u : (ω : F) ≠ 1 := hω1
      let x : SL(3, F) := LinearFlag.scalarElement ω hω3
      have hψx : CFSG.QuasithinUnique.K1.stdAut M 1 1 x = x⁻¹ :=
        stdAut_one_scalarElement_eq_inv M ω hω3
      have hx_mem : x ∈ LinearFlag.scalars 3 F :=
        LinearFlag.scalarElement_mem_scalars ω hω3
      have hx_ne : x ≠ 1 := scalarElement_ne_one ω hω3 hω1u
      have hfpf := fixSpace_repEquiv_eq_bot ρ hx_mem hx_ne hz
      have hz3 : (X7a.repEquiv ρ x) ^ 3 = 1 := by
        rw [repEquiv_pow, scalarElement_pow_three ω hω3, repEquiv_one]
      have hconj : a * X7a.repEquiv ρ x * a⁻¹ = (X7a.repEquiv ρ x)⁻¹ := by
        have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [ha_inv]
        have h1 : a * X7a.repEquiv ρ x * a = X7a.repEquiv ρ (x⁻¹) := by
          rw [conj_repEquiv_of_intertwines ρ ha2 (hint x), hψx]
        rw [h1, repEquiv_inv]
      exact five_le_rank_of_inverts hdim a (X7a.repEquiv ρ x) ha2 hz3 hfpf hconj
    ·
      have hσ_sq : ∀ y, σ y = y ^ 2 :=
        CFSG.HardMathSupport.Curtis.UnitaryLevi.ringEquiv_apply_eq_sq_of_card_four hk4 hσ1
      have hstd1 : ∀ x : SL(3, F),
          CFSG.QuasithinUnique.K1.stdAut M σ 1 x = X7Sec.graphFieldHom M 1 x :=
        stdAut_one_eq_graphFieldHom_one M σ hσ_sq
      have hb : ∀ x : SL(3, F), X7a.Intertwines ρ a x (X7Sec.graphFieldHom M 1 x) := by
        intro x
        rw [← hstd1 x]
        exact hint x
      have h6 := six_dvd_rank_of_graphField hF ρ hker hz a ha2 M (by norm_num : Odd 1) hb
      have hpos : 0 < Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
        have h := CFSG.RankThree.OrthogonalInvolutions.one_le_finrank_commSpace
          (K := ZMod 2) (V := U) (g := a) ha1
        have hcomm : CFSG.RankThree.OrthogonalInvolutions.commSpace a =
            LinearMap.range (a.toLinearMap - 1) := rfl
        rw [hcomm] at h
        omega
      obtain ⟨k, hk⟩ := h6
      omega
end Rep

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2
