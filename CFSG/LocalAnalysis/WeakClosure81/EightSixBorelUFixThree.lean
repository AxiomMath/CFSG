module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofHermitian
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUDict
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUFix
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bInvol
import CFSG.ClassicalGroups.UnitaryFlag.IsotropicKernel
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutModel
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSetup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.RankTwoClassical.URigid
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LinearGroups

variable {m n : ℕ} {F : Type} [Field F] [Finite F]

private theorem borel86_uft_add_self_eq_zero_vec (h : UnitaryFieldData 2 n F) (w : Fin m → F) :
    w + w = 0 := by
  funext i
  haveI := h.charP
  exact CharTwo.add_self_eq_zero (w i)

private theorem borel86_uft_add_eq_zero_iff_vec (h : UnitaryFieldData 2 n F) {p z : Fin m → F} :
    p + z = 0 ↔ p = z := by
  constructor
  · intro hpz
    funext i
    haveI := h.charP
    exact CharTwo.add_eq_zero.mp (congrFun hpz i)
  · intro hpz
    rw [hpz]
    exact borel86_uft_add_self_eq_zero_vec h z

private theorem borel86_uft_bar_comp_mulVec (h : UnitaryFieldData 2 n F)
    (M : Matrix (Fin m) (Fin m) F) (w : Fin m → F) :
    h.bar ∘ (M *ᵥ w) = M.map h.bar *ᵥ (h.bar ∘ w) :=
  funext fun i => RingHom.map_mulVec h.bar M w i

private theorem borel86_uft_phi_phi (h : UnitaryFieldData 2 n F) {A : GL (Fin m) F}
    (hAA : (A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar = 1)
    (w : Fin m → F) :
    (A : Matrix (Fin m) (Fin m) F) *ᵥ
      (h.bar ∘ ((A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ w))) = w := by
  rw [borel86_uft_bar_comp_mulVec h (A : Matrix (Fin m) (Fin m) F) (h.bar ∘ w),
    Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  funext i
  simp [Function.comp_apply, h.bar_bar]

private theorem borel86_uft_phi_add (h : UnitaryFieldData 2 n F) {A : GL (Fin m) F}
    (a b : Fin m → F) :
    (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ (a + b)) =
      (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ a) +
        (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ b) := by
  rw [show h.bar ∘ (a + b) = h.bar ∘ a + h.bar ∘ b by
    funext i; simp [Function.comp_apply, map_add], Matrix.mulVec_add]

private theorem borel86_uft_phi_smul (h : UnitaryFieldData 2 n F) {A : GL (Fin m) F}
    (c : F) (a : Fin m → F) :
    (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ (c • a)) =
      h.bar c • ((A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ a)) := by
  rw [show h.bar ∘ (c • a) = h.bar c • (h.bar ∘ a) by
    funext i; simp [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul],
    Matrix.mulVec_smul]

theorem borel86_uft_mulVec_eq_smul_of_sq (h : UnitaryFieldData 2 n F) {σ : F ≃+* F}
    (hσ : ∀ c, σ c = h.bar c) {A : GL (Fin m) F}
    {α : MulAut (StatedProj (StatedSU m (2 ^ n) F))}
    (hα : ∀ g : StatedSU m (2 ^ n) F,
      ∃ hg : A * glAut σ (g : GL (Fin m) F) * A⁻¹ ∈ StatedSU m (2 ^ n) F,
        α (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    (hα2 : α * α = 1) {u : Fin m → F} (hu : u ≠ 0) (huu : hform h.bar u u = 0) :
    ∃ ν : F, ((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar) *ᵥ u =
      ν • u := by
  classical
  haveI := h.charP
  have hm : 1 ≤ m := by
    by_contra hlt
    push Not at hlt
    exact hu (funext fun i => absurd i.2 (by omega))
  set W : Matrix (Fin m) (Fin m) F := vecMulVec u (h.bar ∘ u) with hW
  obtain ⟨N, hN⟩ := exists_one_add_mem h huu (map_one h.bar)
  have hN' : (N : GL (Fin m) F).val = 1 + W := by
    rw [hN, ← hW, one_smul]
  have hW2 : W * W = 0 := by
    rw [hW]
    exact vecMulVec_mul_self h huu
  have hN2 : N * N = 1 := by
    refine mul_self_eq_one_of_val (x := N) (M := 1 + W) hN' ?_
    rw [add_mul, one_mul, mul_add, mul_one, hW2, add_zero, add_assoc,
      show W + W = 0 by ext i j; exact CharTwo.add_self_eq_zero (W i j), add_zero]
  have hαα : α (α (QuotientGroup.mk N)) = QuotientGroup.mk N := by
    have h2 := congrArg (fun f : MulAut (StatedProj (StatedSU m (2 ^ n) F)) =>
      f (QuotientGroup.mk N)) hα2
    simpa [MulAut.mul_apply, MulAut.one_apply] using h2
  obtain ⟨hg₁, he₁⟩ := hα N
  let N₁ : StatedSU m (2 ^ n) F := ⟨A * glAut σ (N : GL (Fin m) F) * A⁻¹, hg₁⟩
  obtain ⟨hg₂, he₂⟩ := hα N₁
  let N₀ : StatedSU m (2 ^ n) F := ⟨A * glAut σ (N₁ : GL (Fin m) F) * A⁻¹, hg₂⟩
  have hchain : (QuotientGroup.mk N₀ : StatedProj (StatedSU m (2 ^ n) F)) =
      (QuotientGroup.mk N : StatedProj (StatedSU m (2 ^ n) F)) := by
    calc (QuotientGroup.mk N₀ : StatedProj (StatedSU m (2 ^ n) F))
        = α (QuotientGroup.mk N₁) := he₂.symm
      _ = α (α (QuotientGroup.mk N)) := by rw [he₁]
      _ = (QuotientGroup.mk N : StatedProj (StatedSU m (2 ^ n) F)) := hαα
  have hglAut2 : glAut σ (glAut σ (N : GL (Fin m) F)) = (N : GL (Fin m) F) := by
    apply Units.ext
    rw [coe_glAut, coe_glAut, Matrix.map_map]
    have hσσ : σ ∘ σ = id := funext fun c => by
      calc σ (σ c) = h.bar (σ c) := hσ (σ c)
        _ = h.bar (h.bar c) := by rw [hσ c]
        _ = c := h.bar_bar c
    rw [hσσ, Matrix.map_id]
  have hgl : glAut σ (N₁ : GL (Fin m) F) =
      glAut σ A * (N : GL (Fin m) F) * (glAut σ A)⁻¹ := by
    change glAut σ (A * glAut σ (N : GL (Fin m) F) * A⁻¹) =
      glAut σ A * (N : GL (Fin m) F) * (glAut σ A)⁻¹
    simp only [map_mul, map_inv, hglAut2]
  set B : GL (Fin m) F := A * glAut σ A with hB
  have hN₀ : (N₀ : GL (Fin m) F) = B * (N : GL (Fin m) F) * B⁻¹ := by
    change A * glAut σ (N₁ : GL (Fin m) F) * A⁻¹ = B * (N : GL (Fin m) F) * B⁻¹
    rw [hgl, hB]
    group
  have hN2' : (N : GL (Fin m) F) * (N : GL (Fin m) F) = 1 := by
    rw [← Subgroup.coe_mul, hN2, Subgroup.coe_one]
  have hconj : (B * (N : GL (Fin m) F) * B⁻¹) * (B * (N : GL (Fin m) F) * B⁻¹) = 1 := by
    calc B * (N : GL (Fin m) F) * B⁻¹ * (B * (N : GL (Fin m) F) * B⁻¹)
        = B * ((N : GL (Fin m) F) * (N : GL (Fin m) F)) * B⁻¹ := by group
      _ = 1 := by rw [hN2', mul_one, mul_inv_cancel]
  have hN₀2 : N₀ * N₀ = 1 := by
    refine mul_self_eq_one_of_val (x := N₀) (M := (B * (N : GL (Fin m) F) * B⁻¹).val) ?_ ?_
    · change (N₀ : GL (Fin m) F).val = _
      rw [hN₀]
    · have h := congrArg (fun g : GL (Fin m) F => (g : Matrix (Fin m) (Fin m) F)) hconj
      rw [Units.val_mul, Units.val_one] at h
      exact h
  have hproj : uProj F m n N₀ = uProj F m n N := by
    simpa [uProj, QuotientGroup.mk'_apply] using hchain
  have hN₀_eq : N₀ = N :=
    eq_of_uProj_eq_of_mul_self (K := F) (f := n) (n := m) hm hproj hN₀2 hN2
  have hBNB : B * (N : GL (Fin m) F) * B⁻¹ = (N : GL (Fin m) F) := by
    rw [← hN₀]
    exact congrArg Subtype.val hN₀_eq
  have hBN : B * (N : GL (Fin m) F) = (N : GL (Fin m) F) * B := by
    calc B * N = (B * N * B⁻¹) * B := by group
      _ = N * B := by rw [hBNB]
  have hBNmat : (B : Matrix (Fin m) (Fin m) F) * (N : GL (Fin m) F).val =
      (N : GL (Fin m) F).val * (B : Matrix (Fin m) (Fin m) F) := by
    have h := congrArg (fun g : GL (Fin m) F => (g : Matrix (Fin m) (Fin m) F)) hBN
    simpa using h
  have hmapσ : (A : Matrix (Fin m) (Fin m) F).map σ =
      (A : Matrix (Fin m) (Fin m) F).map h.bar := by
    ext i j
    exact hσ _
  have hBmat : (B : Matrix (Fin m) (Fin m) F) =
      (A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar := by
    change ((A * glAut σ A : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = _
    rw [Units.val_mul, coe_glAut, hmapσ]
  have hcommW :
      ((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar) * W =
        W * ((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar) := by
    have h2 : (B : Matrix (Fin m) (Fin m) F) * (1 + W) =
        (1 + W) * (B : Matrix (Fin m) (Fin m) F) := by
      rw [← hN', hBNmat]
    have h3 : ((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar) *
        (1 + W) = (1 + W) *
          ((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar) := by
      rw [← hBmat]
      exact h2
    rw [mul_add, mul_one, add_mul, one_mul] at h3
    exact add_left_cancel h3
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu (funext hc)
  have hwj : h.bar (u j) ≠ 0 := fun h0 =>
    hj (by simpa [h.bar_bar] using congrArg h.bar h0)
  refine ⟨(((h.bar ∘ u) ᵥ* ((A : Matrix (Fin m) (Fin m) F) *
    (A : Matrix (Fin m) (Fin m) F).map h.bar)) j) / h.bar (u j), ?_⟩
  ext i
  have hcol := congrFun (congrFun hcommW i) j
  rw [hW] at hcol
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul] at hcol
  simp only [Function.comp_apply, Matrix.vecMulVec_apply] at hcol
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv,
    mul_comm ((((h.bar ∘ u) ᵥ* ((A : Matrix (Fin m) (Fin m) F) *
      (A : Matrix (Fin m) (Fin m) F).map h.bar)) j) * (h.bar (u j))⁻¹) (u i),
    ← mul_assoc]
  exact (eq_mul_inv_iff_mul_eq₀ hwj).mpr hcol

theorem borel86_uft_mul_map_bar_eq_one (h : UnitaryFieldData 2 n F) (hm : 2 ≤ m)
    {A : GL (Fin m) F}
    (hA : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) F) = 1)
    (hB : ∀ u : Fin m → F, u ≠ 0 → hform h.bar u u = 0 → ∃ ν : F,
      ((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar) *ᵥ u = ν • u) :
    (A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar = 1 := by
  classical
  haveI := h.charP
  have hAt : (A : Matrix (Fin m) (Fin m) F)ᵀ * (A : Matrix (Fin m) (Fin m) F).map h.bar = 1 := by
    have h := congrArg Matrix.transpose hA
    simpa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using h
  have hmapB : ((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar).map
      h.bar = (A : Matrix (Fin m) (Fin m) F).map h.bar * (A : Matrix (Fin m) (Fin m) F) := by
    rw [Matrix.map_mul, Matrix.map_map]
    have hbb : h.bar ∘ h.bar = id := funext fun c => h.bar_bar c
    rw [hbb, Matrix.map_id]
  have hBadj : adjM h.bar ((A : Matrix (Fin m) (Fin m) F) *
      (A : Matrix (Fin m) (Fin m) F).map h.bar) *
      ((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar) = 1 := by
    rw [adjM, hmapB, Matrix.transpose_mul, mul_assoc,
      ← mul_assoc (((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ) (A : Matrix (Fin m) (Fin m) F)
        ((A : Matrix (Fin m) (Fin m) F).map h.bar), hA, one_mul, hAt]
  have hM : ∀ x y : Fin m → F,
      stdHermForm h m (((A : Matrix (Fin m) (Fin m) F) *
        (A : Matrix (Fin m) (Fin m) F).map h.bar) *ᵥ x)
        (((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar) *ᵥ y) =
        stdHermForm h m x y := by
    intro x y
    rw [stdHermForm_eq_hform h, stdHermForm_eq_hform h,
      hform_mulVec, Matrix.mulVec_mulVec, hBadj, Matrix.one_mulVec]
  have hfix : ∀ v : Fin m → F, v ≠ 0 → stdHermForm h m v v = 0 →
      ∃ κ : F, ((A : Matrix (Fin m) (Fin m) F) *
        (A : Matrix (Fin m) (Fin m) F).map h.bar) *ᵥ v = κ • v := by
    intro v hv hvv
    rw [stdHermForm_eq_hform h] at hvv
    exact hB v hv hvv
  obtain ⟨lam, hlam⟩ :=
    CFSG.ClassicalGroups.UnitaryFlag.eq_smul_of_forall_isotropic h hm hM hfix
  have hB1 : (A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar =
      lam • (1 : Matrix (Fin m) (Fin m) F) := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    exact hlam x
  have hBA : (A : Matrix (Fin m) (Fin m) F).map h.bar * (A : Matrix (Fin m) (Fin m) F) =
      lam • 1 := by
    calc (A : Matrix (Fin m) (Fin m) F).map h.bar * (A : Matrix (Fin m) (Fin m) F)
        = (A⁻¹ : GL (Fin m) F).val * ((A : Matrix (Fin m) (Fin m) F) *
            (A : Matrix (Fin m) (Fin m) F).map h.bar) * (A : Matrix (Fin m) (Fin m) F) := by
          rw [← mul_assoc (A⁻¹ : GL (Fin m) F).val (A : Matrix (Fin m) (Fin m) F)
            ((A : Matrix (Fin m) (Fin m) F).map h.bar), Units.inv_mul, one_mul]
      _ = (A⁻¹ : GL (Fin m) F).val * (lam • 1) * (A : Matrix (Fin m) (Fin m) F) := by rw [hB1]
      _ = lam • 1 := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]
  have hfixB : ((A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar).map
      h.bar = (A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar := by
    rw [hmapB, hBA, hB1]
  let i₀ : Fin m := ⟨0, by omega⟩
  have hlam_bar : h.bar lam = lam := by
    have h1 := hfixB
    rw [hB1] at h1
    have h := congrFun (congrFun h1 i₀) i₀
    simpa [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply] using h
  have hlam_mul : h.bar lam * lam = 1 := by
    have hh := hBadj
    rw [hB1] at hh
    rw [adjM_smul, adjM_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hh
    have h := congrFun (congrFun hh i₀) i₀
    simpa [Matrix.smul_apply, Matrix.one_apply] using h
  have hlam1 : lam = 1 := by
    have hsq : lam * lam = 1 := by simpa [hlam_bar] using hlam_mul
    have hz : (lam + 1) * (lam + 1) = 0 := by
      rw [CharTwo.add_mul_self, hsq, one_mul]
      exact CharTwo.add_self_eq_zero 1
    exact CharTwo.add_eq_zero.mp (mul_self_eq_zero.mp hz)
  rw [hB1, hlam1, one_smul]

theorem borel86_uft_mul_map_bar_eq_one_of_sq (h : UnitaryFieldData 2 n F) (hm : 2 ≤ m)
    {σ : F ≃+* F} (hσ : ∀ c, σ c = h.bar c) {A : GL (Fin m) F}
    (hA : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) F) = 1)
    {α : MulAut (StatedProj (StatedSU m (2 ^ n) F))}
    (hα : ∀ g : StatedSU m (2 ^ n) F,
      ∃ hg : A * glAut σ (g : GL (Fin m) F) * A⁻¹ ∈ StatedSU m (2 ^ n) F,
        α (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    (hα2 : α * α = 1) :
    (A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar = 1 :=
  borel86_uft_mul_map_bar_eq_one h hm hA fun _ hu huu =>
    borel86_uft_mulVec_eq_smul_of_sq h hσ hα hα2 hu huu

theorem borel86_uft_eq_smul_of_isotropic_orth (h : UnitaryFieldData 2 n F) {u v : Fin 3 → F}
    (hv : v ≠ 0) (huu : hform h.bar u u = 0) (hvv : hform h.bar v v = 0)
    (hvu : hform h.bar v u = 0) : ∃ c : F, u = c • v := by
  have hhvv : stdHermForm h 3 v v = 0 := by rw [stdHermForm_eq_hform h]; exact hvv
  have hhvu : stdHermForm h 3 v u = 0 := by rw [stdHermForm_eq_hform h]; exact hvu
  have hhuu : stdHermForm h 3 u u = 0 := by rw [stdHermForm_eq_hform h]; exact huu
  obtain ⟨c, hc⟩ := CFSG.QuasithinUnique.Setup.X5.exists_smul_of_orth_isotropic h
    (V := Fin 3 → F) (B := stdHermForm h 3) (Module.finrank_fin_fun F)
    (stdHermForm_isSymm h 3) (stdHermForm_separatingLeft h 3) hv hhvv hhvu hhuu
  exact ⟨c, hc⟩

theorem borel86_uft_exists_decomp (h : UnitaryFieldData 2 n F) {A : GL (Fin m) F}
    (hAA : (A : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F).map h.bar = 1)
    {θ : F} (hθ : h.bar θ ≠ θ) (v : Fin m → F) :
    ∃ x y : Fin m → F, (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ x) = x ∧
      (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ y) = y ∧ v = x + θ • y := by
  classical
  haveI := h.charP
  let φ : (Fin m → F) → (Fin m → F) := fun w => (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ w)
  have hφφ : ∀ w, φ (φ w) = w := fun w => borel86_uft_phi_phi h hAA w
  have hφadd : ∀ a b, φ (a + b) = φ a + φ b := fun a b => borel86_uft_phi_add h a b
  have hφsmul : ∀ c a, φ (c • a) = h.bar c • φ a := fun c a => borel86_uft_phi_smul h c a
  let s : F := θ + h.bar θ
  have hs : s ≠ 0 := by
    intro h0
    exact hθ (CharTwo.add_eq_zero.mp h0).symm
  have hbs : h.bar s = s := by
    show h.bar (θ + h.bar θ) = θ + h.bar θ
    rw [map_add, h.bar_bar, add_comm]
  let y : Fin m → F := s⁻¹ • (v + φ v)
  let x : Fin m → F := v + θ • y
  have hy : φ y = y := by
    show φ (s⁻¹ • (v + φ v)) = s⁻¹ • (v + φ v)
    rw [hφsmul, hφadd, hφφ, map_inv₀, hbs, add_comm (φ v) v]
  have hx : φ x = x := by
    have hzero : φ x + x = 0 := by
      show φ (v + θ • y) + (v + θ • y) = 0
      have hsy : h.bar θ • y + θ • y = v + φ v := by
        rw [← add_smul, add_comm (h.bar θ) θ]
        show s • (s⁻¹ • (v + φ v)) = v + φ v
        rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
      rw [hφadd, hφsmul, hy]
      calc φ v + h.bar θ • y + (v + θ • y)
          = (φ v + v) + (h.bar θ • y + θ • y) := by abel
        _ = (φ v + v) + (v + φ v) := by rw [hsy]
        _ = 0 := by
            funext i
            haveI := h.charP
            exact CharTwo.add_eq_zero.mpr (add_comm ((φ v) i) (v i))
    exact (borel86_uft_add_eq_zero_iff_vec h).mp hzero
  refine ⟨x, y, ?_, ?_, ?_⟩
  · exact hx
  · exact hy
  · show v = (v + θ • y) + θ • y
    rw [add_assoc, borel86_uft_add_self_eq_zero_vec h (θ • y), add_zero]

theorem borel86_uft_bar_hform_of_fix (h : UnitaryFieldData 2 n F) {A : GL (Fin m) F}
    (hA : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) F) = 1)
    {x y : Fin m → F} (hx : (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ x) = x)
    (hy : (A : Matrix (Fin m) (Fin m) F) *ᵥ (h.bar ∘ y) = y) :
    h.bar (hform h.bar x y) = hform h.bar x y := by
  have h1 : hform h.bar x y = hform h.bar (h.bar ∘ x) (h.bar ∘ y) := by
    conv_lhs => rw [← hx]
    conv_lhs => rw [← hy]
    rw [hform_mulVec, Matrix.mulVec_mulVec, adjM, hA, Matrix.one_mulVec]
  have h2 : hform h.bar (h.bar ∘ x) (h.bar ∘ y) = h.bar (hform h.bar x y) := by
    simp only [hform, dotProduct, Function.comp_apply, map_sum, map_mul, h.bar_bar]
  exact h2.symm.trans h1.symm

theorem borel86_uft_exists_not_mem_span (a b : Fin 3 → F) :
    ∃ v : Fin 3 → F, ∀ x y : F, v ≠ x • a + y • b := by
  classical
  by_contra h
  push Not at h
  have htop : Submodule.span F ({a, b} : Set (Fin 3 → F)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro z
    obtain ⟨x, y, rfl⟩ := h z
    rw [Submodule.mem_span_pair]
    exact ⟨x, y, rfl⟩
  have hfin : Module.finrank F (Submodule.span F ({a, b} : Set (Fin 3 → F))) = 3 := by
    rw [htop, finrank_top, Module.finrank_fin_fun F]
  have hle : Module.finrank F (Submodule.span F ({a, b} : Set (Fin 3 → F))) ≤ 2 := by
    have h₀ := finrank_span_finset_le_card (R := F)
      (s := ({a, b} : Finset (Fin 3 → F)))
    have hcard : ({a, b} : Finset (Fin 3 → F)).card ≤ 2 := by
      have h₁ := Finset.card_insert_le a ({b} : Finset (Fin 3 → F))
      simp only [Finset.card_singleton] at h₁
      omega
    have hcoe : (↑({a, b} : Finset (Fin 3 → F)) : Set (Fin 3 → F)) =
        ({a, b} : Set (Fin 3 → F)) := by
      ext z
      simp
    have h₁ : Module.finrank F (Submodule.span F
        (↑({a, b} : Finset (Fin 3 → F)) : Set (Fin 3 → F))) ≤ 2 := by
      simpa only [Set.finrank] using (h₀.trans hcard)
    rwa [hcoe] at h₁
  omega

theorem borel86_uft_false (h : UnitaryFieldData 2 n F) {A : GL (Fin 3) F}
    (hA : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1)
    {G : StatedSU 3 (2 ^ n) F} (hG : G * G = 1) (hG1 : G ≠ 1)
    (hE : ∀ u : Fin 3 → F, u ≠ 0 → hform h.bar u u = 0 →
      (A : Matrix (Fin 3) (Fin 3) F) *ᵥ (h.bar ∘ u) = u → (G : GL (Fin 3) F).val *ᵥ u = u) :
    False := by
  classical
  haveI := h.charP
  let φ : (Fin 3 → F) → (Fin 3 → F) := fun w => (A : Matrix (Fin 3) (Fin 3) F) *ᵥ (h.bar ∘ w)
  let Q : (Fin 3 → F) → F := fun w => hform h.bar w w
  let r : (Fin 3 → F) → F := fun w => Q w ^ 2 ^ (n - 1)
  have hφφ : ∀ w, φ (φ w) = w := fun w => borel86_uft_phi_phi h hAA w
  have hφadd : ∀ a b, φ (a + b) = φ a + φ b := fun a b => borel86_uft_phi_add h a b
  have hφsmul : ∀ c a, φ (c • a) = h.bar c • φ a := fun c a => borel86_uft_phi_smul h c a
  have hQfix : ∀ v, φ v = v → h.bar (Q v) = Q v :=
    fun v hv => borel86_uft_bar_hform_of_fix h hA hv hv
  obtain ⟨a, ha0, haa, hGa, hperp⟩ := borel86_ud_exists_fixed_isotropic h hG hG1
  have hiso_eq : ∀ u : Fin 3 → F, u ≠ 0 → Q u = 0 → φ u = u → ∃ c : F, u = c • a := by
    intro u hu0 huQ hφu
    have hGu : (G : GL (Fin 3) F).val *ᵥ u = u := hE u hu0 huQ hφu
    exact borel86_uft_eq_smul_of_isotropic_orth h (u := u) (v := a) ha0 huQ haa (hperp u hGu)
  have hQadd : ∀ v w, φ v = v → φ w = w → Q (v + w) = Q v + Q w := by
    intro v w hv hw
    have hbarQ : h.bar (hform h.bar v w) = hform h.bar v w :=
      borel86_uft_bar_hform_of_fix h hA hv hw
    have hwv : hform h.bar w v = hform h.bar v w := by
      rw [hform_comm h.bar_bar, hbarQ]
    show hform h.bar (v + w) (v + w) = hform h.bar v v + hform h.bar w w
    rw [hform_add_left, hform_add_right, hform_add_right, hwv]
    rw [add_assoc, ← add_assoc (hform h.bar v w) (hform h.bar v w) (hform h.bar w w),
      CharTwo.add_self_eq_zero, zero_add]
  have hr_mul : ∀ v, φ v = v → r v * r v = Q v := by
    intro v hv
    have hbarQ : h.bar (Q v) = Q v := hQfix v hv
    have hexp : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
      rw [← Nat.mul_two, ← pow_succ, Nat.sub_add_cancel h.one_le]
    show Q v ^ 2 ^ (n - 1) * Q v ^ 2 ^ (n - 1) = Q v
    rw [← pow_add, hexp, ← h.bar_apply, hbarQ]
  have hz : ∀ v w, φ v = v → φ w = w → ∃ c : F, r w • v + r v • w = c • a := by
    intro v w hv hw
    have hrv : h.bar (r v) = r v := by
      show h.bar (Q v ^ 2 ^ (n - 1)) = Q v ^ 2 ^ (n - 1)
      rw [map_pow, hQfix v hv]
    have hrw : h.bar (r w) = r w := by
      show h.bar (Q w ^ 2 ^ (n - 1)) = Q w ^ 2 ^ (n - 1)
      rw [map_pow, hQfix w hw]
    have hφrwv : φ (r w • v) = r w • v := by rw [hφsmul, hv, hrw]
    have hφrvw : φ (r v • w) = r v • w := by rw [hφsmul, hw, hrv]
    have hrmw : r w * r w = hform h.bar w w := hr_mul w hw
    have hrmv : r v * r v = hform h.bar v v := hr_mul v hv
    have hQ1 : Q (r w • v) = hform h.bar w w * hform h.bar v v := by
      show hform h.bar (r w • v) (r w • v) = hform h.bar w w * hform h.bar v v
      rw [hform_smul_left, hform_smul_right, hrw, ← mul_assoc, hrmw]
    have hQ2 : Q (r v • w) = hform h.bar v v * hform h.bar w w := by
      show hform h.bar (r v • w) (r v • w) = hform h.bar v v * hform h.bar w w
      rw [hform_smul_left, hform_smul_right, hrv, ← mul_assoc, hrmv]
    have hQz : Q (r w • v + r v • w) = 0 := by
      rw [hQadd (r w • v) (r v • w) hφrwv hφrvw, hQ1, hQ2,
        mul_comm (hform h.bar v v), CharTwo.add_self_eq_zero]
    rcases eq_or_ne (r w • v + r v • w) 0 with h0 | h0
    · exact ⟨0, by rw [h0, zero_smul]⟩
    · exact hiso_eq _ h0 hQz (by rw [hφadd, hφrwv, hφrvw])
  have hmain : ∃ u₁ : Fin 3 → F, ∀ v, φ v = v → ∃ x y : F, v = x • a + y • u₁ := by
    by_cases hex : ∃ u₁ : Fin 3 → F, φ u₁ = u₁ ∧ Q u₁ ≠ 0
    · obtain ⟨u₁, hu₁, hQu₁⟩ := hex
      refine ⟨u₁, fun v hv => ?_⟩
      have hru₁ : r u₁ ≠ 0 := by
        intro h0
        exact hQu₁ (by rw [← hr_mul u₁ hu₁, h0, mul_zero])
      obtain ⟨c, hc⟩ := hz v u₁ hv hu₁
      have hmul : r u₁ • v = c • a + r v • u₁ := by
        rw [← hc, add_assoc, borel86_uft_add_self_eq_zero_vec h (r v • u₁), add_zero]
      refine ⟨(r u₁)⁻¹ * c, (r u₁)⁻¹ * r v, ?_⟩
      simpa only [smul_add, smul_smul, inv_mul_cancel₀ hru₁, one_smul] using
        congrArg (fun z => (r u₁)⁻¹ • z) hmul
    · refine ⟨a, fun v hv => ?_⟩
      by_cases hv0 : v = 0
      · exact ⟨0, 0, by rw [hv0]; simp⟩
      · have hQv : Q v = 0 := by
          by_contra hQv
          exact hex ⟨v, hv, hQv⟩
        obtain ⟨c, hc⟩ := hiso_eq v hv0 hQv hv
        exact ⟨c, 0, by rw [hc]; simp⟩
  obtain ⟨u₁, hspan⟩ := hmain
  obtain ⟨w, hw⟩ := borel86_uft_exists_not_mem_span a u₁
  obtain ⟨θ, hθ⟩ := h.exists_bar_ne
  obtain ⟨x, y, hx, hy, hwxy⟩ := borel86_uft_exists_decomp h hAA hθ w
  obtain ⟨x₁, x₂, hx'⟩ := hspan x hx
  obtain ⟨y₁, y₂, hy'⟩ := hspan y hy
  exact hw (x₁ + θ * y₁) (x₂ + θ * y₂) (by
    rw [hwxy, hx', hy']
    module)

end CFSG.LocalAnalysis.WeakClosure81

end
