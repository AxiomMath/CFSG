module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpFreeL
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpPlus
import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank
open Matrix
open scoped MatrixGroups

namespace Item211Lie3Proof

open Item211Lie2Proof
open CFSG.RankThree.SubgroupLists (spForm spGram transpose_mul_spGram_mul)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjAut mem_gsp)

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem frConj_add (h : GL V₄ K) (M N : Matrix V₄ V₄ K) :
    frConj h (M + N) = frConj h M + frConj h N := by
  rw [frConj, frConj, frConj, Matrix.mul_add, Matrix.add_mul]

theorem frConj_smul (h : GL V₄ K) (c : K) (M : Matrix V₄ V₄ K) :
    frConj h (c • M) = c • frConj h M := by
  rw [frConj, frConj, Matrix.mul_smul, Matrix.smul_mul]

theorem cancel_left_of_mul_eq_one {R R' Y Y' : Matrix V₄ V₄ K} (hR : R * R' = 1)
    (h : R * Y = R * Y') : Y = Y' := by
  have hR' : R' * R = 1 := mul_eq_one_comm.mp hR
  calc Y = R' * R * Y := by rw [hR', Matrix.one_mul]
    _ = R' * (R * Y') := by rw [Matrix.mul_assoc, h]
    _ = Y' := by rw [← Matrix.mul_assoc, hR', Matrix.one_mul]

theorem xiMat_comm_xiMat_zero_iff (h3 : (3 : K) ≠ 0) (P S X : Matrix (Fin 2) (Fin 2) K) :
    xiMat P S * xiMat X 0 = xiMat X 0 * xiMat P S ↔ P * X = X * P ∧ S * X = X * S := by
  rw [xiMat_mul h3, xiMat_mul h3]
  simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, sub_zero, zero_add, add_zero]
  constructor
  · intro h
    exact xiMat_injective h3 h
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem frConj_root_commute (h3 : (3 : K) ≠ 0) {G : Matrix V₄ V₄ K} {h : GL V₄ K}
    (h2 : (2 : K) ≠ 0)
    (hj : ((2 : K) • G + 1) * (h : Matrix V₄ V₄ K) = (h : Matrix V₄ V₄ K) * jStd)
    (g : Matrix (Fin 2) (Fin 2) K) :
    frConj h G * xiMat g 0 = xiMat g 0 * frConj h G := by
  have hjf : frConj h ((2 : K) • G + 1) = jStd := by
    rw [frConj, Matrix.mul_assoc, hj, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  rw [frConj_add, frConj_smul, frConj_one] at hjf
  have hG : frConj h G = (2 : K)⁻¹ • (jStd - 1) := by
    rw [← hjf, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hG, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, (xiMat_commute_jStd h3 g 0).symm]


theorem rSc_xi_mul_rSc_xi (h3 : (3 : K) ≠ 0) (α β a b : K) (M X : Matrix (Fin 2) (Fin 2) K) :
    rSc α β * xiMat M 0 * (rSc a b * xiMat X 0) = rSc α β * rSc a b * xiMat (M * X) 0 := by
  rw [← xiMat_mul_xiMat_zero h3, Matrix.mul_assoc, ← Matrix.mul_assoc (xiMat M 0),
    ← rSc_comm h3 a b M 0]
  simp only [Matrix.mul_assoc]

theorem rSc_mul_comm (h3 : (3 : K) ≠ 0) (α β a b : K) :
    rSc α β * rSc a b = rSc a b * rSc α β :=
  (rSc_comm h3 a b (α • 1) (β • 1)).symm

theorem rSc_mul_comm_of_mul_comm (h3 : (3 : K) ≠ 0) (α β a b : K)
    {M X : Matrix (Fin 2) (Fin 2) K} (h : M * X = X * M) :
    rSc α β * xiMat M 0 * (rSc a b * xiMat X 0) = rSc a b * xiMat X 0 * (rSc α β * xiMat M 0) := by
  rw [rSc_xi_mul_rSc_xi h3, rSc_xi_mul_rSc_xi h3, rSc_mul_comm h3 a b, h]

theorem mul_comm_of_rSc_mul_comm (h3 : (3 : K) ≠ 0) {α β a b : K}
    {M X : Matrix (Fin 2) (Fin 2) K} {R₁ R₂ : Matrix V₄ V₄ K} (h₁ : rSc α β * R₁ = 1)
    (h₂ : rSc a b * R₂ = 1)
    (h : rSc α β * xiMat M 0 * (rSc a b * xiMat X 0) =
      rSc a b * xiMat X 0 * (rSc α β * xiMat M 0)) : M * X = X * M := by
  rw [rSc_xi_mul_rSc_xi h3, rSc_xi_mul_rSc_xi h3, rSc_mul_comm h3 a b] at h
  have hinv : rSc α β * rSc a b * (R₂ * R₁) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (rSc a b), h₂, Matrix.one_mul, h₁]
  exact (xiMat_injective h3 (cancel_left_of_mul_eq_one hinv h)).1

set_option maxHeartbeats 400000 in
theorem commute_of_similitude (h3 : (3 : K) ≠ 0) (hS : StatedSp 2 K) {x₀ q₀ : StatedSp 2 K}
    {A : GL V₄ K} {Q : Subgroup (MulAut (StatedProj (StatedSp 2 K)))} (hQ2 : IsPGroup 2 Q)
    (hq : MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) ∈ Q)
    (hxN : MulAut.conj (x₀ : StatedProj (StatedSp 2 K)) ∈
      Subgroup.normalizer (Q : Set (MulAut (StatedProj (StatedSp 2 K)))))
    (hx₀3 : (x₀ : GL V₄ K) ^ 3 = 1) (hAx : A * x₀ = x₀ * A)
    (hAq : (q₀ : GL V₄ K) * A = A * q₀ ∨ (q₀ : GL V₄ K) * A = -(A * q₀))
    (hcj : frConj (hS : GL V₄ K) (((q₀ * x₀ * q₀⁻¹ * x₀⁻¹ : StatedSp 2 K) : GL V₄ K) :
        Matrix V₄ V₄ K) * jStd =
      jStd * frConj (hS : GL V₄ K) (((q₀ * x₀ * q₀⁻¹ * x₀⁻¹ : StatedSp 2 K) : GL V₄ K) :
        Matrix V₄ V₄ K))
    {α' β' a b : K} {MA X : Matrix (Fin 2) (Fin 2) K}
    (hAdec : frConj (hS : GL V₄ K) (A : Matrix V₄ V₄ K) = rSc α' β' * xiMat MA 0)
    (hMA : ¬ IsScalar2 MA)
    (hXdec : frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) = rSc a b * xiMat X 0)
    {R₂ : Matrix V₄ V₄ K} (hrx : rSc a b * R₂ = 1) :
    MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) * MulAut.conj (x₀ : StatedProj _) =
      MulAut.conj (x₀ : StatedProj _) * MulAut.conj (q₀ : StatedProj _) := by
  have hrA : rSc α' β' * (xiMat MA 0 * frConj (hS : GL V₄ K) ((A⁻¹ : GL V₄ K) :
      Matrix V₄ V₄ K)) = 1 := by
    rw [← Matrix.mul_assoc, ← hAdec, ← frConj_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, frConj_one]
  have hMX : MA * X = X * MA := by
    have e := congrArg (fun g : GL V₄ K => frConj (hS : GL V₄ K) (g : Matrix V₄ V₄ K)) hAx
    simp only [Units.val_mul, frConj_mul] at e
    rw [hAdec, hXdec] at e
    exact mul_comm_of_rSc_mul_comm h3 hrA hrx e
  set cS : StatedSp 2 K := q₀ * x₀ * q₀⁻¹ * x₀⁻¹ with hcS
  have hcSc : ((cS : GL V₄ K)) = (q₀ : GL V₄ K) * x₀ * (q₀ : GL V₄ K)⁻¹ * (x₀ : GL V₄ K)⁻¹ := by
    rw [hcS, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv]
  have hcA : (cS : GL V₄ K) * A = A * cS := by
    rw [hcSc]
    exact commute_commutator_of_signs hAx.symm hAq
  set Cm := frConj (hS : GL V₄ K) ((cS : GL V₄ K) : Matrix V₄ V₄ K) with hCmdef
  have hCx := eq_xiMat_of_commute h3 hcj
  set P := !![Cm (Sum.inl 0) (Sum.inl 0), Cm (Sum.inl 0) (Sum.inr 0);
    Cm (Sum.inr 0) (Sum.inl 0), Cm (Sum.inr 0) (Sum.inr 0)] with hP
  set S := !![Cm (Sum.inl 1) (Sum.inl 0), Cm (Sum.inl 1) (Sum.inr 0);
    Cm (Sum.inr 1) (Sum.inl 0) / 3, Cm (Sum.inr 1) (Sum.inr 0) / 3] with hS'
  have hCA : Cm * xiMat MA 0 = xiMat MA 0 * Cm := by
    have e := congrArg (fun g : GL V₄ K => frConj (hS : GL V₄ K) (g : Matrix V₄ V₄ K)) hcA
    simp only [Units.val_mul, frConj_mul] at e
    rw [hAdec, ← hCmdef] at e
    have e2 : rSc α' β' * (Cm * xiMat MA 0) = rSc α' β' * (xiMat MA 0 * Cm) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← e, hCx, rSc_comm h3, Matrix.mul_assoc]
    exact cancel_left_of_mul_eq_one hrA e2
  rw [hCx] at hCA
  obtain ⟨hPM, hSM⟩ := (xiMat_comm_xiMat_zero_iff h3 P S MA).mp hCA
  have hPX : P * X = X * P := commute_of_commute_nonscalar hMA hPM.symm hMX
  have hSX : S * X = X * S := commute_of_commute_nonscalar hMA hSM.symm hMX
  have hCX : Cm * frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) =
      frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) * Cm := by
    rw [hXdec, hCx]
    calc xiMat P S * (rSc a b * xiMat X 0) = rSc a b * xiMat P S * xiMat X 0 := by
          rw [← Matrix.mul_assoc, ← rSc_comm h3]
      _ = rSc a b * (xiMat X 0 * xiMat P S) := by
          rw [Matrix.mul_assoc, (xiMat_comm_xiMat_zero_iff h3 P S X).mpr ⟨hPX, hSX⟩]
      _ = rSc a b * xiMat X 0 * xiMat P S := by rw [Matrix.mul_assoc]
  have hcx : (cS : GL V₄ K) * x₀ = x₀ * cS := by
    apply Units.ext
    apply frConj_injective (hS : GL V₄ K)
    rw [Units.val_mul, Units.val_mul, frConj_mul, frConj_mul]
    exact hCX
  have hqb : (q₀ : GL V₄ K) * x₀ * (q₀ : GL V₄ K)⁻¹ = (cS : GL V₄ K) * x₀ := by
    rw [hcSc]
    group
  have hc3 : (cS : GL V₄ K) ^ 3 = 1 := by
    have h4 : (q₀ : GL V₄ K) * (x₀ : GL V₄ K) ^ 3 * (q₀ : GL V₄ K)⁻¹ =
        ((cS : GL V₄ K) * x₀) ^ 3 := by
      rw [← hqb, conj_pow]
    rw [hx₀3, mul_one, mul_inv_cancel, (Commute.mul_pow hcx 3), hx₀3, mul_one] at h4
    exact h4.symm
  have e : MulAut.conj (cS : StatedProj (StatedSp 2 K)) =
      MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) * MulAut.conj (x₀ : StatedProj _) *
        (MulAut.conj (q₀ : StatedProj _))⁻¹ * (MulAut.conj (x₀ : StatedProj _))⁻¹ := by
    rw [hcS, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hcQ : MulAut.conj (cS : StatedProj (StatedSp 2 K)) ∈ Q := by
    have h1 : MulAut.conj (x₀ : StatedProj (StatedSp 2 K)) *
        (MulAut.conj (q₀ : StatedProj (StatedSp 2 K)))⁻¹ *
          (MulAut.conj (x₀ : StatedProj (StatedSp 2 K)))⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp (Q.inv_mem hq)
    rw [e, show MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) * MulAut.conj (x₀ : StatedProj _) *
        (MulAut.conj (q₀ : StatedProj _))⁻¹ * (MulAut.conj (x₀ : StatedProj _))⁻¹ =
      MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) * (MulAut.conj (x₀ : StatedProj _) *
        (MulAut.conj (q₀ : StatedProj _))⁻¹ * (MulAut.conj (x₀ : StatedProj _))⁻¹) by group]
    exact Q.mul_mem hq h1
  have hcS3 : cS ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hc3]
    rfl)
  have hc1 := eq_one_of_pow_three_of_mem hQ2 hcQ (by
    rw [← map_pow, ← QuotientGroup.mk_pow, hcS3, QuotientGroup.mk_one, map_one])
  rw [hc1] at e
  calc MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) * MulAut.conj (x₀ : StatedProj _) =
      (MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) * MulAut.conj (x₀ : StatedProj _) *
        (MulAut.conj (q₀ : StatedProj _))⁻¹ * (MulAut.conj (x₀ : StatedProj _))⁻¹) *
        (MulAut.conj (x₀ : StatedProj _) * MulAut.conj (q₀ : StatedProj _)) := by group
    _ = MulAut.conj (x₀ : StatedProj _) * MulAut.conj (q₀ : StatedProj _) := by
      rw [← e, one_mul]


theorem framePsi_mem [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K)
    (hS : StatedSp 2 K) {x₀ : StatedSp 2 K} {C : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hN : ∀ g, framePsi h3 hS g ∈
      Subgroup.normalizer (C : Set (MulAut (StatedProj (StatedSp 2 K)))))
    {a b : K} {X : Matrix (Fin 2) (Fin 2) K} (hXdet : X.det = 1) (hX3 : X * X * X = 1)
    (hXs : ¬ IsScalar2 X)
    (hXdec : frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) = rSc a b * xiMat X 0)
    (hxC : MulAut.conj (x₀ : StatedProj (StatedSp 2 K)) ∈ C) (g : SL(2, K)) :
    framePsi h3 hS g ∈ C := by
  set Xs : SL(2, K) := ⟨X, hXdet⟩ with hXsdef
  have hXs3 : Xs ^ 3 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_three', Matrix.SpecialLinearGroup.coe_one]
    exact hX3)
  set w : StatedSp 2 K := hS * xiSL h3 Xs * hS⁻¹ with hw
  set z₀ : StatedSp 2 K := w⁻¹ * x₀ with hz₀
  have hzfr : frConj (hS : GL V₄ K) ((z₀ : GL V₄ K) : Matrix V₄ V₄ K) = rSc a b := by
    have hw' : w⁻¹ = hS * xiSL h3 Xs⁻¹ * hS⁻¹ := by
      rw [hw, map_inv]
      group
    have e1 : frConj (hS : GL V₄ K) (((w⁻¹ : StatedSp 2 K) : GL V₄ K) : Matrix V₄ V₄ K) =
        xiMat ((Xs⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 := by
      rw [hw']
      exact frConj_xiSL h3 hS Xs⁻¹
    have e2 : ((Xs⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * X = 1 := by
      rw [show X = ((Xs : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) from rfl,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    change frConj (hS : GL V₄ K) ((((w⁻¹ : StatedSp 2 K) : GL V₄ K) * x₀ : GL V₄ K) :
      Matrix V₄ V₄ K) = _
    rw [Units.val_mul, frConj_mul, e1, hXdec, ← Matrix.mul_assoc, ← rSc_comm h3,
      Matrix.mul_assoc, xiMat_mul_xiMat_zero h3, e2, xiMat_one, Matrix.mul_one]
  have hz : ∀ g', framePsi h3 hS g' * MulAut.conj (z₀ : StatedProj (StatedSp 2 K)) =
      MulAut.conj (z₀ : StatedProj (StatedSp 2 K)) * framePsi h3 hS g' := by
    intro g'
    rw [framePsi_apply, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    apply Subtype.ext
    apply Units.ext
    apply frConj_injective (hS : GL V₄ K)
    change frConj (hS : GL V₄ K) ((((hS * xiSL h3 g' * hS⁻¹ : StatedSp 2 K) : GL V₄ K) *
        z₀ : GL V₄ K) : Matrix V₄ V₄ K) =
      frConj (hS : GL V₄ K) (((z₀ : GL V₄ K) * ((hS * xiSL h3 g' * hS⁻¹ : StatedSp 2 K) :
        GL V₄ K) : GL V₄ K) : Matrix V₄ V₄ K)
    rw [Units.val_mul, Units.val_mul, frConj_mul, frConj_mul, frConj_xiSL, hzfr]
    exact (rSc_comm h3 a b _ 0).symm
  have hXz : framePsi h3 hS Xs * MulAut.conj (z₀ : StatedProj (StatedSp 2 K)) =
      MulAut.conj (x₀ : StatedProj (StatedSp 2 K)) := by
    rw [framePsi_apply, ← map_mul, ← QuotientGroup.mk_mul, ← hw, hz₀, mul_inv_cancel_left]
  exact mem_of_normalizer hK4 h2 (framePsi h3 hS) hN (X := Xs) hXs hXs3 hz
    (by rw [hXz]; exact hxC) g

theorem frConj_comm_of_framePsi [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hK4 : 4 ≤ Nat.card K)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))))
    (hS : StatedSp 2 K) {x₀ q₀ : StatedSp 2 K}
    {Q : Subgroup (MulAut (StatedProj (StatedSp 2 K)))} (hQ2 : IsPGroup 2 Q)
    (hq : MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) ∈ Q)
    (hΨQ : ∀ g, framePsi h3 hS g ∈
      Subgroup.normalizer (Q : Set (MulAut (StatedProj (StatedSp 2 K)))))
    {a b α β : K} {X Mq : Matrix (Fin 2) (Fin 2) K} (hXdet : X.det = 1) (hX3 : X * X * X = 1)
    (hXs : ¬ IsScalar2 X)
    (hXdec : frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) = rSc a b * xiMat X 0)
    (hQdec : frConj (hS : GL V₄ K) ((q₀ : GL V₄ K) : Matrix V₄ V₄ K) = rSc α β * xiMat Mq 0)
    (hQdet : (α ^ 2 + 3 * β ^ 2) * Mq.det = 1) :
    frConj (hS : GL V₄ K) ((q₀ : GL V₄ K) : Matrix V₄ V₄ K) *
        frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) =
      frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) *
        frConj (hS : GL V₄ K) ((q₀ : GL V₄ K) : Matrix V₄ V₄ K) := by
  have hMdet : Mq.det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hQdet
    exact zero_ne_one hQdet
  have hMu : IsUnit Mq.det := isUnit_iff_ne_zero.mpr hMdet
  set X' := Mq * X * Mq⁻¹ with hX'
  have hX'det : X'.det = 1 := by
    rw [hX', Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det Mq).mpr hMu), hXdet]
  set Xs : SL(2, K) := ⟨X, hXdet⟩ with hXsdef
  set Xs' : SL(2, K) := ⟨X', hX'det⟩ with hXs'def
  have hX'M : X' * Mq = Mq * X := by
    rw [hX', Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hMu, Matrix.mul_one]
  have hconj : frConj (hS : GL V₄ K) ((q₀ : GL V₄ K) : Matrix V₄ V₄ K) * xiMat X 0 =
      xiMat X' 0 * frConj (hS : GL V₄ K) ((q₀ : GL V₄ K) : Matrix V₄ V₄ K) := by
    rw [hQdec, Matrix.mul_assoc, xiMat_mul_xiMat_zero h3, ← Matrix.mul_assoc,
      ← rSc_comm h3 α β X' 0, Matrix.mul_assoc, xiMat_mul_xiMat_zero h3, hX'M]
  have hgrp : q₀ * (hS * xiSL h3 Xs * hS⁻¹) = (hS * xiSL h3 Xs' * hS⁻¹) * q₀ := by
    apply Subtype.ext
    apply Units.ext
    apply frConj_injective (hS : GL V₄ K)
    change frConj (hS : GL V₄ K) (((q₀ : GL V₄ K) * ((hS * xiSL h3 Xs * hS⁻¹ : StatedSp 2 K) :
        GL V₄ K) : GL V₄ K) : Matrix V₄ V₄ K) =
      frConj (hS : GL V₄ K) ((((hS * xiSL h3 Xs' * hS⁻¹ : StatedSp 2 K) : GL V₄ K) * q₀ :
        GL V₄ K) : Matrix V₄ V₄ K)
    rw [Units.val_mul, Units.val_mul, frConj_mul, frConj_mul, frConj_xiSL, frConj_xiSL]
    exact hconj
  have hΨ : MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) * framePsi h3 hS Xs =
      framePsi h3 hS Xs' * MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) := by
    rw [framePsi_apply, framePsi_apply, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hgrp]
  have hmem : framePsi h3 hS (Xs' * Xs⁻¹) ∈ Q := by
    have h1 : framePsi h3 hS Xs * (MulAut.conj (q₀ : StatedProj (StatedSp 2 K)))⁻¹ *
        (framePsi h3 hS Xs)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hΨQ Xs) _).mp (Q.inv_mem hq)
    have e : framePsi h3 hS (Xs' * Xs⁻¹) = MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) *
        (framePsi h3 hS Xs * (MulAut.conj (q₀ : StatedProj (StatedSp 2 K)))⁻¹ *
          (framePsi h3 hS Xs)⁻¹) := by
      rw [map_mul, map_inv]
      calc framePsi h3 hS Xs' * (framePsi h3 hS Xs)⁻¹ =
          (framePsi h3 hS Xs' * MulAut.conj (q₀ : StatedProj (StatedSp 2 K))) *
            (MulAut.conj (q₀ : StatedProj (StatedSp 2 K)))⁻¹ * (framePsi h3 hS Xs)⁻¹ := by group
        _ = _ := by rw [← hΨ]; group
    rw [e]
    exact Q.mul_mem hq h1
  have hcen := mem_center_of_pairHom hK4 ((framePsi h3 hS).comp (MonoidHom.fst _ _)) hQ2
    (fun g => hΨQ g) (fun g _ h => framePsi_eq_one h3 hinj hS h) (a := Xs' * Xs⁻¹) (b := 1)
    hmem
  rcases Item211Lie2Proof.eq_one_or_eq_neg_one_of_mem_center hcen with h1 | h1
  · have hXX : X' = X := by
      have e := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K))
        (mul_inv_eq_one.mp h1)
      exact e
    have hMX : Mq * X = X * Mq := by rw [← hX'M, hXX]
    rw [hQdec, hXdec]
    exact rSc_mul_comm_of_mul_comm h3 α β a b hMX
  · exfalso
    have hXX : X' = -X := by
      have e := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K))
        (mul_inv_eq_iff_eq_mul.mp h1)
      simpa using e
    have htr : X'.trace = X.trace := by
      rw [hX', Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hMu,
        Matrix.one_mul]
    have hX1 : X ≠ 1 := fun h => hXs (by rw [h]; exact ⟨rfl, rfl, rfl⟩)
    have htrX := (eq_one_or_trace_eq_neg_one hXdet hX3).resolve_left hX1
    rw [hXX, Matrix.trace_neg, htrX] at htr
    apply h2
    linear_combination htr

theorem excPlus_statedSp_of_free [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hK4 : 4 ≤ Nat.card K)
    (hAut : ∀ α : MulAut (StatedProj (StatedSp 2 K)), ∃ A : gsp 2 K, α = conjAut 2 K A)
    {D : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hDi : D ≤ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).range)
    (hDe : IsElemAbelian 3 D) {d₀ : StatedSp 2 K}
    (hfree : ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) * ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) +
      ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) + 1 = 0)
    (hdD : MulAut.conj (d₀ : StatedProj (StatedSp 2 K)) ∈ D)
    {T : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hTD : T ≤ Subgroup.centralizer (D : Set (MulAut (StatedProj (StatedSp 2 K))))) :
    D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D ((MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).range ⊓
        Subgroup.centralizer ({MulAut.conj (d₀ : StatedProj (StatedSp 2 K))} :
          Set (MulAut (StatedProj (StatedSp 2 K))))) ⊓
        Subgroup.centralizer (T : Set (MulAut (StatedProj (StatedSp 2 K))))) :
          Subgroup (MulAut (StatedProj (StatedSp 2 K)))) :
            Set (MulAut (StatedProj (StatedSp 2 K)))) := by
  classical
  have hZ := center_statedProj_statedSp_eq_bot hK4
  have hinj := Item211Lie2Proof.conj_injective' hZ
  set Cd := (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).range ⊓
    Subgroup.centralizer ({MulAut.conj (d₀ : StatedProj (StatedSp 2 K))} :
      Set (MulAut (StatedProj (StatedSp 2 K)))) with hCd
  set C := conjClosure D Cd with hC
  set H := C ⊓ Subgroup.centralizer (T : Set (MulAut (StatedProj (StatedSp 2 K)))) with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDCd : D ≤ Cd := fun x hx => Subgroup.mem_inf.mpr ⟨hDi hx,
    Subgroup.mem_centralizer_singleton_iff.mpr (hDcomm _ hx _ hdD)⟩
  have hDC : D ≤ C := fun x hx => Subgroup.subset_closure ⟨1, Cd.one_mem, x, hx, by group⟩
  have hCCd : C ≤ Cd := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨g, hg, x, hx, rfl⟩
    exact Cd.mul_mem (Cd.mul_mem hg (hDCd hx)) (Cd.inv_mem hg))
  set G := ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) with hG
  have hG3 : G * G * G = 1 := cube_eq_one_of_root hfree
  have hd3 : (d₀ : GL V₄ K) ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, pow_three', Units.val_one]; exact hG3)
  obtain ⟨h, hh, hj⟩ := exists_frame_free h2 h3 (spForm_skew_of_root d₀.2 hfree)
    (mulVec_sq_of_root hfree)
  obtain ⟨hS, rfl⟩ : ∃ hS : StatedSp 2 K, (hS : GL V₄ K) = h := ⟨⟨h, hh⟩, rfl⟩
  have hfrGL : ∀ N : GL V₄ K, (d₀ : GL V₄ K) * N = N * d₀ →
      frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K) * jStd =
        jStd * frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K) := by
    intro N hN
    refine frConj_commute_jStd hj ?_
    have e := congrArg Units.val hN
    rw [Units.val_mul, Units.val_mul] at e
    exact e.symm
  have hfrSp : ∀ y : StatedSp 2 K,
      (frConj (hS : GL V₄ K) ((y : GL V₄ K) : Matrix V₄ V₄ K))ᵀ * spGram 2 K *
        frConj (hS : GL V₄ K) ((y : GL V₄ K) : Matrix V₄ V₄ K) = spGram 2 K := by
    intro y
    rw [← coe_conj_eq_frConj]
    exact transpose_mul_spGram_mul (hS⁻¹ * y * hS).2
  have hfrGSp : ∀ A : gsp 2 K, ∃ μ : K, μ ≠ 0 ∧
      (frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K))ᵀ * spGram 2 K *
        frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K) = μ • spGram 2 K := by
    intro A
    obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
    refine ⟨μ, μ.ne_zero, ?_⟩
    have hhi := transpose_mul_spGram_mul (hS⁻¹).2
    have hhs := transpose_mul_spGram_mul hS.2
    rw [Subgroup.coe_inv] at hhi
    set Hm := ((hS : GL V₄ K) : Matrix V₄ V₄ K)
    set Hi := (((hS : GL V₄ K)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)
    set Am := ((A : GL V₄ K) : Matrix V₄ V₄ K)
    calc (Hi * Am * Hm)ᵀ * spGram 2 K * (Hi * Am * Hm) =
        Hmᵀ * (Amᵀ * (Hiᵀ * spGram 2 K * Hi) * Am) * Hm := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Hmᵀ * (Amᵀ * spGram 2 K * Am) * Hm := by rw [hhi]
      _ = (μ : K) • spGram 2 K := by
          rw [show Amᵀ * spGram 2 K * Am = (μ : K) • spGram 2 K from hμ, Matrix.mul_smul,
            Matrix.smul_mul, hhs]
  have hTA : ∀ t ∈ T, ∀ A : gsp 2 K, t = conjAut 2 K A → (d₀ : GL V₄ K) * A = A * d₀ := by
    intro t ht A hA
    subst hA
    have e := commute_of_conjAut_commute h2 hinj hd3 A
      (Subgroup.mem_centralizer_iff.mp (hTD ht) _ hdD).symm
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact e.symm)
  have hΨCd : ∀ a : SL(2, K), framePsi h3 hS a ∈ Cd := by
    intro a
    refine Subgroup.mem_inf.mpr ⟨⟨_, (framePsi_apply h3 hS a).symm⟩, ?_⟩
    set w : StatedSp 2 K := hS * xiSL h3 a * hS⁻¹ with hw
    have e1 : frConj (hS : GL V₄ K) ((w : GL V₄ K) : Matrix V₄ V₄ K) =
        xiMat (a : Matrix (Fin 2) (Fin 2) K) 0 := frConj_xiSL h3 hS a
    rw [Subgroup.mem_centralizer_singleton_iff, framePsi_apply, ← hw, ← map_mul, ← map_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    apply Subtype.ext
    apply Units.ext
    apply frConj_injective (hS : GL V₄ K)
    change frConj (hS : GL V₄ K) (((w : GL V₄ K) * d₀ : GL V₄ K) : Matrix V₄ V₄ K) =
      frConj (hS : GL V₄ K) (((d₀ : GL V₄ K) * w : GL V₄ K) : Matrix V₄ V₄ K)
    rw [Units.val_mul, Units.val_mul, frConj_mul, frConj_mul, e1]
    exact (frConj_root_commute h3 h2 hj _).symm
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨x', rfl⟩ := hDi hx
  have hx'3 : x' ^ 3 = 1 := hinj (by rw [map_pow, hDe.2 _ hx, map_one])
  obtain ⟨x₀, rfl, hx₀3⟩ := exists_lift_pow_three hx'3
  have hx₀d : (d₀ : GL V₄ K) * x₀ = x₀ * d₀ := by
    have hc : (x₀ : StatedProj (StatedSp 2 K)) * d₀ = d₀ * x₀ :=
      hinj (by rw [map_mul, map_mul]; exact hDcomm _ hx _ hdD)
    exact (commute_of_pow_three_of_signs (ne_neg_gl h2 _) hx₀3 (comm_or_anticomm_of_mk hc)).symm
  have hqH := hQH hq
  obtain ⟨q₀, rfl, hq₀d⟩ := exists_lift_commute h2 hinj hd3 (hCCd (Subgroup.mem_inf.mp hqH).1)
  have hXj := hfrGL _ hx₀d
  have hQj := hfrGL _ hq₀d
  have hXm3 : frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) *
      frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) *
        frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    have e := congrArg (fun g : GL V₄ K => frConj (hS : GL V₄ K) (g : Matrix V₄ V₄ K)) hx₀3
    simpa only [pow_three', Units.val_mul, frConj_mul, Units.val_one, frConj_one] using e
  obtain ⟨a, b, X, hXdec, hXdet, hX3⟩ := exists_xi_decomp_three h2 h3 hXj (hfrSp x₀) hXm3
  obtain ⟨α, β, Mq, hQdec, hQdet⟩ := exists_xi_decomp h2 h3 one_ne_zero hQj
    (by rw [one_smul]; exact hfrSp q₀)
  have hfin : frConj (hS : GL V₄ K) ((q₀ : GL V₄ K) : Matrix V₄ V₄ K) *
      frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) =
        frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) *
          frConj (hS : GL V₄ K) ((q₀ : GL V₄ K) : Matrix V₄ V₄ K) →
      MulAut.conj (q₀ : StatedProj (StatedSp 2 K)) * MulAut.conj (x₀ : StatedProj _) =
        MulAut.conj (x₀ : StatedProj _) * MulAut.conj (q₀ : StatedProj _) := by
    intro hc
    have e : q₀ * x₀ = x₀ * q₀ := by
      apply Subtype.ext
      apply Units.ext
      apply frConj_injective (hS : GL V₄ K)
      change frConj (hS : GL V₄ K) (((q₀ : GL V₄ K) * x₀ : GL V₄ K) : Matrix V₄ V₄ K) =
        frConj (hS : GL V₄ K) (((x₀ : GL V₄ K) * q₀ : GL V₄ K) : Matrix V₄ V₄ K)
      rw [Units.val_mul, Units.val_mul, frConj_mul, frConj_mul]
      exact hc
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e]
  have hrx : rSc a b * (xiMat X 0 * frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) *
      frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K)) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hXdec, hXm3]
  by_cases hXs : IsScalar2 X
  ·
    apply hfin
    rw [hXdec, hQdec]
    have e : xiMat X 0 = rSc (X 1 1) 0 := by
      rw [rSc, zero_smul, ← eq_smul_one_of_isScalar2 hXs]
    rw [e, rSc_mul h3, rSc_mul_xiMat h3]
    exact (rSc_comm h3 _ _ _ _).symm
  have hxH : MulAut.conj (x₀ : StatedProj (StatedSp 2 K)) ∈ H :=
    Subgroup.mem_inf.mpr ⟨hDC hx, Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_iff.mp (hTD ht) _ hx).symm⟩
  have hxN := CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H hxH
  by_cases hcase : ∃ t ∈ T, ∃ A : gsp 2 K, t = conjAut 2 K A ∧ ∃ (α' β' : K)
      (M : Matrix (Fin 2) (Fin 2) K),
      frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K) = rSc α' β' * xiMat M 0 ∧
        ¬ IsScalar2 M
  ·
    obtain ⟨t, ht, A, rfl, α', β', MA, hAdec, hMA⟩ := hcase
    have hAx : (A : GL V₄ K) * x₀ = x₀ * A := by
      have hs := conjAut_sign A x₀ (fix_of_commute_conj hinj
        (Subgroup.mem_centralizer_iff.mp (hTD ht) _ hx).symm)
      have hs' : (x₀ : GL V₄ K) * A = A * x₀ ∨ (x₀ : GL V₄ K) * A = -(A * x₀) := by
        rcases hs with h' | h'
        · exact Or.inl h'.symm
        · right
          rw [h', neg_neg]
      exact (commute_of_pow_three_of_signs (ne_neg_gl h2 _) hx₀3 hs').symm
    have hAq := conjAut_sign A q₀ (fix_of_commute_conj hinj
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hqH).2 _ ht))
    have hAq' : (q₀ : GL V₄ K) * A = A * q₀ ∨ (q₀ : GL V₄ K) * A = -(A * q₀) := by
      rcases hAq with h' | h'
      · exact Or.inl h'.symm
      · right
        rw [h', neg_neg]
    have hcd : (d₀ : GL V₄ K) * ((q₀ * x₀ * q₀⁻¹ * x₀⁻¹ : StatedSp 2 K) : GL V₄ K) =
        ((q₀ * x₀ * q₀⁻¹ * x₀⁻¹ : StatedSp 2 K) : GL V₄ K) * d₀ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_inv]
      have h1 : Commute (d₀ : GL V₄ K) q₀ := hq₀d
      have h4 : Commute (d₀ : GL V₄ K) x₀ := hx₀d
      exact ((h1.mul_right h4).mul_right h1.inv_right).mul_right h4.inv_right
    exact commute_of_similitude h3 hS hQ2 hq hxN hx₀3 hAx hAq' (hfrGL _ hcd) hAdec hMA hXdec hrx
  ·
    push Not at hcase
    apply hfin
    have hΨT : ∀ g : SL(2, K), framePsi h3 hS g ∈
        Subgroup.centralizer (T : Set (MulAut (StatedProj (StatedSp 2 K)))) := by
      intro g
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨A, rfl⟩ := hAut t
      obtain ⟨μ, hμ0, hμ⟩ := hfrGSp A
      obtain ⟨α', β', M, hAdec, -⟩ := exists_xi_decomp h2 h3 hμ0 (hfrGL _ (hTA _ ht A rfl)) hμ
      obtain ⟨m, hm⟩ : ∃ m : K, M = m • (1 : Matrix (Fin 2) (Fin 2) K) :=
        ⟨_, eq_smul_one_of_isScalar2 (hcase _ ht A rfl α' β' M hAdec)⟩
      have e : frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K) =
          rSc (α' * m) (β' * m) := by
        rw [hAdec, hm, rSc_mul_xiMat h3, rSc, smul_smul, smul_smul]
      exact conjAut_commute_framePsi h3 hS A e g
    have hΨC : ∀ g : SL(2, K), framePsi h3 hS g ∈ C :=
      framePsi_mem h2 h3 hK4 hS (fun g => mem_normalizer_conjClosure (hΨCd g)) hXdet hX3 hXs
        hXdec (hDC hx)
    have hΨQ : ∀ g : SL(2, K), framePsi h3 hS g ∈
        Subgroup.normalizer (Q : Set (MulAut (StatedProj (StatedSp 2 K)))) := fun g =>
      CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H
        (Subgroup.mem_inf.mpr ⟨hΨC g, hΨT g⟩)
    exact frConj_comm_of_framePsi h2 h3 hK4 hinj hS hQ2 hq hΨQ hXdet hX3 hXs hXdec hQdec hQdet

end Item211Lie3Proof

open Item211Lie2Proof Item211Lie3Proof
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjAut)

theorem ks211ExcPlusSp_holds : KS211ExcPlusSp := by
  intro p _ hp3
  set K := GaloisField p 1
  have hK : Nat.card K = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (Fact.out : p.Prime).ne_zero)
  have hn : ∀ n : ℕ, n < p → 0 < n → ((n : ℕ) : K) ≠ 0 := by
    intro n hnp hn0 h
    rw [CharP.cast_eq_zero_iff K p] at h
    have := Nat.le_of_dvd hn0 h
    omega
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast hn 2 (by omega) (by norm_num)
  have h3 : (3 : K) ≠ 0 := by exact_mod_cast hn 3 (by omega) (by norm_num)
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; omega
  have hAut : ∀ α : MulAut (StatedProj (StatedSp 2 K)), ∃ A : gsp 2 K, α = conjAut 2 K A := by
    intro α
    obtain ⟨A, σ, hα⟩ :=
      (CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two (K := K) h2).2 α
    have hσ : σ = 1 := ringEquiv_eq_one_of_card_prime (Fact.out : p.Prime) hK σ
    exact ⟨A, by rw [hα, hσ, map_one, mul_one]⟩
  have hZ := center_statedProj_statedSp_eq_bot hK4
  have hinj := Item211Lie2Proof.conj_injective' hZ
  refine excPlusFor_of_mulEquiv (Sec4.projSpEquivStatedProj 2 K) ?_
  intro D hDi hDe hD9 d hdD hd1 T hT2 hTD
  obtain ⟨y, rfl⟩ := hDi hdD
  have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hDe.2 _ hdD, map_one])
  obtain ⟨d₀, rfl, hd₀3⟩ := exists_lift_pow_three hy3
  have hd₀1 : (d₀ : GL (Fin 2 ⊕ Fin 2) K) ≠ 1 := by
    intro h
    apply hd1
    have e : d₀ = 1 := Subtype.ext h
    rw [e, QuotientGroup.mk_one, map_one]
  by_cases hP : ((d₀ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((d₀ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) +
      ((d₀ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) + 1 = 0
  · exact excPlus_statedSp_of_free h2 h3 hK4 hAut hDi hDe hP hdD hTD
  · exact excPlus_statedSp_of_fixed h2 h3 hK4 hAut hDi hDe hd₀3 hd₀1 hP hdD hTD

end CFSG.RankThree.PartTwo.Sec21
