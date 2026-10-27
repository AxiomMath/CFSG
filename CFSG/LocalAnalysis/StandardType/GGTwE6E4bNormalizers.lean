module

public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bFlag
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel
public import CFSG.LieType.Chevalley.CharTwoWeylLifts
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoA2Holonomy
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee

public section

namespace CFSG.StandardType.TwE6E4bNormalizers

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LieType.AlgebraicGroups
open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.TwE6FixedA2SL3 CFSG.StandardType.TwE6FixedA2Type
open CFSG.StandardType.TwE6HyperplaneTypes
open CFSG.StandardType.TwE6E4bFrame CFSG.StandardType.TwE6E4bFlag CFSG.StandardType.TwE6E4bTorus
open CFSG.StandardType.TableBExc.E6Three
local instance : NeZero Tag.E6.rank := ⟨by decide⟩

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem rootChar_gamma1 (a : Fin Tag.E6.rank → Lˣ) :
    rootChar a gamma1 = a 3 := by
  have h : gamma1 = Pi.single (3 : Fin Tag.E6.rank) 1 := by
    funext i; fin_cases i <;> rfl
  rw [h, rootChar_pi_single]

theorem rootChar_gamma2 (a : Fin Tag.E6.rank → Lˣ) :
    rootChar a gamma2 = a 1 * a 2 * a 3 * a 4 := by
  have h : gamma2 = Pi.single (1 : Fin Tag.E6.rank) 1 + Pi.single 2 1 +
      Pi.single 3 1 + Pi.single 4 1 := by
    funext i; fin_cases i <;> rfl
  rw [h, rootChar_add, rootChar_add, rootChar_add]
  simp [rootChar_pi_single]

theorem rootChar_gamma3 (a : Fin Tag.E6.rank → Lˣ) :
    rootChar a gamma3 = a 1 * a 2 * a 3 ^ 2 * a 4 := by
  have h : gamma3 = Pi.single (1 : Fin Tag.E6.rank) 1 + Pi.single 2 1 +
      (2 : ℕ) • Pi.single 3 1 + Pi.single 4 1 := by
    funext i; fin_cases i <;> rfl
  rw [h, rootChar_add, rootChar_add, rootChar_add, rootChar_nsmul_single]
  simp [rootChar_pi_single]

theorem rootChar_neg_eq_inv (a : Fin Tag.E6.rank → Lˣ) (α : Fin Tag.E6.rank → ℤ) :
    rootChar a (-α) = (rootChar a α)⁻¹ := by
  have h : -α = 0 - α := by abel
  rw [h, rootChar_sub, rootChar_zero, one_mul]

noncomputable def canonicalY : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L cE6

theorem canonicalY_mem_monomial : canonicalY (L := L) ∈ monomialSubgroup Tag.E6 L :=
  canonicalRep_mem_monomialSubgroup L cE6

theorem canonicalY_weylQuotientHom :
    weylQuotientHom Tag.E6 L ⟨canonicalY (L := L), canonicalY_mem_monomial⟩ = cE6 :=
  weylQuotientHom_eq (mapsRootLines_canonicalRep cE6)

theorem canonicalY_fixes_rootVec {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ fixedA2E6) :
    (canonicalY (L := L) : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L γ) =
      rootVec Tag.E6 L γ := by
  have hroot : IsRoot Tag.E6 γ := isRoot_of_mem_fixedA2E6 hγ
  have hcfix : cE6 • γ = γ := by
    rw [cE6_smul]
    exact cAct_fixedA2E6 γ hγ
  obtain ⟨ε, hε, hY⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner.canonicalRep_rootVec_sign
      (L := L) cE6 hroot
  rw [hcfix] at hY
  rcases hε with rfl | hε
  · simpa [canonicalY] using hY
  · rw [hε] at hY
    simpa [canonicalY, CharTwo.neg_eq] using hY

theorem exists_torusTuple_of_weyl_c
    {E : Subgroup (ModGL Tag.E6 L)}
    (hEM : E ≤ monomialSubgroup Tag.E6 L)
    {n : ModGL Tag.E6 L} (hnE : n ∈ E)
    (hnc : weylQuotientHom Tag.E6 L ⟨n, hEM hnE⟩ = cE6) :
    ∃ b : Fin Tag.E6.rank → Lˣ, n * (canonicalY (L := L))⁻¹ = rootDiagUnit Tag.E6 b := by
  classical
  let d : ModGL Tag.E6 L := n * (canonicalY (L := L))⁻¹
  have hYmem : canonicalY (L := L) ∈ monomialSubgroup Tag.E6 L := canonicalY_mem_monomial
  have hdmem : d ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (hEM hnE) (inv_mem hYmem)
  have hdsub : (⟨d, hdmem⟩ : monomialSubgroup Tag.E6 L) =
      ⟨n, hEM hnE⟩ * (⟨canonicalY (L := L), hYmem⟩ : monomialSubgroup Tag.E6 L)⁻¹ :=
    Subtype.ext rfl
  have hdweyl : weylQuotientHom Tag.E6 L ⟨d, hdmem⟩ = 1 := by
    rw [hdsub, map_mul, map_inv, hnc, canonicalY_weylQuotientHom, mul_inv_cancel]
  have hdT : d ∈ torusGroup Tag.E6 L :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_torusGroup_of_weylQuotientHom_eq_one
      hdmem hdweyl
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdT
  exact ⟨b, hb⟩

theorem normRoute_PQ
    {E : Subgroup (ModGL Tag.E6 L)}
    (hEM : E ≤ monomialSubgroup Tag.E6 L)
    (hE : CFSG.Open.IsElemAbelian 3 E)
    {n : ModGL Tag.E6 L} (hnE : n ∈ E)
    (hnc : weylQuotientHom Tag.E6 L ⟨n, hEM hnE⟩ = cE6) :
    ∃ b : Fin Tag.E6.rank → Lˣ,
      n * (canonicalY (L := L))⁻¹ = rootDiagUnit Tag.E6 b ∧
      b 1 * b 2 * b 4 = 1 ∧ b 3 ^ 3 = 1 := by
  classical
  obtain ⟨b, hb⟩ := exists_torusTuple_of_weyl_c hEM hnE hnc
  have hn_eq : n = rootDiagUnit Tag.E6 b * canonicalY (L := L) := by
    rw [← hb]
    group
  have hroot1 : IsRoot Tag.E6 (Pi.single (1 : Fin Tag.E6.rank) 1) := isRoot_single _ _
  have hroot2 : IsRoot Tag.E6 (Pi.single (2 : Fin Tag.E6.rank) 1) := isRoot_single _ _
  have hroot3 : IsRoot Tag.E6 (Pi.single (3 : Fin Tag.E6.rank) 1) := isRoot_single _ _
  have hroot4 : IsRoot Tag.E6 (Pi.single (4 : Fin Tag.E6.rank) 1) := isRoot_single _ _
  have hc1 : cE6 • (Pi.single (1 : Fin Tag.E6.rank) (1 : ℤ) : Fin Tag.E6.rank → ℤ) = (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := by
    rw [cE6_smul]; decide +kernel
  have hc2 : cE6 • (Pi.single (2 : Fin Tag.E6.rank) (1 : ℤ) : Fin Tag.E6.rank → ℤ) = (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) := by
    rw [cE6_smul]; decide +kernel
  have hc4 : cE6 • (Pi.single (4 : Fin Tag.E6.rank) (1 : ℤ) : Fin Tag.E6.rank → ℤ) = (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) := by
    rw [cE6_smul]; decide +kernel
  have hc3 : cE6 • (Pi.single (3 : Fin Tag.E6.rank) (1 : ℤ) : Fin Tag.E6.rank → ℤ) = (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) := by
    rw [cE6_smul]; decide +kernel
  have hYroot (i : Fin Tag.E6.rank) (hroot : IsRoot Tag.E6 (Pi.single i 1))
      (ci : cE6 • (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) = (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) :
      (canonicalY (L := L) : Module.End L (RootModule Tag.E6 L))
        (rootVec Tag.E6 L (Pi.single i 1)) = rootVec Tag.E6 L (Pi.single i 1) := by
    obtain ⟨ε, hε, hY⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner.canonicalRep_rootVec_sign
        (L := L) cE6 hroot
    rw [ci] at hY
    rcases hε with rfl | hε
    · simpa [canonicalY] using hY
    · rw [hε] at hY
      simpa [canonicalY, CharTwo.neg_eq] using hY
  have hY1 : (canonicalY (L := L) : Module.End L (RootModule Tag.E6 L))
      (rootVec Tag.E6 L (Pi.single 1 1)) = rootVec Tag.E6 L (Pi.single 2 1) := by
    obtain ⟨ε, hε, hY⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner.canonicalRep_rootVec_sign
        (L := L) cE6 hroot1
    rw [hc1] at hY
    rcases hε with rfl | hε
    · simpa [canonicalY] using hY
    · rw [hε] at hY
      simpa [canonicalY, CharTwo.neg_eq] using hY
  have hY2 : (canonicalY (L := L) : Module.End L (RootModule Tag.E6 L))
      (rootVec Tag.E6 L (Pi.single 2 1)) = rootVec Tag.E6 L (Pi.single 4 1) := by
    obtain ⟨ε, hε, hY⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner.canonicalRep_rootVec_sign
        (L := L) cE6 hroot2
    rw [hc2] at hY
    rcases hε with rfl | hε
    · simpa [canonicalY] using hY
    · rw [hε] at hY
      simpa [canonicalY, CharTwo.neg_eq] using hY
  have hY4 : (canonicalY (L := L) : Module.End L (RootModule Tag.E6 L))
      (rootVec Tag.E6 L (Pi.single 4 1)) = rootVec Tag.E6 L (Pi.single 1 1) := by
    obtain ⟨ε, hε, hY⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner.canonicalRep_rootVec_sign
        (L := L) cE6 hroot4
    rw [hc4] at hY
    rcases hε with rfl | hε
    · simpa [canonicalY] using hY
    · rw [hε] at hY
      simpa [canonicalY, CharTwo.neg_eq] using hY
  have hY3 := hYroot 3 hroot3 hc3
  have hn1 : (n : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L (Pi.single 1 1)) =
      (b 2 : L) • rootVec Tag.E6 L (Pi.single 2 1) := by
    rw [hn_eq, Units.val_mul, Module.End.mul_apply, hY1]
    change (rootDiag b) (rootVec Tag.E6 L (Pi.single 2 1)) = _
    rw [rootDiag_rootVec b hroot2, rootChar_pi_single]
  have hn2 : (n : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L (Pi.single 2 1)) =
      (b 4 : L) • rootVec Tag.E6 L (Pi.single 4 1) := by
    rw [hn_eq, Units.val_mul, Module.End.mul_apply, hY2]
    change (rootDiag b) (rootVec Tag.E6 L (Pi.single 4 1)) = _
    rw [rootDiag_rootVec b hroot4, rootChar_pi_single]
  have hn4 : (n : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L (Pi.single 4 1)) =
      (b 1 : L) • rootVec Tag.E6 L (Pi.single 1 1) := by
    rw [hn_eq, Units.val_mul, Module.End.mul_apply, hY4]
    change (rootDiag b) (rootVec Tag.E6 L (Pi.single 1 1)) = _
    rw [rootDiag_rootVec b hroot1, rootChar_pi_single]
  have hn3 : (n : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L (Pi.single 3 1)) =
      (b 3 : L) • rootVec Tag.E6 L (Pi.single 3 1) := by
    rw [hn_eq, Units.val_mul, Module.End.mul_apply, hY3]
    change (rootDiag b) (rootVec Tag.E6 L (Pi.single 3 1)) = _
    rw [rootDiag_rootVec b hroot3, rootChar_pi_single]
  have hn3pow : n ^ 3 = 1 := hE.2 n hnE
  have hcalc1 : (n : Module.End L (RootModule Tag.E6 L))
      ((n : Module.End L (RootModule Tag.E6 L))
        ((n : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L (Pi.single 1 1)))) =
      (((b 1 * b 2 * b 4 : Lˣ) : L)) • rootVec Tag.E6 L (Pi.single 1 1) := by
    rw [hn1]
    simp only [map_smul]
    rw [hn2]
    simp only [map_smul]
    rw [hn4]
    simp only [smul_smul]
    congr 1
    simp [mul_comm, mul_left_comm, mul_assoc]
  have hPvec : (((b 1 * b 2 * b 4 : Lˣ) : L)) • rootVec Tag.E6 L (Pi.single 1 1) =
      rootVec Tag.E6 L (Pi.single 1 1) := by
    have h := congrArg (fun m : ModGL Tag.E6 L => (m : Module.End L (RootModule Tag.E6 L))
      (rootVec Tag.E6 L (Pi.single 1 1))) hn3pow
    have hcomp : (n ^ 3 : ModGL Tag.E6 L) = n * n * n := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
        show (2 : ℕ) = 1 + 1 by norm_num, pow_succ, pow_one]
    rw [hcomp, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hcalc1] at h
    simpa using h
  have hPfield : (((b 1 * b 2 * b 4 : Lˣ) : L)) = 1 := by
    have h := congrArg (fun w : RootModule Tag.E6 L =>
      w (Sum.inr ⟨Pi.single (1 : Fin Tag.E6.rank) 1, hroot1⟩)) hPvec
    rw [rootVec_eq_single_of_isRoot hroot1] at h
    simpa [Finsupp.smul_apply, Finsupp.single_eq_same] using h
  have hcalc3 : (n : Module.End L (RootModule Tag.E6 L))
      ((n : Module.End L (RootModule Tag.E6 L))
        ((n : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L (Pi.single 3 1)))) =
      ((b 3 ^ 3 : Lˣ) : L) • rootVec Tag.E6 L (Pi.single 3 1) := by
    simp [hn3, smul_smul, pow_succ, mul_assoc]
  have hQvec : ((b 3 ^ 3 : Lˣ) : L) • rootVec Tag.E6 L (Pi.single 3 1) =
      rootVec Tag.E6 L (Pi.single 3 1) := by
    have h := congrArg (fun m : ModGL Tag.E6 L => (m : Module.End L (RootModule Tag.E6 L))
      (rootVec Tag.E6 L (Pi.single 3 1))) hn3pow
    have hcomp : (n ^ 3 : ModGL Tag.E6 L) = n * n * n := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
        show (2 : ℕ) = 1 + 1 by norm_num, pow_succ, pow_one]
    rw [hcomp, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hcalc3] at h
    simpa using h
  have hQfield : ((b 3 ^ 3 : Lˣ) : L) = 1 := by
    have h := congrArg (fun w : RootModule Tag.E6 L =>
      w (Sum.inr ⟨Pi.single (3 : Fin Tag.E6.rank) 1, hroot3⟩)) hQvec
    rw [rootVec_eq_single_of_isRoot hroot3] at h
    simpa [Finsupp.smul_apply, Finsupp.single_eq_same] using h
  exact ⟨b, hb, Units.ext hPfield, Units.ext hQfield⟩

noncomputable def actualn' (n : ModGL Tag.E6 L) (k : ℤ) : ModGL Tag.E6 L :=
  (frameT (L := L)) ^ (-k) * n

theorem frameT_eq_diagTuple :
    frameT (L := L) = rootDiagUnit Tag.E6
      (diagTuple (1 : Lˣ) (frameOmega (L := L))) := by
  rw [frameT_eq, frameRho0]
  change fixedA2Rho L (diagSL3 1 (frameOmega (L := L))) = _
  rw [fixedA2Rho_diagSL3]

theorem n_rootVec_fixed {n : ModGL Tag.E6 L} {b : Fin Tag.E6.rank → Lˣ}
    (hn : n = rootDiagUnit Tag.E6 b * canonicalY (L := L))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ fixedA2E6) :
    (n : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L γ) =
      (rootChar b γ : L) • rootVec Tag.E6 L γ := by
  rw [hn, Units.val_mul, Module.End.mul_apply, canonicalY_fixes_rootVec hγ]
  change (rootDiag b) (rootVec Tag.E6 L γ) = _
  rw [rootDiag_rootVec b (isRoot_of_mem_fixedA2E6 hγ)]

theorem frameT_rootVec_fixed {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ fixedA2E6) :
    (frameT (L := L) : Module.End L (RootModule Tag.E6 L))
        (rootVec Tag.E6 L γ) =
      (rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) γ : L) •
        rootVec Tag.E6 L γ := by
  rw [frameT_eq_diagTuple]
  change (rootDiag (diagTuple (1 : Lˣ) (frameOmega (L := L))))
    (rootVec Tag.E6 L γ) = _
  rw [rootDiag_rootVec _ (isRoot_of_mem_fixedA2E6 hγ)]

theorem frameT_pow_rootVec_fixed (m : ℕ) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ fixedA2E6) :
    ((frameT (L := L) ^ m : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L))
        (rootVec Tag.E6 L γ) =
      ((rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) γ : L) ^ m) •
        rootVec Tag.E6 L γ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Units.val_mul, Module.End.mul_apply, frameT_rootVec_fixed hγ,
        map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem frameT_orderOf : orderOf (frameT (L := L)) = 3 := by
  apply orderOf_eq_prime (frameT_pow_three (L := L))
  intro h
  apply frameT_not_mem_zpowers_frameA (L := L)
  rw [h]
  exact Subgroup.one_mem _

theorem frameT_zpow_neg_two_mul (r : Fin 3) :
    (frameT (L := L)) ^ (-(2 * (r : ℤ))) =
      (frameT (L := L)) ^ (r : ℕ) := by
  rw [show (frameT (L := L)) ^ (r : ℕ) = (frameT (L := L)) ^ (r : ℤ) by
    rw [zpow_natCast]]
  rw [zpow_eq_zpow_iff_modEq]
  rw [frameT_orderOf]
  rw [Int.ModEq]
  fin_cases r <;> norm_num

theorem rootChar_diagTuple_gamma1 :
    rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) gamma1 =
      frameOmega (L := L) ^ 2 := by
  rw [rootChar_gamma1, diagTuple_explicit]
  simp [frameOmega_inv]

theorem rootChar_diagTuple_gamma2 :
    rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) gamma2 =
      frameOmega (L := L) ^ 2 := by
  rw [rootChar_gamma2, diagTuple_explicit]
  have hz : (frameOmega (L := L)) ^ (5 : ℤ) =
      (frameOmega (L := L)) ^ (2 : ℤ) :=
    frameOmega_zpow_eq_of_eq_add_three_mul (a := 5) (b := 2) (m := 1) (by norm_num)
  simpa [zpow_natCast, pow_succ, pow_two, mul_assoc] using hz

theorem rootChar_diagTuple_gamma3 :
    rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) gamma3 =
      frameOmega (L := L) := by
  rw [rootChar_gamma3, diagTuple_explicit]
  have hz : (frameOmega (L := L)) ^ (7 : ℤ) =
      (frameOmega (L := L)) ^ (1 : ℤ) :=
    frameOmega_zpow_eq_of_eq_add_three_mul (a := 7) (b := 1) (m := 2) (by norm_num)
  simpa [zpow_natCast, pow_succ, pow_two, mul_assoc] using hz

theorem n1_scalar_eq_one {b : Fin Tag.E6.rank → Lˣ} {r : Fin 3}
    (hb3 : b 3 = frameOmega (L := L) ^ (r : ℕ))
    (hP : b 1 * b 2 * b 4 = 1) :
    ∀ γ ∈ fixedA2E6,
      (rootChar b γ : L) *
        ((rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) γ : L) ^ (r : ℕ)) = 1 := by
  intro γ hγ
  have hb2 : b 1 * b 2 * b 3 * b 4 = b 3 := by
    calc b 1 * b 2 * b 3 * b 4 = (b 1 * b 2 * b 4) * b 3 := by ac_rfl
      _ = b 3 := by rw [hP, one_mul]
  have hb3sq : b 1 * b 2 * b 3 ^ 2 * b 4 = b 3 ^ 2 := by
    calc b 1 * b 2 * b 3 ^ 2 * b 4 = (b 1 * b 2 * b 4) * b 3 ^ 2 := by ac_rfl
      _ = b 3 ^ 2 := by rw [hP, one_mul]
  have hpow2 : (frameOmega (L := L) ^ (r : ℕ)) *
      ((frameOmega (L := L) ^ 2) ^ (r : ℕ)) = 1 := by
    rw [← mul_pow, frameOmega_mul_sq, one_pow]
  have hpow3 : (frameOmega (L := L) ^ (r : ℕ)) ^ 2 *
      (frameOmega (L := L) ^ (r : ℕ)) = 1 := by
    rw [← pow_mul, ← pow_add]
    rw [show (r : ℕ) * 2 + r = 3 * r by ring, pow_mul, frameOmega_pow_three, one_pow]
  rcases (mem_fixedA2E6.mp hγ) with rfl | rfl | rfl | rfl | rfl | rfl
  · have hunit : rootChar b gamma1 *
        (rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) gamma1) ^ (r : ℕ) = 1 := by
      rw [rootChar_gamma1, rootChar_diagTuple_gamma1, hb3]
      exact hpow2
    simpa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Lˣ => (u : L)) hunit
  · have hunit : rootChar b gamma2 *
        (rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) gamma2) ^ (r : ℕ) = 1 := by
      rw [rootChar_gamma2, rootChar_diagTuple_gamma2, hb2, hb3]
      exact hpow2
    simpa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Lˣ => (u : L)) hunit
  · have hunit : rootChar b gamma3 *
        (rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) gamma3) ^ (r : ℕ) = 1 := by
      rw [rootChar_gamma3, rootChar_diagTuple_gamma3, hb3sq, hb3]
      exact hpow3
    simpa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Lˣ => (u : L)) hunit
  · have hunit : rootChar b (-gamma1) *
        (rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) (-gamma1)) ^ (r : ℕ) = 1 := by
      rw [rootChar_neg_eq_inv, rootChar_neg_eq_inv, rootChar_gamma1,
        rootChar_diagTuple_gamma1]
      rw [inv_pow, ← mul_inv]
      rw [show b 3 * (frameOmega (L := L) ^ 2) ^ (r : ℕ) = 1 by
        rw [hb3]; exact hpow2]
      rw [inv_one]
    simpa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Lˣ => (u : L)) hunit
  · have hunit : rootChar b (-gamma2) *
        (rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) (-gamma2)) ^ (r : ℕ) = 1 := by
      rw [rootChar_neg_eq_inv, rootChar_neg_eq_inv, rootChar_gamma2,
        rootChar_diagTuple_gamma2]
      rw [inv_pow, ← mul_inv]
      rw [show b 1 * b 2 * b 3 * b 4 * (frameOmega (L := L) ^ 2) ^ (r : ℕ) = 1 by
        rw [hb2, hb3]; exact hpow2]
      rw [inv_one]
    simpa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Lˣ => (u : L)) hunit
  · have hunit : rootChar b (-gamma3) *
        (rootChar (diagTuple (1 : Lˣ) (frameOmega (L := L))) (-gamma3)) ^ (r : ℕ) = 1 := by
      rw [rootChar_neg_eq_inv, rootChar_neg_eq_inv, rootChar_gamma3,
        rootChar_diagTuple_gamma3]
      rw [inv_pow, ← mul_inv]
      rw [show b 1 * b 2 * b 3 ^ 2 * b 4 * (frameOmega (L := L)) ^ (r : ℕ) = 1 by
        rw [hb3sq, hb3]; exact hpow3]
      rw [inv_one]
    simpa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Lˣ => (u : L)) hunit

theorem n1_rootVec_fixed {n : ModGL Tag.E6 L} {b : Fin Tag.E6.rank → Lˣ}
    (hn : n = rootDiagUnit Tag.E6 b * canonicalY (L := L))
    {r : Fin 3} (hb3 : b 3 = frameOmega (L := L) ^ (r : ℕ))
    (hP : b 1 * b 2 * b 4 = 1)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ fixedA2E6) :
    (actualn' (L := L) n (2 * (r : ℤ)) : Module.End L (RootModule Tag.E6 L))
        (rootVec Tag.E6 L γ) = rootVec Tag.E6 L γ := by
  unfold actualn'
  rw [Units.val_mul, Module.End.mul_apply, n_rootVec_fixed hn hγ, map_smul,
    frameT_zpow_neg_two_mul r, frameT_pow_rootVec_fixed (r : ℕ) hγ, smul_smul,
    n1_scalar_eq_one hb3 hP γ hγ, one_smul]

theorem Vlong_eq_span_fixedA2E6 :
    Vlong L = Submodule.span L
      (rootVec Tag.E6 L '' {γ : Fin Tag.E6.rank → ℤ | γ ∈ fixedA2E6}) := by
  unfold Vlong
  rw [Finsupp.supported_eq_span_single]
  congr 1
  ext w
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    obtain ⟨α, hα, hmem, rfl⟩ := (longWeight_label_iff ℓ).mp hℓ
    exact ⟨α, hmem, rootVec_eq_single_of_isRoot hα⟩
  · rintro ⟨α, hmem, rfl⟩
    exact ⟨Sum.inr ⟨α, isRoot_of_mem_fixedA2E6 hmem⟩,
      (longWeight_label_iff _).mpr ⟨α, isRoot_of_mem_fixedA2E6 hmem, hmem, rfl⟩,
      (rootVec_eq_single_of_isRoot (isRoot_of_mem_fixedA2E6 hmem)).symm⟩

theorem exists_norm_adjusted_generator
    {E : Subgroup (ModGL Tag.E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup Tag.E6 L)
    (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4)
    (hWeyl : ∀ e (he : e ∈ E),
      weylQuotientHom Tag.E6 L ⟨e, hEM he⟩ ∈ Subgroup.zpowers cE6)
    {n : ModGL Tag.E6 L} (hnE : n ∈ E)
    (hnc : weylQuotientHom Tag.E6 L ⟨n, hEM hnE⟩ = cE6) :
    ∃ (k : ℤ) (h1 : actualn' (L := L) n k ∈ E),
      actualn' (L := L) n k ∈ VlongFixer L ∧
      weylQuotientHom Tag.E6 L ⟨actualn' (L := L) n k, hEM h1⟩ = cE6 := by
  obtain ⟨b, hb, hP, hQ⟩ := normRoute_PQ hEM hE hnE hnc
  obtain ⟨r, hr⟩ := exists_fin3_eq_frameOmega_zpow (b 3) hQ
  let k : ℤ := 2 * (r : ℤ)
  have hn_eq : n = rootDiagUnit Tag.E6 b * canonicalY (L := L) := by
    rw [← hb]
    group
  have hET := frame_actualE_torus_eq_frameD hEM hE hcard hWeyl hnE hnc
  have hT_E : frameT (L := L) ∈ E := by
    have hTframeD : frameT (L := L) ∈ frameD (L := L) := by
      rw [frameD_eq_sup_zpowers]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have : frameT ∈ E ⊓ torusGroup Tag.E6 L := by
      rw [hET]
      exact hTframeD
    exact this.1
  have h1 : actualn' (L := L) n k ∈ E := by
    unfold actualn'
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hT_E _) hnE
  have hfix : actualn' (L := L) n k ∈ VlongFixer L := by
    rw [mem_VlongFixer_iff]
    intro v hv
    rw [Vlong_eq_span_fixedA2E6] at hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨γ, hγ, rfl⟩
      exact n1_rootVec_fixed hn_eq hr hP hγ
    · simp
    · intro x y _ _ ihx ihy
      rw [map_add, ihx, ihy]
    · intro c x _ ihx
      rw [map_smul, ihx]
  have hT_weyl : weylQuotientHom Tag.E6 L
      ⟨frameT (L := L), torusGroup_le_monomialSubgroup (frameT_mem_torus (L := L))⟩ = 1 :=
    frameT_weylQuotientHom (L := L)
  have hsub : (⟨actualn' (L := L) n k, hEM h1⟩ : monomialSubgroup Tag.E6 L) =
      (⟨frameT (L := L), torusGroup_le_monomialSubgroup (frameT_mem_torus (L := L))⟩ :
        monomialSubgroup Tag.E6 L) ^ (-k) * ⟨n, hEM hnE⟩ := Subtype.ext rfl
  have hweyl : weylQuotientHom Tag.E6 L ⟨actualn' (L := L) n k, hEM h1⟩ = cE6 := by
    rw [hsub, map_mul, map_zpow, hT_weyl, hnc]
    simp
  exact ⟨k, h1, hfix, hweyl⟩

end CFSG.StandardType.TwE6E4bNormalizers

end
