module

import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTools
import CFSG.RankThree.PartTwo.KFacts.K72OutL3
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup conjAut
  mem_linearAutGroup_iff)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitarySU mem_unitarySU_iff commute_scalar)

namespace Proof166Res3

section Unitary

open Matrix

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem isInnerAut_psuConj_pow_three (A : KFacts.unitaryIsom3 h) :
    KFacts.IsInnerAut (KFacts.psuConj h A ^ 3) :=
  CFSG.RankThree.PartTwo.KFacts.cube_mem_range_conj_of_mem_psuConj_range ⟨A, rfl⟩

end Unitary

theorem isInnerAut_commutator_pow_three {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hiso : Sec4.IsoLThreePi X 2 n) (α β : MulAut X) :
    KFacts.IsInnerAut ((α * β * α⁻¹ * β⁻¹) ^ 3) := by
  rcases hiso with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  ·
    obtain ⟨φ⟩ := KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
    rw [← KFacts.isInnerAut_congr (e.trans φ), map_pow, map_mul, map_mul, map_mul, map_inv,
      map_inv]
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp
      (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup le_rfl
        (MulAut.congr (e.trans φ) α) (MulAut.congr (e.trans φ) β))
    rw [← hA]
    exact Sec4.isInnerAut_conjAut_pow_n A
  ·
    have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    have hq2 : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
    obtain ⟨ψ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
    rw [← KFacts.isInnerAut_congr (e.trans ψ.symm), map_pow, map_mul, map_mul, map_mul, map_inv,
      map_inv]
    obtain ⟨A, hA⟩ := KFacts.commutator_mem_psuConj_range hU hq2
      (MulAut.congr (e.trans ψ.symm) α) (MulAut.congr (e.trans ψ.symm) β)
    rw [← hA]
    exact isInnerAut_psuConj_pow_three A

theorem inv_apply_eq_of_apply_eq {X : Type} [Group X] {α : MulAut X} {d : X} (h : α d = d) :
    α⁻¹ d = d := by
  conv_lhs => rw [← h]
  exact MulAut.inv_apply_self X α d

end Proof166Res3

open Proof166Res3 in
theorem ks167OutComm :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → ¬ 3 ∣ n → Sec4.IsoLThreePi X 2 n →
      ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
        ∀ α β : MulAut X, (∀ d ∈ D, α d = d) → (∀ d ∈ D, β d = d) →
          Nat.Coprime 3 (orderOf (α * β * α⁻¹ * β⁻¹)) → α * β * α⁻¹ * β⁻¹ = 1 := by
  intro X _ _ n hn hn3 hiso D hD hD9 α β hα hβ hcop
  set γ := α * β * α⁻¹ * β⁻¹ with hγ
  have hγD : ∀ d ∈ D, γ d = d := by
    intro d hd
    rw [hγ, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply,
      inv_apply_eq_of_apply_eq (hβ d hd), inv_apply_eq_of_apply_eq (hα d hd), hβ d hd, hα d hd]
  have hγ3D : ∀ d ∈ D, (γ ^ 3) d = d := by
    intro d hd
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hγD d hd, hγD d hd,
      hγD d hd]
  obtain ⟨y, hy⟩ := isInnerAut_commutator_pow_three hn hiso α β
  have hyC : y ∈ Subgroup.centralizer (D : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 := hγ3D d hd
    rw [← hy, MulAut.conj_apply] at h1
    calc d * y = y * d * y⁻¹ * y := by rw [h1]
      _ = y * d := by group
  have h3 := kS169HessCent X n (by omega) hiso (ProofKSL3Two.not_two_pow_mod_nine hn3) D hD hD9
  obtain ⟨a, ha⟩ := h3 ⟨y, hyC⟩
  have hya : y ^ 3 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hγa : γ ^ 3 ^ (a + 1) = 1 := by
    rw [pow_succ', pow_mul, ← hy, ← map_pow, hya, map_one]
  have hdvd : orderOf γ ∣ 3 ^ (a + 1) := orderOf_dvd_of_pow_eq_one hγa
  have h1 : orderOf γ = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left (a + 1) hcop).symm hdvd
  exact orderOf_eq_one_iff.mp h1

end CFSG.RankThree.PartTwo.Sec16
