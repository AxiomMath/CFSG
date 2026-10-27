module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.SharpNearField
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.IntegralDomain

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert--Blackburn XI.2.6

The projective-linear endpoint is stated with the affine coordinate model and
normalized inversion obtained in the proof of XI.2.6.  These hypotheses are
essential: a bare Bruhat-cardinality cover admits trivial counterexamples.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u

open scoped Pointwise

public theorem xi26_exists_square_add_one_nonsquare
    {K : Type*} [Field K] [Finite K] [DecidableEq K]
    (hchar : ringChar K ≠ 2) :
    ∃ b : K, IsSquare b ∧ ¬ IsSquare (b + 1) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  by_contra hex
  push Not at hex
  have hadd {x y : K} (hx : IsSquare x) (hy : IsSquare y) :
      IsSquare (x + y) := by
    by_cases hy0 : y = 0
    · simpa [hy0] using hx
    have hxy : IsSquare (x / y) := by simpa [div_eq_mul_inv] using hx.mul hy.inv
    have hxy1 : IsSquare (x / y + 1) := hex _ hxy
    have hprod : IsSquare ((x / y + 1) * y) := hxy1.mul hy
    convert hprod using 1 <;> field_simp
  have hneg {x : K} (hx : IsSquare x) : IsSquare (-x) := by
    have hnsmul : ∀ n : ℕ, IsSquare (n • x) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [succ_nsmul]
          exact hadd ih hx
    have hcard : Nat.card K ≠ 0 := (Nat.card_pos (α := K)).ne'
    have heq : (Nat.card K - 1) • x = -x := by
      apply eq_neg_of_add_eq_zero_right
      rw [sub_one_nsmul_add hcard]
      exact card_nsmul_eq_zero'
    rw [← heq]
    exact hnsmul _
  let S : AddSubgroup K :=
    { carrier := {x | IsSquare x}
      zero_mem' := IsSquare.zero
      add_mem' := fun hx hy => hadd hx hy
      neg_mem' := fun hx => hneg hx }
  let R : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range
  let toNonzeroSquare : R → {x : S // x ≠ 0} := fun r =>
    ⟨⟨((r : Kˣ) : K), by
      rcases r.property with ⟨u, hu⟩
      rw [← hu]
      exact IsSquare.sq (u : K)⟩,
      by
        intro h
        exact Units.ne_zero (r : Kˣ) (congrArg Subtype.val h)⟩
  have hto_inj : Function.Injective toNonzeroSquare := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun z : {x : S // x ≠ 0} => ((z.1 : S) : K)) hxy
  have hto_surj : Function.Surjective toNonzeroSquare := by
    intro x
    rcases x.1.property with ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro ha0
      apply x.2
      simpa [ha0] using ha
    let u : Kˣ := Units.mk0 a ha0
    have hx0 : (x.1 : K) ≠ 0 := by
      intro h
      apply x.2
      exact Subtype.ext h
    let r : R := ⟨Units.mk0 (x.1 : K) hx0, ⟨u, by
      apply Units.ext
      simpa [u, pow_two] using ha.symm⟩⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let eNonzero : R ≃ {x : S // x ≠ 0} :=
    Equiv.ofBijective toNonzeroSquare ⟨hto_inj, hto_surj⟩
  let eOption : Option R ≃ S :=
    ((Equiv.optionSubtype (0 : S)).symm eNonzero).1
  have hScard : Nat.card S = Nat.card R + 1 := by
    rw [← Nat.card_congr eOption]
    simp
  have hKodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hchar)
  have hUeven : Even (Nat.card Kˣ) := by
    rw [Nat.card_units]
    exact Nat.Odd.sub_odd hKodd odd_one
  have hRcard : Nat.card R = Nat.card Kˣ / 2 := by
    calc
      Nat.card R = Nat.card Kˣ / (Nat.card Kˣ).gcd 2 := by
        simpa [R] using IsCyclic.card_powMonoidHom_range Kˣ 2
      _ = Nat.card Kˣ / 2 := by
        rw [Nat.gcd_eq_right (even_iff_two_dvd.mp hUeven)]
  have hRtwo : 2 * Nat.card R = Nat.card Kˣ := by
    rw [hRcard]
    exact Nat.mul_div_cancel' (even_iff_two_dvd.mp hUeven)
  have hStwo : 2 * Nat.card S = Nat.card K + 1 := by
    have hKpos : 0 < Nat.card K := Nat.card_pos
    rw [Nat.card_units] at hRtwo
    omega
  have hSdK : Nat.card S ∣ Nat.card K := by
    use S.index
    rw [mul_comm]
    exact S.index_mul_card.symm
  have hSdK1 : Nat.card S ∣ Nat.card K + 1 := by
    use 2
    simpa [mul_comm] using hStwo.symm
  have hSone : Nat.card S = 1 := by
    apply Nat.dvd_one.mp
    have : Nat.card S ∣ Nat.gcd (Nat.card K) (Nat.card K + 1) :=
      Nat.dvd_gcd hSdK hSdK1
    simpa using this
  have hsub : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hSone).1
  let oneS : S := ⟨1, IsSquare.one⟩
  have h01 : (0 : S) = oneS := hsub.elim _ _
  have hk : (0 : K) = 1 := by
    simpa [oneS] using congrArg Subtype.val h01
  exact zero_ne_one hk

private theorem xi26_tau_inverse
    {K : Type*} [Field K] [Finite K] [DecidableEq K]
    (hchar : ringChar K ≠ 2)
    (H A : Subgroup (Equiv.Perm (Option K)))
    (tau : Equiv.Perm (Option K))
    (affinePerm : K → Kˣ → Equiv.Perm (Option K))
    (hAffinePerm : ∀ b : K, ∀ a : Kˣ, ∀ y : Option K,
      affinePerm b a y = Option.map (fun x => b + x * (a : K)) y)
    (hA : (A : Set (Equiv.Perm (Option K))) =
      {sigma | ∃ b : K, ∃ a : Kˣ, sigma = affinePerm b a})
    (hA_le : A ≤ H) (hTau_mem : tau ∈ H)
    (hA_fix_infty : ∀ sigma : H,
      ((sigma : Equiv.Perm (Option K)) ∈ A ↔
        (sigma : Equiv.Perm (Option K)) none = none))
    (hTauInf : tau none = some 0)
    (hTauZero : tau (some 0) = none)
    (hTauSq : ∀ y : Option K, tau (tau y) = y)
    (theta : Kˣ ≃* Kˣ)
    (hThetaApply : ∀ x : Kˣ,
      tau (some (x : K)) = some ((theta x : Kˣ) : K))
    (hThetaSquare : ∀ x : Kˣ, theta (x ^ 2) = (x ^ 2)⁻¹) :
    ∀ y : Option K,
      tau y = match y with
        | none => some 0
        | some x => if x = 0 then none else some x⁻¹ := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let negOne : Kˣ := Units.mk0 (-1 : K) (by
    exact neg_ne_zero.mpr one_ne_zero)
  have hThetaNegOne : theta negOne = negOne := by
    have hpow : theta negOne ^ 2 = 1 := by
      calc
        theta negOne ^ 2 = theta (negOne ^ 2) := (map_pow theta negOne 2).symm
        _ = theta 1 := by
          congr 1
          apply Units.ext
          simp [negOne]
        _ = 1 := map_one theta
    have hvalpow : (((theta negOne : Kˣ) : K) ^ 2) = 1 := by
      simpa using congrArg (fun u : Kˣ => (u : K)) hpow
    rcases sq_eq_one_iff.mp hvalpow with hval | hval
    · exfalso
      have hthetaOne : theta negOne = 1 := Units.ext hval
      have hnegOneOne : negOne = 1 := theta.injective (by simpa using hthetaOne)
      apply hchar
      apply neg_one_eq_one_iff.mp
      simpa [negOne] using congrArg (fun u : Kˣ => (u : K)) hnegOneOne
    · exact Units.ext hval
  have hThetaNeg (x : Kˣ) :
      theta (Units.mk0 (-(x : K)) (neg_ne_zero.mpr (Units.ne_zero x))) =
        Units.mk0 (-((theta x : Kˣ) : K))
          (neg_ne_zero.mpr (Units.ne_zero (theta x))) := by
    have hunit :
        Units.mk0 (-(x : K)) (neg_ne_zero.mpr (Units.ne_zero x)) = negOne * x := by
      apply Units.ext
      simpa [negOne]
    rw [hunit, map_mul, hThetaNegOne]
    apply Units.ext
    simpa [negOne]
  have hThetaInvolutive : Function.Involutive theta := by
    intro x
    apply Units.ext
    exact Option.some.inj (by
      rw [← hThetaApply, ← hThetaApply]
      exact hTauSq (some (x : K)))
  let T (b : K) : Equiv.Perm (Option K) := affinePerm b 1
  have hT_apply (b : K) (y : Option K) :
      T b y = Option.map (fun x => b + x) y := by
    rw [show T b = affinePerm b 1 by rfl, hAffinePerm]
    simp
  have hT_mem_A (b : K) : T b ∈ A := by
    have : T b ∈ {sigma : Equiv.Perm (Option K) |
        ∃ c : K, ∃ a : Kˣ, sigma = affinePerm c a} :=
      ⟨b, 1, rfl⟩
    rwa [← hA] at this
  have hT_mem_H (b : K) : T b ∈ H := hA_le (hT_mem_A b)
  have hTau_mul_self : tau * tau = 1 := by
    apply Equiv.ext
    exact hTauSq
  have hTau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right hTau_mul_self
  have hT_inv (b : K) : (T b)⁻¹ = T (-b) := by
    apply Equiv.ext
    intro y
    apply (T b).injective
    calc
      (T b) ((T b)⁻¹ y) = y := Equiv.apply_symm_apply (T b) y
      _ = (T b) (T (-b) y) := by
        simp [hT_apply, T]
  have hT_cancel_left (b : K) : T (-b) * T b = 1 := by
    rw [← hT_inv]
    simp
  have hT_cancel_right (b : K) : T b * T (-b) = 1 := by
    rw [← hT_inv]
    simp
  have hEquationOne (a : Kˣ) :
      ∃ c : Kˣ, ∀ x : Option K,
        tau (T (a : K) (tau x)) =
          T ((theta a : Kˣ) : K)
            (tau (T (-(a : K)) (affinePerm 0 c x))) := by
    let ha : Equiv.Perm (Option K) :=
      T (a : K) * tau * T (-((theta a : Kˣ) : K)) * tau *
        T (a : K) * tau
    have hha_mem : ha ∈ H := by
      exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
        (H.mul_mem (hT_mem_H _) hTau_mem) (hT_mem_H _)) hTau_mem)
          (hT_mem_H _)) hTau_mem
    have hhaInf : ha none = none := by
      change T (a : K)
        (tau (T (-((theta a : Kˣ) : K))
          (tau (T (a : K) (tau none))))) = none
      rw [hTauInf]
      simp only [hT_apply, Option.map_some, add_zero]
      rw [hThetaApply]
      simp only [hT_apply, Option.map_some]
      simp only [Option.map_some, neg_add_cancel]
      rw [hTauZero]
      rfl
    have hhaZero : ha (some 0) = some 0 := by
      change T (a : K)
        (tau (T (-((theta a : Kˣ) : K))
          (tau (T (a : K) (tau (some 0)))))) = some 0
      rw [hTauZero]
      simp only [hT_apply, Option.map_none]
      rw [hTauInf]
      simp only [hT_apply, Option.map_some, add_zero]
      have hnegApply := hThetaApply
        (Units.mk0 (-((theta a : Kˣ) : K))
          (neg_ne_zero.mpr (Units.ne_zero (theta a))))
      rw [hThetaNeg, hThetaInvolutive] at hnegApply
      have hnegApply' :
          tau (some (-((theta a : Kˣ) : K))) = some (-(a : K)) := by
        simpa using hnegApply
      rw [hnegApply']
      simp [hT_apply]
    have hhaA : ha ∈ A :=
      (hA_fix_infty ⟨ha, hha_mem⟩).mpr hhaInf
    have hhaA' : ha ∈ (A : Set (Equiv.Perm (Option K))) := hhaA
    rw [hA] at hhaA'
    rcases hhaA' with ⟨b, c, hha⟩
    have hb : b = 0 := by
      have heval := congrArg (fun q : Equiv.Perm (Option K) => q (some 0)) hha
      change ha (some 0) = affinePerm b c (some 0) at heval
      rw [hhaZero, hAffinePerm] at heval
      simpa using Option.some.inj heval.symm
    subst b
    refine ⟨c, ?_⟩
    intro x
    have hperm : tau * T (a : K) * tau =
        T ((theta a : Kˣ) : K) * tau * T (-(a : K)) * ha := by
      symm
      calc
        T ((theta a : Kˣ) : K) * tau * T (-(a : K)) * ha =
            T ((theta a : Kˣ) : K) * tau *
              (T (-(a : K)) * T (a : K)) * tau *
                T (-((theta a : Kˣ) : K)) * tau * T (a : K) * tau := by
          dsimp [ha]
          group
        _ = T ((theta a : Kˣ) : K) * (tau * tau) *
              T (-((theta a : Kˣ) : K)) * tau * T (a : K) * tau := by
          rw [hT_cancel_left]
          simp
          group
        _ = (T ((theta a : Kˣ) : K) *
              T (-((theta a : Kˣ) : K))) * tau * T (a : K) * tau := by
          rw [hTau_mul_self]
          simp
        _ = tau * T (a : K) * tau := by
          rw [hT_cancel_right]
          simp
    have happ := congrArg (fun q : Equiv.Perm (Option K) => q x) hperm
    simp only [Equiv.Perm.mul_apply] at happ
    rw [hha, hAffinePerm] at happ
    simpa [hT_apply] using happ
  have hSquareEquation (r : Kˣ) :
      let a : Kˣ := r ^ 2
      ∃ c : Kˣ, (c : K) = -((a : K) ^ 2) ∧
        ∀ x : Option K,
          tau (T (a : K) (tau x)) =
            T ((theta a : Kˣ) : K)
              (tau (T (-(a : K)) (affinePerm 0 c x))) := by
    dsimp
    let a : Kˣ := r ^ 2
    rcases hEquationOne a with ⟨c, hc⟩
    let z : Kˣ := a * c⁻¹
    have hcz := hc (some (z : K))
    have hleft0 : tau (T (a : K) (tau (some (z : K)))) = none := by
      have haff : affinePerm 0 c (some (z : K)) =
          some ((z : K) * (c : K)) := by
        rw [hAffinePerm]
        simp
      rw [hcz, haff]
      have hzc : (z : K) * (c : K) = (a : K) := by
        simpa using congrArg (fun u : Kˣ => (u : K))
          (show z * c = a by simp [z])
      rw [hzc]
      simp only [hT_apply, Option.map_some, neg_add_cancel]
      rw [hTauZero]
      simp [hT_apply]
    have hinner : T (a : K) (tau (some (z : K))) = some 0 := by
      apply tau.injective
      rw [hleft0, hTauZero]
    rw [hThetaApply, hT_apply] at hinner
    have hthetaZval : ((theta z : Kˣ) : K) = -(a : K) :=
      eq_neg_of_add_eq_zero_right (Option.some.inj hinner)
    let negA : Kˣ := Units.mk0 (-(a : K))
      (neg_ne_zero.mpr (Units.ne_zero a))
    have hthetaZ : theta z = negA := Units.ext hthetaZval
    have hzneg : z = negOne * theta a := by
      calc
        z = theta (theta z) := (hThetaInvolutive z).symm
        _ = theta negA := by rw [hthetaZ]
        _ = Units.mk0 (-((theta a : Kˣ) : K))
              (neg_ne_zero.mpr (Units.ne_zero (theta a))) := by
          simpa [negA] using hThetaNeg a
        _ = negOne * theta a := by
          apply Units.ext
          simp [negOne]
    have hnegInv : negOne⁻¹ = negOne := by
      apply Units.ext
      simp [negOne]
    have hcunit : c = negOne * a ^ 2 := by
      calc
        c = z⁻¹ * a := by
          dsimp [z]
          group
        _ = (negOne * theta a)⁻¹ * a := by rw [hzneg]
        _ = negOne * a ^ 2 := by
          have hthetaA : theta a = a⁻¹ := by
            simpa [a] using hThetaSquare r
          rw [hthetaA, mul_inv_rev, inv_inv, hnegInv, pow_two]
          ac_rfl
    have hcval : (c : K) = -((a : K) ^ 2) := by
      simpa [negOne] using congrArg (fun u : Kˣ => (u : K)) hcunit
    exact ⟨c, hcval, hc⟩
  obtain ⟨b, hbSquare, hb1Nonsquare⟩ :=
    xi26_exists_square_add_one_nonsquare hchar
  have hb1zero : b + 1 ≠ 0 := by
    intro h
    apply hb1Nonsquare
    rw [h]
    exact IsSquare.zero
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hb1Nonsquare
    simp [hb0]
  rcases hbSquare with ⟨r0, hr0⟩
  have hr00 : r0 ≠ 0 := by
    intro hr
    apply hb0
    simpa [hr] using hr0
  let r : Kˣ := Units.mk0 r0 hr00
  have hrSq : ((r ^ 2 : Kˣ) : K) = b := by
    simpa [r, pow_two] using hr0.symm
  have hbInv : tau (some b) = some b⁻¹ := by
    rw [← hrSq, hThetaApply, hThetaSquare]
    simp
  have hTauOne : tau (some (1 : K)) = some 1 := by
    simpa using hThetaApply (1 : Kˣ)
  have hb1Inv : tau (some (b + 1)) = some (b + 1)⁻¹ := by
    rcases hSquareEquation r with ⟨c, hcval, heq⟩
    have he := heq (some (1 : K))
    simp only [hTauOne, hT_apply, hAffinePerm, Option.map_some,
      zero_add, one_mul] at he
    let aU : Kˣ := r ^ 2
    let dU : Kˣ := Units.mk0 (b + 1) hb1zero
    let qU : Kˣ := negOne * aU * dU
    have haUval : (aU : K) = b := by simpa [aU] using hrSq
    have hcval' : (c : K) = -((aU : K) ^ 2) := by simpa [aU] using hcval
    have harg : -(aU : K) + (c : K) = (qU : K) := by
      rw [hcval']
      simp only [qU, negOne, dU, Units.val_mul, Units.val_mk0]
      rw [haUval]
      ring
    have hright : Option.map (fun x => ((theta aU : Kˣ) : K) + x)
          (tau (some (-(aU : K) + (c : K)))) =
        some (((theta aU : Kˣ) : K) + ((theta qU : Kˣ) : K)) := by
      rw [harg, hThetaApply]
      rfl
    have he' : tau (some (b + 1)) =
        some (((theta aU : Kˣ) : K) + ((theta qU : Kˣ) : K)) := by
      calc
        tau (some (b + 1)) = tau (some ((aU : K) + 1)) := by rw [hrSq]
        _ = Option.map (fun x => ((theta aU : Kˣ) : K) + x)
              (tau (some (-(aU : K) + (c : K)))) := by
          simpa [aU] using he
        _ = _ := hright
    have hthetaD : ((theta dU : Kˣ) : K) =
        ((theta aU : Kˣ) : K) + ((theta qU : Kˣ) : K) := by
      exact Option.some.inj ((hThetaApply dU).symm.trans he')
    have hthetaA : theta aU = aU⁻¹ := by
      simpa [aU] using hThetaSquare r
    have hthetaQ : theta qU = negOne * aU⁻¹ * theta dU := by
      simp only [qU, map_mul, hThetaNegOne, hthetaA]
    have hthetaD' : ((theta dU : Kˣ) : K) =
        (aU : K)⁻¹ - (aU : K)⁻¹ * ((theta dU : Kˣ) : K) := by
      calc
        ((theta dU : Kˣ) : K) =
            ((theta aU : Kˣ) : K) + ((theta qU : Kˣ) : K) := hthetaD
        _ = (aU : K)⁻¹ - (aU : K)⁻¹ * ((theta dU : Kˣ) : K) := by
          rw [hthetaA, hthetaQ]
          simp [negOne, sub_eq_add_neg]
    have haU0 : (aU : K) ≠ 0 := Units.ne_zero aU
    have hmulA : (aU : K) * ((theta dU : Kˣ) : K) =
        1 - ((theta dU : Kˣ) : K) := by
      calc
        (aU : K) * ((theta dU : Kˣ) : K) =
            (aU : K) * ((aU : K)⁻¹ -
              (aU : K)⁻¹ * ((theta dU : Kˣ) : K)) :=
          congrArg (fun v : K => (aU : K) * v) hthetaD'
        _ = 1 - ((theta dU : Kˣ) : K) := by
          field_simp
    have hmulD : (b + 1) * ((theta dU : Kˣ) : K) = 1 := by
      rw [← hrSq]
      linear_combination hmulA
    have hthetaDInv : ((theta dU : Kˣ) : K) = (b + 1)⁻¹ :=
      eq_inv_of_mul_eq_one_right hmulD
    change tau (some ((dU : Kˣ) : K)) = some (b + 1)⁻¹
    rw [hThetaApply]
    exact congrArg some hthetaDInv
  intro y
  cases y with
  | none => exact hTauInf
  | some x =>
      by_cases hx0 : x = 0
      · simp [hx0, hTauZero]
      by_cases hxsq : IsSquare x
      · rcases hxsq with ⟨z, hz⟩
        have hz0 : z ≠ 0 := by
          intro hz0
          apply hx0
          simpa [hz0] using hz
        let u : Kˣ := Units.mk0 z hz0
        have hux : ((u ^ 2 : Kˣ) : K) = x := by
          simpa [u, pow_two] using hz.symm
        rw [← hux, hThetaApply, hThetaSquare]
        simp
      · have hxratio : IsSquare (x / (b + 1)) := by
          apply (quadraticChar_one_iff_isSquare (div_ne_zero hx0 hb1zero)).mp
          have hmulChar := congrArg (quadraticChar K)
            (div_mul_cancel₀ x hb1zero)
          rw [map_mul,
            quadraticChar_neg_one_iff_not_isSquare.mpr hxsq,
            quadraticChar_neg_one_iff_not_isSquare.mpr hb1Nonsquare] at hmulChar
          norm_num at hmulChar
          exact hmulChar
        rcases hxratio with ⟨z, hz⟩
        have hz0 : z ≠ 0 := by
          intro hz0
          have : x / (b + 1) = 0 := by simpa [hz0] using hz
          exact hx0 (div_eq_zero_iff.mp this |>.resolve_right hb1zero)
        let u : Kˣ := Units.mk0 z hz0
        let bx : Kˣ := Units.mk0 (b + 1) hb1zero
        have hxunit : Units.mk0 x hx0 = bx * u ^ 2 := by
          apply Units.ext
          change x = (b + 1) * z ^ 2
          calc
            x = (x / (b + 1)) * (b + 1) := (div_mul_cancel₀ x hb1zero).symm
            _ = (b + 1) * z ^ 2 := by rw [hz, pow_two]; ac_rfl
        simp only [if_neg hx0]
        change tau (some ((Units.mk0 x hx0 : Kˣ) : K)) = some x⁻¹
        have hbtheta : theta bx = bx⁻¹ := by
          apply Units.ext
          have hb1Inv' : tau (some ((bx : Kˣ) : K)) =
              some ((bx⁻¹ : Kˣ) : K) := by
            simpa [bx] using hb1Inv
          exact Option.some.inj ((hThetaApply bx).symm.trans hb1Inv')
        have hthetaX : theta (Units.mk0 x hx0) = (Units.mk0 x hx0)⁻¹ := by
          rw [hxunit, map_mul, hThetaSquare, hbtheta]
          rw [← mul_inv_rev, mul_comm (u ^ 2) bx, ← hxunit]
        rw [hThetaApply, hthetaX]
        rfl

private theorem xi26_gl2_scalar_smul_onePoint
    (K : Type*) [Field K] [DecidableEq K]
    (a : Kˣ) (x : OnePoint K) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a • x = x := by
  cases x with
  | infty =>
      rw [OnePoint.smul_infty_eq_self_iff]
      simp
  | coe x =>
      rw [OnePoint.smul_some_eq_ite]
      simp [Units.ne_zero]

private theorem xi26_gl2_mem_center_of_onePoint_trivial
    (K : Type*) [Field K] [DecidableEq K]
    (g : GL (Fin 2) K) (hfix : ∀ x : OnePoint K, g • x = x) :
    g ∈ Subgroup.center (GL (Fin 2) K) := by
  have h10 : g 1 0 = 0 :=
    OnePoint.smul_infty_eq_self_iff.mp (hfix (OnePoint.infty : OnePoint K))
  have hzero := hfix (↑(0 : K) : OnePoint K)
  rw [OnePoint.smul_some_eq_ite] at hzero
  have h11 : g 1 1 ≠ 0 := by
    intro h
    simp [h10, h] at hzero
  have h01 : g 0 1 = 0 := by
    simp [h10, h11] at hzero
    exact hzero
  have hone := hfix (↑(1 : K) : OnePoint K)
  rw [OnePoint.smul_some_eq_ite] at hone
  have hdiag : g 0 0 = g 1 1 := by
    simp [h10, h01, h11] at hone
    exact (div_eq_one_iff_eq h11).mp hone
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  refine ⟨g 0 0, ?_⟩
  symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, h10, h01, hdiag]

private theorem xi26_gl2_onePointPermHom_ker
    (K : Type*) [Field K] [DecidableEq K] :
    (MulAction.toPermHom (GL (Fin 2) K) (OnePoint K)).ker =
      Subgroup.center (GL (Fin 2) K) := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    apply xi26_gl2_mem_center_of_onePoint_trivial K g
    intro x
    simpa using DFunLike.congr_fun hg x
  · intro hg
    rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hg with
      ⟨a, ha⟩
    rw [Equiv.Perm.ext_iff]
    intro x
    have ha0 : a ≠ 0 := by
      intro ha0
      have hgzero : (g : Matrix (Fin 2) (Fin 2) K) = 0 := by
        rw [← ha]
        simp [ha0]
      exact Units.ne_zero g hgzero
    let aUnit : Kˣ := Units.mk0 a ha0
    have hu : Matrix.GeneralLinearGroup.scalar (Fin 2) aUnit = g := by
      apply Units.ext
      change Matrix.scalar (Fin 2) (aUnit : K) =
        (g : Matrix (Fin 2) (Fin 2) K)
      simpa [aUnit] using ha
    rw [← hu]
    exact xi26_gl2_scalar_smul_onePoint K aUnit x

private noncomputable def xi26_pgl2_onePointPermHom
    (K : Type*) [Field K] [DecidableEq K] :
    Matrix.ProjGenLinGroup (Fin 2) K →* Equiv.Perm (OnePoint K) :=
  Matrix.ProjGenLinGroup.lift
    (MulAction.toPermHom (GL (Fin 2) K) (OnePoint K)) (by
      ext a x
      exact xi26_gl2_scalar_smul_onePoint K a x)

private theorem xi26_pgl2_onePointPermHom_injective
    (K : Type*) [Field K] [DecidableEq K] :
    Function.Injective (xi26_pgl2_onePointPermHom K) := by
  intro q1 q2 hq
  obtain ⟨g1, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective q1
  obtain ⟨g2, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective q2
  have hperm :
      MulAction.toPermHom (GL (Fin 2) K) (OnePoint K) g1 =
        MulAction.toPermHom (GL (Fin 2) K) (OnePoint K) g2 := by
    simpa [xi26_pgl2_onePointPermHom] using hq
  apply (inv_mul_eq_one).mp
  rw [← map_inv, ← map_mul, ← MonoidHom.mem_ker,
    Matrix.ProjGenLinGroup.ker_mk, ← xi26_gl2_onePointPermHom_ker,
    MonoidHom.mem_ker]
  change MulAction.toPermHom (GL (Fin 2) K) (OnePoint K) (g1⁻¹ * g2) = 1
  rw [map_mul, map_inv, hperm]
  simp

private theorem xi26_card_pgl2
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let GL2 := GL (Fin 2) K
  let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
  let centerGL := Subgroup.center GL2
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL2 =>
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card centerGL = Nat.card K - 1 := by
    dsimp [centerGL, GL2]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card (Matrix.GeneralLinearGroup.scalar (Fin 2)).range = Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalar_inj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := K))
  have hGL : Nat.card GL2 =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
    simpa [GL2, Fin.prod_univ_two] using (Matrix.card_GL_field (𝔽 := K) 2)
  let mkPGL : GL2 →* PGL2 := Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : centerGL.index = Nat.card PGL2 := by
    calc
      centerGL.index = mkPGL.ker.index := by rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card PGL2 := by rw [hrange]; simp
  have hmul := centerGL.index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  have hdiff : Nat.card K ^ 2 - Nat.card K =
      Nat.card K * (Nat.card K - 1) := by
    rw [pow_two]
    calc
      Nat.card K * Nat.card K - Nat.card K =
          Nat.card K * Nat.card K - Nat.card K * 1 := by simp
      _ = Nat.card K * (Nat.card K - 1) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdiff] at hmul
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
  calc
    (Nat.card K - 1) * Nat.card PGL2 =
        Nat.card PGL2 * (Nat.card K - 1) := by ac_rfl
    _ = (Nat.card K ^ 2 - 1) * (Nat.card K * (Nat.card K - 1)) := hmul
    _ = (Nat.card K - 1) * (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring

/-- The final projective-linear recognition endpoint in XI.2.6.  The affine
point stabilizer and the normalized inversion generate the standard faithful
`PGL₂` image; the sharp-action order equality makes that containment an
equality. -/
public theorem xi26_pglRange_of_tau
    {G K : Type u} [Group G] [Field K] [Finite K] [DecidableEq K]
    (rho : G →* Equiv.Perm (Option K))
    (A : Subgroup (Equiv.Perm (Option K)))
    (tau : Equiv.Perm (Option K))
    (affinePerm : K → Kˣ → Equiv.Perm (Option K))
    (hAffinePerm : ∀ b : K, ∀ a : Kˣ, ∀ y : Option K,
      affinePerm b a y = Option.map (fun x => b + x * (a : K)) y)
    (hA : (A : Set (Equiv.Perm (Option K))) =
      {sigma | ∃ b : K, ∃ a : Kˣ, sigma = affinePerm b a})
    (hTau : ∀ y : Option K,
      tau y = match y with
        | none => some 0
        | some x => if x = 0 then none else some x⁻¹)
    (hRange :
      (rho.range : Set (Equiv.Perm (Option K))) =
        (A : Set (Equiv.Perm (Option K))) ∪
          DoubleCoset.doubleCoset tau
            (A : Set (Equiv.Perm (Option K)))
            (A : Set (Equiv.Perm (Option K))))
    (hRangeCard : Nat.card rho.range = Nat.card K * (Nat.card K ^ 2 - 1)) :
    Nonempty (rho.range ≃* Matrix.ProjGenLinGroup (Fin 2) K) := by
  classical
  let pglPerm := xi26_pgl2_onePointPermHom K
  let J : Subgroup (Equiv.Perm (Option K)) := pglPerm.range
  have hA_le_J : A ≤ J := by
    intro sigma hsigma
    have hsigmaSet : sigma ∈ (A : Set (Equiv.Perm (Option K))) := hsigma
    rw [hA] at hsigmaSet
    rcases hsigmaSet with ⟨b, a, rfl⟩
    have ha0 : (a : K) ≠ 0 := Units.ne_zero a
    let M : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : K), b; 0, 1] (by
        simpa [Matrix.det_fin_two] using ha0)
    refine ⟨Matrix.ProjGenLinGroup.mk M, ?_⟩
    apply Equiv.ext
    intro y
    cases y with
    | infty =>
        change _ = affinePerm b a none
        rw [hAffinePerm b a none]
        simp only [pglPerm, xi26_pgl2_onePointPermHom,
          Matrix.ProjGenLinGroup.lift_mk]
        change M • (OnePoint.infty : OnePoint K) = OnePoint.infty
        rw [OnePoint.smul_infty_eq_self_iff]
        simp [M]
    | coe x =>
        change _ = affinePerm b a (some x)
        rw [hAffinePerm b a (some x)]
        simp only [pglPerm, xi26_pgl2_onePointPermHom,
          Matrix.ProjGenLinGroup.lift_mk]
        change M • (x : OnePoint K) =
          (b + x * (a : K) : K)
        rw [OnePoint.smul_some_eq_ite]
        simp [M, add_comm, mul_comm]
  have hTau_mem_J : tau ∈ J := by
    let W : GL (Fin 2) K := {
      val := !![0, 1; 1, 0]
      inv := !![0, 1; 1, 0]
      val_inv := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two]
      inv_val := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] }
    refine ⟨Matrix.ProjGenLinGroup.mk W, ?_⟩
    apply Equiv.ext
    intro y
    cases y with
    | infty =>
        change _ = tau none
        rw [hTau none]
        simp only [pglPerm, xi26_pgl2_onePointPermHom,
          Matrix.ProjGenLinGroup.lift_mk]
        change W • (OnePoint.infty : OnePoint K) = (0 : K)
        rw [OnePoint.smul_infty_eq_ite]
        simp [W]
    | coe x =>
        change _ = tau (some x)
        rw [hTau (some x)]
        simp only [pglPerm, xi26_pgl2_onePointPermHom,
          Matrix.ProjGenLinGroup.lift_mk]
        change W • (x : OnePoint K) =
          if x = 0 then OnePoint.infty else (x⁻¹ : K)
        rw [OnePoint.smul_some_eq_ite]
        by_cases hx : x = 0 <;> simp [W, hx, div_eq_inv_mul]
  have hRange_le_J : rho.range ≤ J := by
    intro sigma hsigma
    have hsigma' : sigma ∈
        (A : Set (Equiv.Perm (Option K))) ∪
          DoubleCoset.doubleCoset tau
            (A : Set (Equiv.Perm (Option K)))
            (A : Set (Equiv.Perm (Option K))) := by
      rw [← hRange]
      exact hsigma
    rcases hsigma' with hsigmaA | hsigmaD
    · exact hA_le_J hsigmaA
    · rcases DoubleCoset.mem_doubleCoset.mp hsigmaD with
        ⟨a1, ha1, a2, ha2, rfl⟩
      exact J.mul_mem (J.mul_mem (hA_le_J ha1) hTau_mem_J) (hA_le_J ha2)
  have hJcard : Nat.card J =
      Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) :=
    (Nat.card_congr
      (Equiv.ofInjective pglPerm (xi26_pgl2_onePointPermHom_injective K))).symm
  have hRangeEq : rho.range = J := by
    apply Subgroup.eq_of_le_of_card_ge hRange_le_J
    rw [hJcard, xi26_card_pgl2, hRangeCard]
  let pglToJ : Matrix.ProjGenLinGroup (Fin 2) K →* J :=
    pglPerm.codRestrict J (fun x => ⟨x, rfl⟩)
  have hpglToJ : Function.Bijective pglToJ := by
    constructor
    · intro x y hxy
      apply xi26_pgl2_onePointPermHom_injective K
      exact congrArg Subtype.val hxy
    · intro y
      rcases y.property with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
  let ePGLJ : Matrix.ProjGenLinGroup (Fin 2) K ≃* J :=
    MulEquiv.ofBijective pglToJ hpglToJ
  exact ⟨(MulEquiv.subgroupCongr hRangeEq).trans ePGLJ.symm⟩


/-- Huppert--Blackburn XI.2.6, in the field branch.  The involution on the
projective line is first identified with inversion from its action on square
multipliers and the affine point stabilizer; the resulting standard image is
then recognized as `PGL₂`. -/
public theorem huppert_XI_2_6_pglRange
    {G K : Type u} [Group G] [Field K] [Finite K] [DecidableEq K]
    (hchar : ringChar K ≠ 2)
    (rho : G →* Equiv.Perm (Option K))
    (A : Subgroup (Equiv.Perm (Option K)))
    (tau : Equiv.Perm (Option K))
    (affinePerm : K → Kˣ → Equiv.Perm (Option K))
    (hAffinePerm : ∀ b : K, ∀ a : Kˣ, ∀ y : Option K,
      affinePerm b a y = Option.map (fun x => b + x * (a : K)) y)
    (hA : (A : Set (Equiv.Perm (Option K))) =
      {sigma | ∃ b : K, ∃ a : Kˣ, sigma = affinePerm b a})
    (hA_fix_infty : ∀ sigma : rho.range,
      ((sigma : Equiv.Perm (Option K)) ∈ A ↔
        (sigma : Equiv.Perm (Option K)) none = none))
    (hTauInf : tau none = some 0)
    (hTauZero : tau (some 0) = none)
    (hTauSq : ∀ y : Option K, tau (tau y) = y)
    (theta : Kˣ ≃* Kˣ)
    (hThetaApply : ∀ x : Kˣ,
      tau (some (x : K)) = some ((theta x : Kˣ) : K))
    (hThetaSquare : ∀ x : Kˣ, theta (x ^ 2) = (x ^ 2)⁻¹)
    (hRange :
      (rho.range : Set (Equiv.Perm (Option K))) =
        (A : Set (Equiv.Perm (Option K))) ∪
          DoubleCoset.doubleCoset tau
            (A : Set (Equiv.Perm (Option K)))
            (A : Set (Equiv.Perm (Option K))))
    (hRangeCard : Nat.card rho.range = Nat.card K * (Nat.card K ^ 2 - 1)) :
    Nonempty (rho.range ≃* Matrix.ProjGenLinGroup (Fin 2) K) := by
  classical
  have hA_le_range : A ≤ rho.range := by
    intro sigma hsigma
    have hsigma' : sigma ∈
        (A : Set (Equiv.Perm (Option K))) ∪
          DoubleCoset.doubleCoset tau
            (A : Set (Equiv.Perm (Option K)))
            (A : Set (Equiv.Perm (Option K))) := Or.inl hsigma
    rw [← hRange] at hsigma'
    exact hsigma'
  have hTau_mem_range : tau ∈ rho.range := by
    have htauDouble : tau ∈
        DoubleCoset.doubleCoset tau
          (A : Set (Equiv.Perm (Option K)))
          (A : Set (Equiv.Perm (Option K))) :=
      DoubleCoset.mem_doubleCoset.mpr
        ⟨1, A.one_mem, 1, A.one_mem, by simp⟩
    have htau' : tau ∈
        (A : Set (Equiv.Perm (Option K))) ∪
          DoubleCoset.doubleCoset tau
            (A : Set (Equiv.Perm (Option K)))
            (A : Set (Equiv.Perm (Option K))) := Or.inr htauDouble
    rw [← hRange] at htau'
    exact htau'
  have hTau := xi26_tau_inverse hchar rho.range A tau affinePerm
    hAffinePerm hA hA_le_range hTau_mem_range hA_fix_infty
    hTauInf hTauZero hTauSq theta hThetaApply hThetaSquare
  exact xi26_pglRange_of_tau rho A tau affinePerm hAffinePerm hA hTau
    hRange hRangeCard

end External
end CFSG.BenderSuzuki
