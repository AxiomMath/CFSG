module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Sporadic.Co2I301.Inputs
public import CFSG.Sporadic.Co2Schreier.SixGroup
import CFSG.Sporadic.Co2Schreier.IndexNineVecK

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier.IndexNineData

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2I301
  CFSG.Sporadic.SmallF2
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  (basisMatrixEquiv basisMatrixEquiv_mulVec basisMatrixEquiv_val)
open scoped Matrix BigOperators

@[expose] def xorAux (arr : Array ℕ) (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
    xorAux arr m fuel (i + 1) (if m.testBit i then acc ^^^ arr[i]! else acc)

@[expose] def xorE (arr : Array ℕ) (m : ℕ) : ℕ := xorAux arr m arr.size 0 0

@[expose] def co2NineXorF (c : Fin 6 → ℕ) (m : ℕ) : ℕ := xorE (Array.ofFn c) m

theorem toVecD_xorAux (d : ℕ) (arr : Array ℕ) (m : ℕ) :
    ∀ (fuel i acc : ℕ),
      toVecD d (xorAux arr m fuel i acc) =
        toVecD d acc + ∑ j ∈ Finset.range fuel,
          (if m.testBit (i + j) then toVecD d arr[(i + j)]! else 0) := by
  intro fuel
  induction fuel with
  | zero => intro i acc; simp [xorAux]
  | succ n ih =>
    intro i acc
    have hS :
        (∑ j ∈ Finset.range n,
          (if m.testBit (i + 1 + j) then toVecD d arr[(i + 1 + j)]! else 0)) =
        (∑ j ∈ Finset.range n,
          (if m.testBit (i + (j + 1)) then toVecD d arr[(i + (j + 1))]! else 0)) :=
      Finset.sum_congr rfl fun j _ => by rw [show i + 1 + j = i + (j + 1) by omega]
    rw [xorAux, ih, Finset.sum_range_succ', hS]
    by_cases h : m.testBit i
    · rw [if_pos h, toVecD_xor]
      simp only [Nat.add_zero, if_pos h]
      abel
    · rw [if_neg h]
      simp only [Nat.add_zero, if_neg h, add_zero]

theorem toVecD_xorE (d : ℕ) (arr : Array ℕ) (m : ℕ) :
    toVecD d (xorE arr m) =
      ∑ j ∈ Finset.range arr.size, (if m.testBit j then toVecD d arr[j]! else 0) := by
  rw [xorE, toVecD_xorAux, toVecD_zero, zero_add]
  refine Finset.sum_congr rfl fun j _ => by rw [Nat.zero_add]

theorem toVecD_xorF (d : ℕ) (c : Fin 6 → ℕ) (m : ℕ) :
    toVecD d (co2NineXorF c m) =
      ∑ j : Fin 6, (if m.testBit (j : ℕ) then toVecD d (c j) else 0) := by
  rw [co2NineXorF, toVecD_xorE]
  simp only [Array.size_ofFn]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [getElem!_ofFn_nat]

theorem sixAction_sixBasis_colsE (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300)))
    {col : Fin 6 → ℕ}
    (hvec : ∀ k : Fin 6, toVecD 22 (sixImage t (k : ℕ)) =
      ∑ j : Fin 6, toVecD 6 (col k) j • sixVec j) (k : Fin 6) :
    sixAction c (sixBasis k) = ∑ j : Fin 6, toVecD 6 (col k) j • sixBasis j := by
  apply Subtype.ext
  rw [sixAction_apply, sixBasis_apply, linC_sixVec, ← toVecD_sixImage ht k,
    hvec k, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, sixBasis_apply]

theorem toMatrix_sixAction_colsE (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300)))
    {col : Fin 6 → ℕ}
    (hvec : ∀ k : Fin 6, toVecD 22 (sixImage t (k : ℕ)) =
      ∑ j : Fin 6, toVecD 6 (col k) j • sixVec j) :
    LinearMap.toMatrix sixBasis sixBasis (sixAction c : V6 →ₗ[ZMod 2] V6) =
      Matrix.of fun j k : Fin 6 => toVecD 6 (col k) j := by
  ext j k
  rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, sixAction_sixBasis_colsE c ht hvec k,
    Module.Basis.repr_sum_self, Matrix.of_apply]

theorem sixAction_sixPt_colsE (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300)))
    {col : Fin 6 → ℕ}
    (hvec : ∀ k : Fin 6, toVecD 22 (sixImage t (k : ℕ)) =
      ∑ j : Fin 6, toVecD 6 (col k) j • sixVec j)
    {p : ℕ} (hp : p < 63) (hpos : 0 < co2NineXorF col (p + 1))
    (hlt : co2NineXorF col (p + 1) < 64) :
    sixAction c (sixPt p) = sixPt (co2NineXorF col (p + 1) - 1) := by
  have hright : sixBasis.equivFun (sixPt (co2NineXorF col (p + 1) - 1)) =
      toVecD 6 (co2NineXorF col (p + 1)) := by
    rw [sixPt, LinearEquiv.apply_symm_apply,
      show co2NineXorF col (p + 1) - 1 + 1 = co2NineXorF col (p + 1) by omega]
  apply sixBasis.equivFun.injective
  rw [hright]
  change sixBasis.repr ((sixAction c : V6 →ₗ[ZMod 2] V6) (sixPt p)) =
    toVecD 6 (co2NineXorF col (p + 1))
  rw [← LinearMap.toMatrix_mulVec_repr (v₁ := sixBasis) (v₂ := sixBasis)
    (f := (sixAction c : V6 →ₗ[ZMod 2] V6)) (x := sixPt p),
    toMatrix_sixAction_colsE c ht hvec]
  simp only [sixPt, Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [toVecD_xorF]
  congr 1
  ext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.of_apply, toVecD_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoord : sixBasis.repr (sixBasis.equivFun.symm (toVecD 6 (p + 1))) = toVecD 6 (p + 1) := by
    simp [Module.Basis.equivFun]
  rw [hcoord]
  by_cases ha : (col i).testBit (j : ℕ) <;> by_cases hb : (p + 1).testBit (i : ℕ) <;>
    simp [ha, hb, mul_comm, toVecD_apply]

@[expose] def sLit (i : ℕ) : Array ℕ := localRec.chains.S.origArrs[i]!

@[expose] def co2NineColAt : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, 1 => 2
  | 0, 2 => 4
  | 0, 3 => 8
  | 0, 4 => 16
  | 0, 5 => 32
  | 1, 0 => 1
  | 1, 1 => 2
  | 1, 2 => 4
  | 1, 3 => 8
  | 1, 4 => 16
  | 1, 5 => 32
  | 2, 0 => 1
  | 2, 1 => 2
  | 2, 2 => 4
  | 2, 3 => 8
  | 2, 4 => 16
  | 2, 5 => 32
  | 3, 0 => 1
  | 3, 1 => 2
  | 3, 2 => 4
  | 3, 3 => 8
  | 3, 4 => 16
  | 3, 5 => 32
  | 4, 0 => 1
  | 4, 1 => 2
  | 4, 2 => 4
  | 4, 3 => 8
  | 4, 4 => 16
  | 4, 5 => 32
  | 5, 0 => 1
  | 5, 1 => 2
  | 5, 2 => 4
  | 5, 3 => 8
  | 5, 4 => 16
  | 5, 5 => 32
  | 6, 0 => 1
  | 6, 1 => 2
  | 6, 2 => 4
  | 6, 3 => 8
  | 6, 4 => 16
  | 6, 5 => 32
  | 7, 0 => 1
  | 7, 1 => 2
  | 7, 2 => 4
  | 7, 3 => 8
  | 7, 4 => 16
  | 7, 5 => 32
  | 8, 0 => 55
  | 8, 1 => 46
  | 8, 2 => 36
  | 8, 3 => 40
  | 8, 4 => 28
  | 8, 5 => 32
  | 9, 0 => 55
  | 9, 1 => 2
  | 9, 2 => 18
  | 9, 3 => 30
  | 9, 4 => 6
  | 9, 5 => 32
  | 10, 0 => 55
  | 10, 1 => 2
  | 10, 2 => 36
  | 10, 3 => 40
  | 10, 4 => 48
  | 10, 5 => 32
  | 11, 0 => 33
  | 11, 1 => 2
  | 11, 2 => 36
  | 11, 3 => 40
  | 11, 4 => 48
  | 11, 5 => 32
  | 12, 0 => 59
  | 12, 1 => 20
  | 12, 2 => 50
  | 12, 3 => 62
  | 12, 4 => 48
  | 12, 5 => 32
  | 13, 0 => 1
  | 13, 1 => 3
  | 13, 2 => 51
  | 13, 3 => 37
  | 13, 4 => 60
  | 13, 5 => 58
  | 14, 0 => 13
  | 14, 1 => 7
  | 14, 2 => 18
  | 14, 3 => 30
  | 14, 4 => 47
  | 14, 5 => 32
  | _, _ => 0

@[expose] def colFun (i : ℕ) : Fin 6 → ℕ := fun k => co2NineColAt i k

@[expose] def co2NineSC (i : ℕ) : locC := ⟨sTuple.getD i 1, getD_one_mem_of sTuple_mem_C i⟩

theorem sLit_rep (i : ℕ) (hi : i < 15) :
    Rep 2300 (sLit i) (co2NineSC i) := by
  have hcount : chainS.originalCount = 15 := by
    rw [← chainS_arrays.orig_size, localShape.chainS.origArrs_size]
  let k : Fin chainS.originalCount := ⟨i, by omega⟩
  have hlit : Rep 2300 (sLit i) (chainS.original.get k) := chainS_arrays.orig k
  have harr : Rep 2300 (sArrs[i]!) (sTuple.getD i 1) :=
    repTuple_s.rep (by rw [sTuple_length]; exact hi)
  have hperm : chainS.original.get k = sTuple.getD i 1 :=
    eq_of_eqA hlit harr (wordFacts.eqS i hi)
  rw [hperm] at hlit
  exact hlit

theorem sLit_vec_0 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 0) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 0 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_0 : ∀ p < 63,
    0 < co2NineXorF (colFun 0) (p + 1) ∧ co2NineXorF (colFun 0) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_0 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 0) (sixPt p) = sixPt (co2NineXorF (colFun 0) (p + 1) - 1) := by
  have hp' := col_pos_lt_0 p hp
  exact sixAction_sixPt_colsE (co2NineSC 0) (sLit_rep (i := 0) (by norm_num))
    (sLit_vec_0) hp hp'.1 hp'.2

theorem sLit_vec_1 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 1) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 1 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_1 : ∀ p < 63,
    0 < co2NineXorF (colFun 1) (p + 1) ∧ co2NineXorF (colFun 1) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_1 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 1) (sixPt p) = sixPt (co2NineXorF (colFun 1) (p + 1) - 1) := by
  have hp' := col_pos_lt_1 p hp
  exact sixAction_sixPt_colsE (co2NineSC 1) (sLit_rep (i := 1) (by norm_num))
    (sLit_vec_1) hp hp'.1 hp'.2

theorem sLit_vec_2 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 2) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 2 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_2 : ∀ p < 63,
    0 < co2NineXorF (colFun 2) (p + 1) ∧ co2NineXorF (colFun 2) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_2 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 2) (sixPt p) = sixPt (co2NineXorF (colFun 2) (p + 1) - 1) := by
  have hp' := col_pos_lt_2 p hp
  exact sixAction_sixPt_colsE (co2NineSC 2) (sLit_rep (i := 2) (by norm_num))
    (sLit_vec_2) hp hp'.1 hp'.2

theorem sLit_vec_3 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 3) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 3 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_3 : ∀ p < 63,
    0 < co2NineXorF (colFun 3) (p + 1) ∧ co2NineXorF (colFun 3) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_3 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 3) (sixPt p) = sixPt (co2NineXorF (colFun 3) (p + 1) - 1) := by
  have hp' := col_pos_lt_3 p hp
  exact sixAction_sixPt_colsE (co2NineSC 3) (sLit_rep (i := 3) (by norm_num))
    (sLit_vec_3) hp hp'.1 hp'.2

theorem sLit_vec_4 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 4) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 4 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_4 : ∀ p < 63,
    0 < co2NineXorF (colFun 4) (p + 1) ∧ co2NineXorF (colFun 4) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_4 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 4) (sixPt p) = sixPt (co2NineXorF (colFun 4) (p + 1) - 1) := by
  have hp' := col_pos_lt_4 p hp
  exact sixAction_sixPt_colsE (co2NineSC 4) (sLit_rep (i := 4) (by norm_num))
    (sLit_vec_4) hp hp'.1 hp'.2

theorem sLit_vec_5 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 5) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 5 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_5 : ∀ p < 63,
    0 < co2NineXorF (colFun 5) (p + 1) ∧ co2NineXorF (colFun 5) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_5 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 5) (sixPt p) = sixPt (co2NineXorF (colFun 5) (p + 1) - 1) := by
  have hp' := col_pos_lt_5 p hp
  exact sixAction_sixPt_colsE (co2NineSC 5) (sLit_rep (i := 5) (by norm_num))
    (sLit_vec_5) hp hp'.1 hp'.2

theorem sLit_vec_6 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 6) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 6 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_6 : ∀ p < 63,
    0 < co2NineXorF (colFun 6) (p + 1) ∧ co2NineXorF (colFun 6) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_6 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 6) (sixPt p) = sixPt (co2NineXorF (colFun 6) (p + 1) - 1) := by
  have hp' := col_pos_lt_6 p hp
  exact sixAction_sixPt_colsE (co2NineSC 6) (sLit_rep (i := 6) (by norm_num))
    (sLit_vec_6) hp hp'.1 hp'.2

theorem sLit_vec_7 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 7) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 7 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_7 : ∀ p < 63,
    0 < co2NineXorF (colFun 7) (p + 1) ∧ co2NineXorF (colFun 7) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_7 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 7) (sixPt p) = sixPt (co2NineXorF (colFun 7) (p + 1) - 1) := by
  have hp' := col_pos_lt_7 p hp
  exact sixAction_sixPt_colsE (co2NineSC 7) (sLit_rep (i := 7) (by norm_num))
    (sLit_vec_7) hp hp'.1 hp'.2

theorem sLit_vec_8 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 8) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 8 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_8 : ∀ p < 63,
    0 < co2NineXorF (colFun 8) (p + 1) ∧ co2NineXorF (colFun 8) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_8 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 8) (sixPt p) = sixPt (co2NineXorF (colFun 8) (p + 1) - 1) := by
  have hp' := col_pos_lt_8 p hp
  exact sixAction_sixPt_colsE (co2NineSC 8) (sLit_rep (i := 8) (by norm_num))
    (sLit_vec_8) hp hp'.1 hp'.2

theorem sLit_vec_9 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 9) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 9 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_9 : ∀ p < 63,
    0 < co2NineXorF (colFun 9) (p + 1) ∧ co2NineXorF (colFun 9) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_9 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 9) (sixPt p) = sixPt (co2NineXorF (colFun 9) (p + 1) - 1) := by
  have hp' := col_pos_lt_9 p hp
  exact sixAction_sixPt_colsE (co2NineSC 9) (sLit_rep (i := 9) (by norm_num))
    (sLit_vec_9) hp hp'.1 hp'.2

theorem sLit_vec_10 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 10) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 10 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_10 : ∀ p < 63,
    0 < co2NineXorF (colFun 10) (p + 1) ∧ co2NineXorF (colFun 10) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_10 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 10) (sixPt p) = sixPt (co2NineXorF (colFun 10) (p + 1) - 1) := by
  have hp' := col_pos_lt_10 p hp
  exact sixAction_sixPt_colsE (co2NineSC 10) (sLit_rep (i := 10) (by norm_num))
    (sLit_vec_10) hp hp'.1 hp'.2

theorem sLit_vec_11 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 11) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 11 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_11 : ∀ p < 63,
    0 < co2NineXorF (colFun 11) (p + 1) ∧ co2NineXorF (colFun 11) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_11 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 11) (sixPt p) = sixPt (co2NineXorF (colFun 11) (p + 1) - 1) := by
  have hp' := col_pos_lt_11 p hp
  exact sixAction_sixPt_colsE (co2NineSC 11) (sLit_rep (i := 11) (by norm_num))
    (sLit_vec_11) hp hp'.1 hp'.2

theorem sLit_vec_12 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 12) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 12 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_12 : ∀ p < 63,
    0 < co2NineXorF (colFun 12) (p + 1) ∧ co2NineXorF (colFun 12) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_12 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 12) (sixPt p) = sixPt (co2NineXorF (colFun 12) (p + 1) - 1) := by
  have hp' := col_pos_lt_12 p hp
  exact sixAction_sixPt_colsE (co2NineSC 12) (sLit_rep (i := 12) (by norm_num))
    (sLit_vec_12) hp hp'.1 hp'.2

theorem sLit_vec_13 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 13) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 13 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_13 : ∀ p < 63,
    0 < co2NineXorF (colFun 13) (p + 1) ∧ co2NineXorF (colFun 13) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_13 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 13) (sixPt p) = sixPt (co2NineXorF (colFun 13) (p + 1) - 1) := by
  have hp' := col_pos_lt_13 p hp
  exact sixAction_sixPt_colsE (co2NineSC 13) (sLit_rep (i := 13) (by norm_num))
    (sLit_vec_13) hp hp'.1 hp'.2

theorem sLit_vec_14 : ∀ k : Fin 6,
    toVecD 22 (sixImage (sLit 14) (k : ℕ)) = ∑ j : Fin 6, toVecD 6 (colFun 14 k) j • sixVec j := by
  intro k
  rw [IndexNineVecK.sum_sixVec_xor6, sLit, ChainRecord.origArrs_get _ ?hk,
    IndexNineVecK.sixImage_toArray]
  case hk => decide +kernel
  refine congrArg (toVecD 22) ?_
  fin_cases k <;> decide +kernel

theorem col_pos_lt_14 : ∀ p < 63,
    0 < co2NineXorF (colFun 14) (p + 1) ∧ co2NineXorF (colFun 14) (p + 1) < 64 := by
  intro p hp
  interval_cases p <;> decide +kernel

theorem sPt_eq_14 (p : ℕ) (hp : p < 63) :
    sixAction (co2NineSC 14) (sixPt p) = sixPt (co2NineXorF (colFun 14) (p + 1) - 1) := by
  have hp' := col_pos_lt_14 p hp
  exact sixAction_sixPt_colsE (co2NineSC 14) (sLit_rep (i := 14) (by norm_num))
    (sLit_vec_14) hp hp'.1 hp'.2

@[expose] def co2NineCode (i p : ℕ) : ℕ := co2NineXorF (colFun i) (p + 1) - 1

@[expose] def allLtE : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && allLtE n f

theorem allLtE_eq (n : ℕ) (f : ℕ → Bool) :
    allLtE n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allLtE]
  | succ n ih =>
    rw [allLtE, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

@[expose] def pairFixed (i x y : ℕ) : Bool :=
  (co2NineCode i x == x && co2NineCode i y == y) || (co2NineCode i x == y && co2NineCode i y == x)

@[expose] def co2NineFixedOK : Bool := allLtE 15 fun i => co2NineCode i 43 == 43

@[expose] def pairPreservedOK : Bool := allLtE 15 fun i => pairFixed i 25 53

theorem fixedOK_true : co2NineFixedOK = true := by decide +kernel

theorem pairPreservedOK_true : pairPreservedOK = true := by decide +kernel

end CFSG.Sporadic.Co2Schreier.IndexNineData

end
