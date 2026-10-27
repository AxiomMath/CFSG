
module

public import CFSG.Sporadic.Schreier.J4SElevenCheck
public import CFSG.Sporadic.Schreier.J4SFiveBase
public import CFSG.Sporadic.Schreier.J4SFormBase
public import CFSG.Sporadic.Schreier.J4SRankBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SElevenData
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def nrm₁ : J := runProg (initRegs a b) max7Prog 1

@[expose] def nrm₂ : J := runProg (initRegs a b) max7Prog 2

@[expose] def qs : J := nrm₂ ^ 8

@[expose] def qx₀ : J := qs * nrm₁⁻¹ * qs⁻¹ * nrm₁

@[expose] def qy₀ : J := ⁅qs, nrm₁ * nrm₂⁆

@[expose] def qx : J := qx₀ * qy₀ ^ 7

@[expose] def qy : J := qy₀ ^ 3

@[expose] def qz : J := ⁅qx, qy⁆

@[expose] def qu : J := nrm₂ ^ 5

@[expose] def qw : J := qx ^ 3 * qy ^ 9 * qz * signedWord nrm₁ nrm₂ [1, 2, 1, 2, 2, 2, 2]

@[expose] def Q11 : Subgroup J := Subgroup.closure ({qx, qy} : Set J)

theorem rep_commP {g h : J} {P Q : Pair} (hg : Rep Sp φ g P) (hh : Rep Sp φ h Q) :
    Rep Sp φ ⁅g, h⁆ (commP P Q) := by
  rw [commutatorElement_def]
  exact rep_mulP (rep_mulP (rep_mulP hg hh) (rep_invP hg)) (rep_invP hh)

theorem eq_of_rep_check {g h : J} {G H : Pair} (hg : Rep Sp φ g G) (hh : Rep Sp φ h H)
    (hc : O.eq G.1 H.1 = true) : g = h :=
  φ_injective (by rw [← hg.2.2.1, ← hh.2.2.1]; exact Sp.toMat_eq hg.1 hh.1 hc)

theorem conj_of_rep_check {h x w : J} {Hp Xp Wp : Pair} (hh : Rep Sp φ h Hp)
    (hx : Rep Sp φ x Xp) (hw : Rep Sp φ w Wp) (hc : O.conjOK Hp.1 Xp.1 Wp.1 = true) :
    h * x * h⁻¹ = w := by
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_of_rep_check (rep_mulP hh hx) (rep_mulP hw hh) hc

theorem pow_eq_one_of_rep_check {x : J} {Xp : Pair} (hx : Rep Sp φ x Xp) {n : ℕ}
    (hc : O.eq (O.pow Xp.1 n) O.one = true) : x ^ n = 1 :=
  eq_of_rep_check (rep_powP hx n) rep_oneP hc

theorem qx_mem : qx ∈ Q11 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem qy_mem : qy ∈ Q11 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem qz_mem : qz ∈ Q11 := by
  rw [qz, commutatorElement_def]
  exact Q11.mul_mem (Q11.mul_mem (Q11.mul_mem qx_mem qy_mem) (Q11.inv_mem qx_mem))
    (Q11.inv_mem qy_mem)

theorem commute_pow_qz {g : J} (h : qz * g = g * qz) (k : ℕ) : qz ^ k * g = g * qz ^ k := by
  induction k with
  | zero => rw [pow_zero, one_mul, mul_one]
  | succ k ih => rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]

theorem ne_of_rowsDiffer {M N : Array ℕ} (hM : Sp.WF M) (hN : Sp.WF N)
    (h : rowsDiffer M N = true) : Sp.toMat M ≠ Sp.toMat N := by
  unfold rowsDiffer at h
  obtain ⟨t, -, ht⟩ := List.any_eq_true.1 h
  intro e
  apply Sp.toVec_ne ht
  rw [Sp.toVec_vmul (Sp.unit_wf t) hM, Sp.toVec_vmul (Sp.unit_wf t) hN, e]

theorem mem_normalizer_closure_pair {G : Type*} [Group G] [Finite G] {x y h : G}
    (hx : h * x * h⁻¹ ∈ Subgroup.closure ({x, y} : Set G))
    (hy : h * y * h⁻¹ ∈ Subgroup.closure ({x, y} : Set G)) :
    h ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set G) : Set G) := by
  set R := Subgroup.closure ({x, y} : Set G)
  have hle : R.map (MulAut.conj h).toMonoidHom ≤ R := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  have heq : R.map (MulAut.conj h).toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj h).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← heq]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg', e⟩ := hg
    have e' : g' = g := (MulAut.conj h).injective e
    rwa [← e']

theorem mem_normalizer_Q11 {h : J} (hx : h * qx * h⁻¹ ∈ Q11) (hy : h * qy * h⁻¹ ∈ Q11) :
    h ∈ Subgroup.normalizer (Q11 : Set J) :=
  @mem_normalizer_closure_pair J (Subgroup.toGroup J) _ qx qy h hx hy

theorem qWord_mem (i j k : ℕ) : qx ^ i * qy ^ j * qz ^ k ∈ Q11 :=
  Q11.mul_mem (Q11.mul_mem (Q11.pow_mem qx_mem i) (Q11.pow_mem qy_mem j)) (Q11.pow_mem qz_mem k)

@[expose] def rowFix (M : Matrix (Fin 112) (Fin 112) (ZMod 2)) :
    Submodule (ZMod 2) (Fin 112 → ZMod 2) :=
  LinearMap.eqLocus (Matrix.vecMulLinear M) LinearMap.id

theorem mem_rowFix {M : Matrix (Fin 112) (Fin 112) (ZMod 2)} {v : Fin 112 → ZMod 2} :
    v ∈ rowFix M ↔ v ᵥ* M = v := by
  rw [rowFix, LinearMap.mem_eqLocus, Matrix.vecMulLinear_apply, LinearMap.id_apply]

@[expose] def extZero (k : ℕ) : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2) where
  toFun c i := if h : i.val < k then c ⟨i.val, h⟩ else 0
  map_add' c d := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' r c := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem extZero_apply (k : ℕ) (c : Fin k → ZMod 2) (i : Fin 112) :
    extZero k c i = if h : i.val < k then c ⟨i.val, h⟩ else 0 := rfl

theorem vecMul_dRows (k : ℕ) (c : Fin 112 → ZMod 2) (j : Fin 112) :
    (c ᵥ* rowsMatrix 112 (dRows k)) j = if j.val < k then 0 else c j := by
  rw [Matrix.vecMul, dotProduct]
  have hD : ∀ i : Fin 112, rowsMatrix 112 (dRows k) i j =
      if i = j ∧ ¬ i.val < k then 1 else 0 := by
    intro i
    rw [SmallF2.rowsMatrix_apply, toVecD_apply]
    unfold dRows
    simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
    by_cases hik : i.val < k
    · simp [hik]
    · rw [ite_eq_right hik, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hij : i = j
      · subst hij
        simp [hik]
      · have : i.val ≠ j.val := fun e => hij (Fin.ext e)
        simp [hij, this]
  simp only [hD, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  by_cases hjk : j.val < k
  · rw [ite_eq_left hjk]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := (Finset.mem_filter.1 hi).2
    exact absurd (this.1 ▸ hjk) this.2
  · rw [ite_eq_right hjk]
    rw [Finset.sum_eq_single j]
    · intro i hi hij
      exact absurd (Finset.mem_filter.1 hi).2.1 hij
    · intro hj
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hjk⟩) hj

theorem fixDimOK_spec {G P Pinv R : Array ℕ} {k : ℕ} (h : fixDimOK G P Pinv R k = true) :
    rowsMatrix 112 P * rowsMatrix 112 Pinv = 1 ∧ rowsMatrix 112 Pinv * rowsMatrix 112 P = 1 ∧
      (∀ i : Fin 112, i.val < k → (rowsMatrix 112 P * (rowsMatrix 112 G + 1)) i = 0) ∧
      rowsMatrix 112 P * (rowsMatrix 112 G + 1) * rowsMatrix 112 R = rowsMatrix 112 (dRows k) := by
  unfold fixDimOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hT : rowsMatrix 112 (mulRows 112 P (xorRows112 G (idRows 112))) =
      rowsMatrix 112 P * (rowsMatrix 112 G + 1) := by
    rw [SmallF2.rowsMatrix_mulRows, rowsMatrix_xorRows112, SmallF2.rowsMatrix_idRows]
  refine ⟨?_, ?_, fun i hi => ?_, ?_⟩
  · rw [← SmallF2.rowsMatrix_mulRows, h1, SmallF2.rowsMatrix_idRows]
  · rw [← SmallF2.rowsMatrix_mulRows, h2, SmallF2.rowsMatrix_idRows]
  · rw [← hT]
    funext j
    rw [SmallF2.rowsMatrix_apply, h3 i hi, toVecD_zero]
  · rw [← hT, ← SmallF2.rowsMatrix_mulRows, h4]

theorem finrank_rowFix_of_ok {M : Matrix (Fin 112) (Fin 112) (ZMod 2)} {G P Pinv R : Array ℕ}
    {k : ℕ} (hk : k ≤ 112) (hG : rowsMatrix 112 G = M) (h : fixDimOK G P Pinv R k = true) :
    Module.finrank (ZMod 2) (rowFix M) = k := by
  obtain ⟨h1, h2, h3, h4⟩ := fixDimOK_spec h
  rw [hG] at h3 h4
  have hneg : ∀ w : Fin 112 → ZMod 2, -w = w := fun w =>
    funext fun i => ZMod.neg_eq_self_mod_two (w i)
  have h2' : ∀ v : Fin 112 → ZMod 2, v ᵥ* (M + 1) = 0 ↔ v ᵥ* M = v := by
    intro v
    rw [Matrix.vecMul_add, Matrix.vecMul_one, add_eq_zero_iff_eq_neg, hneg]
  set f := (Matrix.vecMulLinear (rowsMatrix 112 P)).comp (extZero k) with hf_def
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hf_def, LinearMap.comp_apply, Matrix.vecMulLinear_apply] at hc
    have e : extZero k c = 0 := by
      calc extZero k c = extZero k c ᵥ* (rowsMatrix 112 P * rowsMatrix 112 Pinv) := by
            rw [h1, Matrix.vecMul_one]
        _ = 0 := by rw [← Matrix.vecMul_vecMul, hc, Matrix.zero_vecMul]
    funext i
    have := congrFun e ⟨i.val, by have := i.isLt; omega⟩
    rw [extZero_apply] at this
    simp only [i.isLt, ↓reduceDIte] at this
    exact this
  have hrange : LinearMap.range f = rowFix M := by
    ext v
    rw [LinearMap.mem_range, mem_rowFix]
    constructor
    · rintro ⟨c, rfl⟩
      rw [← h2', hf_def, LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
        Matrix.vecMul_eq_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [extZero_apply]
      split_ifs with hi
      · rw [h3 i hi, smul_zero]
      · rw [zero_smul]
    · intro hv
      rw [← h2'] at hv
      obtain ⟨c, hc⟩ : ∃ c, c = v ᵥ* rowsMatrix 112 Pinv := ⟨_, rfl⟩
      have hvc : v = c ᵥ* rowsMatrix 112 P := by
        rw [hc, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
      have h0 : c ᵥ* (rowsMatrix 112 P * (M + 1)) = 0 := by
        rw [← Matrix.vecMul_vecMul, ← hvc, hv]
      have hD : c ᵥ* rowsMatrix 112 (dRows k) = 0 := by
        rw [← h4, ← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
      refine ⟨fun i => c ⟨i.val, by have := i.isLt; omega⟩, ?_⟩
      rw [hf_def, LinearMap.comp_apply, Matrix.vecMulLinear_apply]
      conv_rhs => rw [hvc]
      refine congrArg (fun w => w ᵥ* rowsMatrix 112 P) ?_
      funext j
      rw [extZero_apply]
      split_ifs with hj
      · rfl
      · have := congrFun hD j
        rw [vecMul_dRows, ite_eq_right hj] at this
        exact this.symm
  rw [← hrange, LinearMap.finrank_range_of_inj hf, Module.finrank_fin_fun]

theorem evalW_eq (l : List ℕ) (v : Fin 2 → ZMod 11) :
    evalW l v = (l.map letterM).prod *ᵥ v := by
  induction l with
  | nil => rw [evalW, List.foldr_nil, List.map_nil, List.prod_nil, Matrix.one_mulVec]
  | cons i l ih =>
    rw [evalW, List.foldr_cons, ← evalW, ih, List.map_cons, List.prod_cons,
      Matrix.mulVec_mulVec]

theorem matAB_transitive : ∀ v w : Fin 2 → ZMod 11, v ≠ 0 → w ≠ 0 →
    ∃ g ∈ Submonoid.closure ({matA, matB} : Set (Matrix (Fin 2) (Fin 2) (ZMod 11))),
      g *ᵥ v = w := by
  intro v w hv hw
  have h1 := (trans_check w hw).1
  have h2 := (trans_check v hv).2
  refine ⟨((fwdW w ++ bwdW v).map letterM).prod, ?_, ?_⟩
  · refine Submonoid.list_prod_mem _ fun m hm => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hm
    unfold letterM
    split_ifs
    · exact Submonoid.subset_closure (Set.mem_insert _ _)
    · exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rw [List.map_append, List.prod_append, ← Matrix.mulVec_mulVec, ← evalW_eq (bwdW v) v, h2,
      ← evalW_eq, h1]

theorem card_nonzero_eleven : Nat.card {v : Fin 2 → ZMod 11 // v ≠ 0} = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, Fintype.card_unique]
  norm_num

end CFSG.Sporadic.J4Schreier
