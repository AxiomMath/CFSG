
module

public import CFSG.Sporadic.Fi24.SepSpecBase
import all CFSG.Sporadic.Fi24.SepSpecBase


public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi24.Native

open Matrix CFSG.F3.Native

section Algebra

variable (mats : Array (Array W))

variable {mats}

theorem MatsOK.get {mats : Array (Array W)} (h : MatsOK mats) {i : ℕ} (hi : i < mats.size) :
    canonRows 781 (mats[i]?.getD #[]) = true := by
  have := h i hi
  rwa [getElem!_pos mats i hi, ← Option.getD_some (a := mats[i]) (b := #[]),
    ← Array.getElem?_eq_getElem hi] at this

theorem prodW_spec (hm : MatsOK mats) (w : List ℕ) (hw : ∀ x ∈ w, x < mats.size) :
    ∀ M0 : Array W, canonRows 781 M0 = true → matW 781 781 M0 ∈ matsAlg mats →
      canonRows 781 (w.foldl (fun M x => mulW M (mats[x]?.getD #[])) M0) = true ∧
        matW 781 781 (w.foldl (fun M x => mulW M (mats[x]?.getD #[])) M0) ∈ matsAlg mats := by
  induction w with
  | nil => intro M0 h1 h2; exact ⟨h1, h2⟩
  | cons x w ih =>
    intro M0 h1 h2
    have hx : x < mats.size := hw x List.mem_cons_self
    rw [List.foldl_cons]
    have hc := hm.get hx
    refine ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ (canonRows_mulW h1 hc) ?_
    rw [matW_mulW (m := 781) (by norm_num) (RowsWF.of_canonRows h1) (RowsWF.of_canonRows hc)
      (by rw [(canonRows_spec hc).1])]
    exact Subalgebra.mul_mem _ h2 (Algebra.subset_adjoin ⟨x, hx, rfl⟩)

theorem combW_spec (hm : MatsOK mats) (terms : List (ℕ × List ℕ))
    (ht : ∀ t ∈ terms, ∀ x ∈ t.2, x < mats.size) :
    ∀ M0 : Array W, M0.size = 781 → RowsWF M0 → matW 781 781 M0 ∈ matsAlg mats →
      (terms.foldl (fun acc t => let M := prodW 781 mats t.2
          addW 781 acc (if t.1 == 2 then negW M else M)) M0).size = 781 ∧
      RowsWF (terms.foldl (fun acc t => let M := prodW 781 mats t.2
          addW 781 acc (if t.1 == 2 then negW M else M)) M0) ∧
        matW 781 781 (terms.foldl (fun acc t => let M := prodW 781 mats t.2
          addW 781 acc (if t.1 == 2 then negW M else M)) M0) ∈ matsAlg mats := by
  induction terms with
  | nil => intro M0 h1 h2 h3; exact ⟨h1, h2, h3⟩
  | cons t terms ih =>
    intro M0 h1 h2 h3
    rw [List.foldl_cons]
    obtain ⟨hpc, hpm⟩ := prodW_spec hm t.2 (ht t List.mem_cons_self) (idW 781) canonRows_idW
      (by rw [matW_idW (by norm_num)]; exact Subalgebra.one_mem _)
    change canonRows 781 (prodW 781 mats t.2) = true at hpc
    change matW 781 781 (prodW 781 mats t.2) ∈ matsAlg mats at hpm
    have hpw := RowsWF.of_canonRows hpc
    have hP : RowsWF (if t.1 == 2 then negW (prodW 781 mats t.2) else prodW 781 mats t.2) ∧
        matW 781 781 (if t.1 == 2 then negW (prodW 781 mats t.2) else prodW 781 mats t.2) ∈
          matsAlg mats := by
      split_ifs
      · refine ⟨RowsWF.negW hpw, ?_⟩
        rw [matW_negW hpw]
        exact Subalgebra.neg_mem _ hpm
      · exact ⟨hpw, hpm⟩
    refine ih (fun s hs => ht s (List.mem_cons_of_mem _ hs)) _ (addW_size _ _ _)
      (RowsWF.addW _ h2 hP.1) ?_
    rw [matW_addW h2 hP.1]
    exact Subalgebra.add_mem _ h3 hP.2

end Algebra

theorem spinW_spec {mats : Array (Array W)} (hm : MatsOK mats) {v : W} (tree : List (ℕ × ℕ))
    (htree : ∀ t ∈ tree, t.2 < mats.size) :
    ∀ S : Array W, (∀ i : ℕ, (rowW S i).wf = true ∧
        ∃ N ∈ matsAlg mats, vecW (rowW S i) = N.mulVec (vecW v)) →
      ∀ i : ℕ, (rowW (tree.foldl (fun S t => S.push (frApply
          ((mats.map fun M => frTable (transposeW 781 781 M))[t.2]?.getD #[])
          (S[t.1]?.getD W.zero))) S) i).wf = true ∧
        ∃ N ∈ matsAlg mats, vecW (rowW (tree.foldl (fun S t => S.push (frApply
          ((mats.map fun M => frTable (transposeW 781 781 M))[t.2]?.getD #[])
          (S[t.1]?.getD W.zero))) S) i) = N.mulVec (vecW v) := by
  induction tree with
  | nil => intro S hS; exact hS
  | cons t tree ih =>
    intro S hS
    rw [List.foldl_cons]
    apply ih (fun t' ht' => htree t' (List.mem_cons_of_mem _ ht'))
    intro i
    rw [rowW_push]
    split_ifs with h1 h2
    · exact hS i
    · obtain ⟨hw, N, hN, he⟩ := hS t.1
      have hr : t.2 < mats.size := htree t List.mem_cons_self
      have htab : (mats.map fun M => frTable (transposeW 781 781 M))[t.2]?.getD #[] =
          frTable (transposeW 781 781 (mats[t.2]?.getD #[])) := by
        rw [Array.getElem?_map, Array.getElem?_eq_getElem hr, Option.map_some, Option.getD_some,
          Option.getD_some]
      rw [htab]
      have hc := hm.get hr
      have hx : (S[t.1]?.getD W.zero).wf = true := hw
      refine ⟨(frApply_spec (RowsWF.transposeW (by norm_num) _ _) hx 0).1, ?_⟩
      refine ⟨matW 781 781 (mats[t.2]?.getD #[]) * N, Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨t.2, hr, rfl⟩) hN, ?_⟩
      rw [vecW_apply_mat (RowsWF.of_canonRows hc) hx, ← Matrix.mulVec_mulVec]
      exact congrArg _ he
    · refine ⟨W.wf_zero, 0, Subalgebra.zero_mem _, ?_⟩
      rw [vecW_zero, Matrix.zero_mulVec]

theorem scalar_of_sepOKW
    {mats : Array (Array W)} {terms : List (ℕ × List ℕ)} {v : W} {k : ℕ}
    {P Tinv : Array W} {tree : List (ℕ × ℕ)} (h : sepOKW mats terms v k P Tinv tree = true)
    (g : Matrix (Fin 781) (Fin 781) (ZMod 3))
    (hg : ∀ i < mats.size, g * matW 781 781 (mats[i]?.getD #[]) =
      matW 781 781 (mats[i]?.getD #[]) * g) :
    ∃ c : ZMod 3, g = c • 1 := by
  unfold sepOKW at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hvc⟩, hvk⟩, hmats⟩, hPc⟩, hTc⟩, hterms⟩, hwv⟩, hPw⟩, htree⟩, -⟩,
    hSs⟩, hTS⟩ := h
  have hv : v.wf = true := W.canon_wf hvc
  have hm : MatsOK mats := fun i hi => by rw [getElem!_pos mats i hi]; exact hmats i hi
  have hcomm : ∀ N ∈ matsAlg mats, g * N = N * g := by
    intro N hN
    have hle : matsAlg mats ≤ Subalgebra.centralizer (ZMod 3) {g} := by
      unfold matsAlg
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hg i hi
    have := hle hN
    rw [Subalgebra.mem_centralizer_iff] at this
    exact this g rfl
  set x := vecW v with hx
  obtain ⟨hws, hwwf, hwmem⟩ := combW_spec hm terms (fun t ht y hy => hterms t ht y hy)
    (zeroW 781) (zeroW_size 781) (RowsWF.zeroW 781)
    (by rw [matW_zeroW]; exact Subalgebra.zero_mem _)
  change (combW 781 mats terms).size = 781 at hws
  change RowsWF (combW 781 mats terms) at hwwf
  change matW 781 781 (combW 781 mats terms) ∈ matsAlg mats at hwmem
  set Wm := matW 781 781 (combW 781 mats terms)
  have hWx : Wm.mulVec x = 0 := by
    rw [← vecW_apply_mat hwwf hv]
    exact W.isZero_vecW hwv
  set y := g.mulVec x
  have hWy : Wm.mulVec y = 0 := by
    rw [Matrix.mulVec_mulVec, ← hcomm Wm hwmem, ← Matrix.mulVec_mulVec, hWx, Matrix.mulVec_zero]
  have hPW := congrArg (matW 781 781) (eq_of_eqRows hPw).2
  rw [matW_mulW (m := 781) (by norm_num) (RowsWF.of_canonRows hPc) hwwf (by omega)] at hPW
  have hy : y = y ⟨k, hk⟩ • x := by
    have h1 := mulVec_projW hv hk y
    rw [← hPW, ← Matrix.mulVec_mulVec, hWy, Matrix.mulVec_zero] at h1
    exact (sub_eq_zero.1 h1.symm)
  set c := y ⟨k, hk⟩
  set S := spinW (mats.map fun M => frTable (transposeW 781 781 M)) v tree
  have hS0 : ∀ i : ℕ, (rowW (#[v] : Array W) i).wf = true ∧
      ∃ N ∈ matsAlg mats, vecW (rowW (#[v] : Array W) i) = N.mulVec x := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact ⟨hv, 1, Subalgebra.one_mem _, by simp [hx, rowW]⟩
    · rw [rowW_ge (by simp; omega)]
      refine ⟨W.wf_zero, 0, Subalgebra.zero_mem _, ?_⟩
      rw [vecW_zero, Matrix.zero_mulVec]
  have hSpec := spinW_spec hm tree (fun t ht => htree t ht) #[v] hS0
  have hSc : ∀ i : ℕ, g.mulVec (vecW (rowW S i)) = c • vecW (rowW S i) := by
    intro i
    obtain ⟨-, N, hN, he⟩ := hSpec i
    change vecW (rowW S i) = N.mulVec x at he
    rw [he, Matrix.mulVec_mulVec, hcomm N hN, ← Matrix.mulVec_mulVec]
    change N.mulVec y = c • N.mulVec x
    rw [hy, Matrix.mulVec_smul]
  set T := matW 781 781 S
  have hSwf : RowsWF S := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hz
    have := (hSpec i).1
    change (rowW S i).wf = true at this
    unfold rowW at this
    rwa [Array.getElem?_eq_getElem hi] at this
  have hTinv := congrArg (matW 781 781) (eq_of_eqRows hTS).2
  rw [matW_mulW (m := 781) (by norm_num) (RowsWF.of_canonRows hTc) hSwf (by omega),
    matW_idW (by norm_num)] at hTinv
  have hgT : g * T.transpose = c • T.transpose := by
    ext r i
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply]
    have := congrFun (hSc i.val) r
    rw [Matrix.mulVec, dotProduct, Pi.smul_apply] at this
    simpa [T, matW_apply, vecW] using this
  have hright : T.transpose * (matW 781 781 Tinv).transpose = 1 := by
    rw [← Matrix.transpose_mul, hTinv, Matrix.transpose_one]
  refine ⟨c, ?_⟩
  calc g = g * (T.transpose * (matW 781 781 Tinv).transpose) := by rw [hright, mul_one]
    _ = (g * T.transpose) * (matW 781 781 Tinv).transpose := by rw [mul_assoc]
    _ = c • 1 := by rw [hgT, smul_mul_assoc, hright]

end CFSG.Sporadic.Fi24.Native
