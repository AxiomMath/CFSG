module

public import CFSG.Quasithin.Background.B69SL2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F918U3
public import CFSG.Quasithin.Background.SmithB51LnModel
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Native
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.KGC31.J4M4

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Sporadic.J4
open CFSG.Quasithin.B5.Ln (mat dmat ofGL)
open scoped Matrix

@[expose] def glOf (a b : ℕ) (h : D35Chk.bmul a b = D35Chk.idm ∧ D35Chk.bmul b a = D35Chk.idm) :
    GL (Fin 5) (ZMod 2) where
  val := D35Chk.bm a
  inv := D35Chk.bm b
  val_inv := by rw [← D35Chk.bm_bmul, h.1, D35Chk.bm_idm]
  inv_val := by rw [← D35Chk.bm_bmul, h.2, D35Chk.bm_idm]

@[expose] def gCode (m : ℕ) : ℕ :=
  if m = 0 then 17457231 else if m = 1 then 25454420 else D35Chk.idm

@[expose] def gInvCode (m : ℕ) : ℕ :=
  if m = 0 then 17457231 else if m = 1 then 25454164 else D35Chk.idm

theorem gCode_spec (m : ℕ) : D35Chk.bmul (gCode m) (gInvCode m) = D35Chk.idm ∧
    D35Chk.bmul (gInvCode m) (gCode m) = D35Chk.idm := by
  unfold gCode gInvCode
  split_ifs <;> decide +kernel

@[expose] def gam (m : ℕ) : ↥(StatedSL 5 (ZMod 2)) :=
  ofGL (glOf (gCode m) (gInvCode m) (gCode_spec m))

theorem mat_gam (m : ℕ) : mat (gam m) = D35Chk.bm (gCode m) := rfl

theorem mat_gam_inv (m : ℕ) : mat (gam m)⁻¹ = D35Chk.bm (gInvCode m) := rfl

theorem gam_eq_one {m : ℕ} (hm : 2 ≤ m) : gam m = 1 := by
  apply B5.Ln.mat_injective
  rw [mat_gam, B5.Ln.mat_one, gCode, ite_eq_right (by omega), ite_eq_right (by omega),
    D35Chk.bm_idm]

@[expose] def letCode (l : ℤ) : ℕ :=
  if 0 < l then gCode (l.toNat - 1) else gInvCode ((-l).toNat - 1)

@[expose] def ev5 (w : List ℤ) : ℕ :=
  w.foldl (fun acc l => D35Chk.bmul acc (letCode l)) D35Chk.idm

theorem bm_foldl_letCode (w : List ℤ) (acc : ℕ) :
    D35Chk.bm (w.foldl (fun acc l => D35Chk.bmul acc (letCode l)) acc) =
      D35Chk.bm acc * mat (wordProd gam w) := by
  induction w generalizing acc with
  | nil => simp [wordProd]
  | cons l w ih =>
    rw [List.foldl_cons, ih, D35Chk.bm_bmul, Matrix.mul_assoc]
    congr 1
    unfold wordProd
    rw [List.map_cons, List.prod_cons, B5.Ln.mat_mul]
    congr 1
    unfold letCode
    split_ifs <;> rfl

theorem bm_ev5 (w : List ℤ) : D35Chk.bm (ev5 w) = mat (wordProd gam w) := by
  rw [ev5, bm_foldl_letCode, D35Chk.bm_idm, Matrix.one_mul]

theorem eq_top_of_transvections (H : Subgroup ↥(StatedSL 5 (ZMod 2)))
    (h : ∀ i j : Fin 5, i ≠ j → ∀ g : ↥(StatedSL 5 (ZMod 2)),
      mat g = Matrix.transvection i j 1 → g ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  set e := specialLinearGroupEquivStatedSL 5 (ZMod 2)
  obtain ⟨A, rfl⟩ := e.surjective g
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun A => e A ∈ H) A
    ?_ ?_ fun A B hA hB => by rw [map_mul]; exact H.mul_mem hA hB
  · intro i j hij c hc
    have hc1 : c = 1 := by revert c; decide
    subst hc1
    have h1 : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 :=
      Matrix.SpecialLinearGroup.ext _ _ fun a b => by
        simp [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply, Matrix.one_apply]
    show e _ ∈ H
    rw [h1, map_one]
    exact H.one_mem
  · intro i j hij c
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · show e _ ∈ H
      rw [Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
      exact H.one_mem
    · exact h i j hij _ (specialLinearGroupEquivStatedSL_coe 5 (ZMod 2) _)

@[expose] def tvWords : List (List Int) := [
    [],
    [-2, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, 1, 2, 1, -2, 1, 2, 1,
     -2, 1, -2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1,
     2, 1, 2, 1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, 1, -2, 1, -2],
    [1, 2, 1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -2, -1, 2, 1, 2, 1, -2, 1, -2, 1,
     2, 1, -2, 1, -2, 1, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 2, -1, -2, -1, 2, -1, 2,
     -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -1, -2, -1, -2, -1, 2, -1],
    [-2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1,
     -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1,
     -2, 1, 2, 1, 2, 2, 1, -2, -1, 2, -1, -2, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2,
     -1, 2, -1, -2, -1, 2, -1],
    [1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, -1, -2, -1, 2, -1, -2, -1, 2, 2, 1, 2, 1,
     -2, 1, -2, -2, -1, -1, -2, -1, -2, -1, -2, -1],
    [-1, -2, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, 1, -2,
     1, 2, 1, -2, 1, -2, 1, 2, -1, -2, -2, -1, -2, -1, -2, 1, 2, -1, -2, -1, 2, -1, -2, -2, -1,
     -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1,
     -2, 1, 2, 1, -2, 1, 2, 2, 2, -1, -2, -1],
    [],
    [-1, -2, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, 1, -2,
     1, 2, 1, -2, 1, -2, 1, 2, -1, -2, -2, -1, -2, -1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1,
     2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, -2],
    [-2, -2],
    [2, -1, -2, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -1,
     -2, -1, -2, -1, -2, -1, -1, -2, -2, -1, -2, -1, -2, -2, -1],
    [1, 2, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -2, -1, -2, -1, -2, -1, 2, -1,
     -2, -1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -1, 2, -1,
     -2, -1, -2, -1, 2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2,
     1, 2, 2, 2, -1, -2, -1],
    [1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1,
     -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
     2, 1, -2, 1, -2, 1, 2, 2, 1, -2, -1, -2, -1],
    [],
    [1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2],
    [1, 2, 1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -2, -1, 2, 1, 2, 1, -2, 1, -2, 1,
     2, 1, -2, 1, -2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -1,
     -2, -1, -2, -1, -2, -1, -1, -2, -2, -1, -2, -1, -2, -2, -1],
    [2, -1, -2, -2, -1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, -2, -1, 2, -1,
     -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1],
    [2, -1, -2, -2, -1, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1,
     -2],
    [-2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2,
     -1, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1,
     -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1,
     -2, 1, 2, 1, 2, -1, -2, -1, -2, -1, 2, -1],
    [],
    [1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1,
     -2, 1, -2, -2, -1, 2, -1, -2, -1, 2, -1, -1, -2, -1, -2, -1, -2, -1],
    [1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, -2, -2, -1,
     -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -1, 2, -1, 2, 2, 1, 2, 1, -2,
     1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 2, -1, -2, -1],
    [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, -1, -2, -1, 2, -1, -2, -1, 2,
     2, 2, 1, -2, 1, 2, 2, 1, 1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -2, -1, -2, -1,
     -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, -2, -1, -2, -1],
    [2, -1, -2, -2, -1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, -2],
    [1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1,
     2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -1, -2, -1, -2, -1, -2, -1,
     -2, -2],
    []]


theorem ev5_tvWords : ∀ i < 5, ∀ j < 5, i ≠ j →
    ev5 (tvWords.getD (5 * i + j) []) = Nat.xor D35Chk.idm (2 ^ (5 * i + j)) := by
  decide +kernel

theorem bm_two_pow (i j : Fin 5) :
    D35Chk.bm (2 ^ (5 * (i : ℕ) + j)) = Matrix.single i j (1 : ZMod 2) := by
  ext a b
  have h : (5 * (i : ℕ) + j = 5 * a + b) ↔ (i = a ∧ j = b) := by
    constructor
    · intro h
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [D35Chk.bm, Nat.testBit_two_pow, decide_eq_true_eq, h, Matrix.single_apply]

theorem mat_wordProd_tv {i j : Fin 5} (hij : i ≠ j) :
    mat (wordProd gam (tvWords.getD (5 * i + j) [])) = Matrix.transvection i j 1 := by
  rw [← bm_ev5, ev5_tvWords i i.2 j j.2 (fun h => hij (Fin.ext h)), D35Chk.bm_xor,
    D35Chk.bm_idm, bm_two_pow]
  rfl

theorem gam_mem_closure (m : ℕ) : gam m ∈ Subgroup.closure {gam 0, gam 1} := by
  rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rw [gam_eq_one hm]
    exact Subgroup.one_mem _

theorem closure_gam_eq_top : Subgroup.closure {gam 0, gam 1} = ⊤ := by
  refine eq_top_of_transvections _ fun i j hij g hg => ?_
  have h := mat_wordProd_tv hij
  rw [← hg] at h
  rw [← B5.Ln.mat_injective h]
  exact wordProd_mem _ gam_mem_closure _

@[expose] def ptCodes : List ℕ :=
  [1, 4, 9, 26, 11, 7, 24, 25, 13, 27, 15, 14, 29, 17, 12, 19, 31, 30, 18, 10, 21, 6, 28, 20, 3, 16,
    8, 22, 2, 23, 5]

@[expose] def vec5 (p : ℕ) : Fin 5 → ZMod 2 := fun i => if p.testBit i then 1 else 0

@[expose] def code5 (u : Fin 5 → ZMod 2) : ℕ := ∑ i : Fin 5, (u i).val * 2 ^ (i : ℕ)

theorem vec5_code5 : ∀ u : Fin 5 → ZMod 2, vec5 (code5 u) = u := by decide +kernel

theorem code5_vec5 : ∀ p < 32, code5 (vec5 p) = p := by decide +kernel

theorem code5_pos : ∀ u : Fin 5 → ZMod 2, u ≠ 0 → 1 ≤ code5 u ∧ code5 u < 32 := by
  decide +kernel

theorem ptCodes_idxOf : ∀ p < 32, 1 ≤ p →
    ptCodes.idxOf p < 31 ∧ ptCodes.getD (ptCodes.idxOf p) 0 = p := by decide +kernel

theorem idxOf_ptCodes : ∀ k < 31, ptCodes.idxOf (ptCodes.getD k 0) = k ∧
    ptCodes.getD k 0 < 32 := by decide +kernel

theorem kwSig_lt : ∀ l < 2, ∀ k < 31, (kwSig.getD l []).getD k 0 < 31 := by decide +kernel

@[expose] def ptIdx (u : Fin 5 → ZMod 2) : ℕ := ptCodes.idxOf (code5 u)

theorem ptIdx_spec {u : Fin 5 → ZMod 2} (hu : u ≠ 0) :
    ptIdx u < 31 ∧ vec5 (ptCodes.getD (ptIdx u) 0) = u := by
  obtain ⟨h1, h2⟩ := code5_pos u hu
  obtain ⟨h3, h4⟩ := ptCodes_idxOf _ h2 h1
  exact ⟨h3, by rw [ptIdx, h4, vec5_code5]⟩

theorem ptIdx_vec5 {k : ℕ} (hk : k < 31) : ptIdx (vec5 (ptCodes.getD k 0)) = k := by
  obtain ⟨h1, h2⟩ := idxOf_ptCodes k hk
  rw [ptIdx, code5_vec5 _ h2, h1]

theorem vec5_ne_zero {k : ℕ} (hk : k < 31) : vec5 (ptCodes.getD k 0) ≠ 0 := by
  revert k
  decide +kernel

theorem bm_gCode_ptCodes : ∀ l < 2, ∀ k < 31, D35Chk.bm (gCode l) *ᵥ vec5 (ptCodes.getD k 0) =
    vec5 (ptCodes.getD ((kwSig.getD l []).getD k 0) 0) := by decide +kernel

theorem gam_ptCodes {l : ℕ} (hl : l < 2) {k : ℕ} (hk : k < 31) :
    mat (gam l) *ᵥ vec5 (ptCodes.getD k 0) = vec5 (ptCodes.getD ((kwSig.getD l []).getD k 0) 0) :=
  bm_gCode_ptCodes l hl k hk

theorem card_statedSL5' : Nat.card ↥(StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

theorem isPSL_of_equiv5 {X : Type} [Group X] (e : X ≃* ↥(StatedSL 5 (ZMod 2))) :
    CFSG.Quasithin.IsPSL 5 2 1 X :=
  ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod]; norm_num,
    ⟨e.trans (CFSG.Quasithin.B69.statedSLEquivStatedProj (by rw [Nat.card_zmod]) 5)⟩⟩

end CFSG.Quasithin.KGC31.J4M4

end
