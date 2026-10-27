module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2C
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR4S

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.Quasithin.H.Coc24
  CFSG.Quasithin.E3 CFSG.Quasithin.H13 CFSG.Quasithin.H13.L828T CFSG.Quasithin.H13.Mat.MB2C

@[expose] def mb2LC4 : List ℕ := [922, 513, 1466, 1281, 1323, 599]

@[expose] noncomputable def mb2Gens4 : List (MulAut W11) := [rhoTrA, rhoTrB]

@[expose] def mb2Cols4 : List (List ℕ) := [trACols, trBCols]

@[expose] def mb2Ms4 : List (List ℕ) :=
  [[2, 8, 16, 3, 36, 4], [4, 3, 2, 32, 24, 16]]

@[expose] def mb2W4 : List (List (ℕ × List ℕ)) :=
  [[(0, [])], [(0, [0])], [(0, [1])], [(0, [0, 0])], [(0, [0, 1])], [(0, [1, 0, 0])]]

@[expose] def mb2E4 : Fin 2 → Fin 2 → List ℕ :=
  matUnits [12, 19, 34, 46, 12, 49] [49, 34, 12, 12, 19, 34] [38, 28, 17, 55, 38, 13]
    [13, 17, 38, 38, 28, 17]

theorem mb2c4_data :
    MaskCoordsData (MaskCoords.std 11) (maskSub 11 mb4L9) UT 6 mb4L9 uTBasis mb2LC4 :=
  MaskCoordsData.std mb4L9_lt uTBasis_lt (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel)

theorem genGroup_mb2Gens4 : genGroup mb2Gens4 = img11 trQ := by
  rw [img11_trQ_closure_r4s]
  exact genGroup_two _ _

theorem mb2c4_hgens : ∀ i < mb2Gens4.length, ∀ m,
    mb2Gens4.getD i 1 ((MaskCoords.std 11).vm m) =
      (MaskCoords.std 11).vm (actM (mb2Cols4.getD i []) m) :=
  hgens_two actsBy_rhoTrA actsBy_rhoTrB

theorem mb2c4_check : ∀ i < 2, ∀ j < 6,
    (actM (mb2Cols4.getD i []) (actM mb2LC4 (2 ^ j)) ^^^
      actM mb2LC4 (actM (mb2Ms4.getD i []) (2 ^ j))) ∈ combos uTBasis := by
  decide +kernel

theorem mb2c4_lenM : ∀ M ∈ mb2Ms4, M.length = 6 := by decide +kernel

theorem mb2c4_ltM : ∀ M ∈ mb2Ms4, ∀ x ∈ M, x < 2 ^ 6 := by decide +kernel

theorem mb2c4_invB :
    ∀ g ∈ genGroup mb2Gens4, ∀ b ∈ maskSub 11 mb4L9, g b ∈ maskSub 11 mb4L9 := by
  rw [genGroup_mb2Gens4]
  refine invariant_of_commV_le_mat ?_
  exact (le_sup_left : commV (img11 trQ) ≤ commV (img11 trQ) ⊔ UT).trans
    (le_of_eq std4_commV_sup)

theorem mb2c4_invU : ∀ g ∈ genGroup mb2Gens4, ∀ u ∈ UT, g u ∈ UT := by
  rw [genGroup_mb2Gens4]
  exact fun g hg u hu => ((img11_trQ_le hg).2 u).2 hu

@[expose] noncomputable def mb2Model4 : MB2Model 6 (maskSub 11 mb4L9) UT mb2Gens4 :=
  MB2Model.ofMasks mb2c4_data mb2Gens4 mb2Cols4 mb2Ms4 mb2c4_hgens rfl mb2c4_lenM mb2c4_ltM
    mb2c4_check mb2c4_invB mb2c4_invU

private theorem mb2c4_lenE : ∀ i j, (mb2E4 i j).length = 6 := by decide +kernel

private theorem mb2c4_ltE : ∀ i j, ∀ x ∈ mb2E4 i j, x < 2 ^ 6 := by decide +kernel

private theorem mb2c4_commE : ∀ i j, ∀ k < 2, ∀ m < 2 ^ 6,
    actM (mb2Ms4.getD k []) (actM (mb2E4 i j) m) =
      actM (mb2E4 i j) (actM (mb2Ms4.getD k []) m) := by
  decide +kernel

private theorem mb2c4_mulE : ∀ i j k l, ∀ m < 2 ^ 6,
    actM (mb2E4 i j) (actM (mb2E4 k l) m) = if j = k then actM (mb2E4 i l) m else 0 := by
  decide +kernel

private theorem mb2c4_sumE : ∀ m < 2 ^ 6, actM (mb2E4 0 0) m ^^^ actM (mb2E4 1 1) m = m := by
  decide +kernel

private theorem mb2c4_hW : ∀ j < 6, algAct mb2Ms4 (mb2W4.getD j []) [1] = 2 ^ j := by
  decide +kernel

private theorem mb2c4_count :
    ((tuples 6 [1].length).filter (commCheck mb2Ms4 mb2W4 6)).length ≤ 16 := by
  decide +kernel

theorem mb2_std_row4 :
    Nonempty (↥(commutant (maskSub 11 mb4L9) UT
      ((img11 trQ : Subgroup (MulAut W11)) : Set (MulAut W11))) ≃+*
        Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  haveI := mb2Model4.finite_commutant
  haveI := mb2Model4.nontrivial_commutant (by norm_num : 0 < 6)
  have h := exists_matrix2_of_data (mb2Model4.matrix2Data mb2E4 mb2c4_lenE mb2c4_ltE mb2c4_commE
    mb2c4_mulE mb2c4_sumE [1] mb2W4 mb2c4_hW mb2c4_count)
  rwa [genGroup_mb2Gens4] at h

end CFSG.Quasithin.H13.Mat
