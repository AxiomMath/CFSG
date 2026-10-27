module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2C
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR3S

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.Quasithin.H.LU24
  CFSG.Quasithin.E3 CFSG.Quasithin.H13 CFSG.Quasithin.H13.L828T CFSG.Quasithin.H13.Mat.MB2C

@[expose] def mb2LC3 : List ℕ := [948, 1572, 82, 1562, 568, 143]

@[expose] noncomputable def mb2Gens3 : List (MulAut W11) := [rhoCd sxG1_mem, rhoCd sxG2_mem]

@[expose] def mb2Cols3 : List (List ℕ) := [sxG1C, sxG2C]

@[expose] def mb2Ms3 : List (List ℕ) :=
  [[46, 9, 44, 32, 35, 55], [8, 23, 54, 10, 56, 26]]

@[expose] def mb2A3 : List ℕ := [61, 15, 41, 22, 56, 6]

@[expose] def mb2W3 : List (List (ℕ × List ℕ)) :=
  [[(0, [])], [(0, []), (0, [0, 0]), (0, [1, 0])],
    [(0, []), (0, [0]), (0, [1]), (0, [0, 0]), (0, [1, 0]), (0, [0, 1])], [(0, [1])],
    [(0, []), (0, [1, 0]), (0, [0, 1])], [(0, [0, 1])]]

theorem mb2c3_data :
    MaskCoordsData (MaskCoords.std 11) (maskSub 11 mb3L10) US 6 mb3L10 uSBasis mb2LC3 :=
  MaskCoordsData.std mb3L10_lt uSBasis_lt (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel)

theorem genGroup_mb2Gens3 : genGroup mb2Gens3 = imgCd sxP0 := by
  rw [imgCd_P0_eq_r3s]
  exact genGroup_two _ _

theorem mb2c3_hgens : ∀ i < mb2Gens3.length, ∀ m,
    mb2Gens3.getD i 1 ((MaskCoords.std 11).vm m) =
      (MaskCoords.std 11).vm (actM (mb2Cols3.getD i []) m) :=
  hgens_two actsBy_sxG1 actsBy_sxG2

theorem mb2c3_check : ∀ i < 2, ∀ j < 6,
    (actM (mb2Cols3.getD i []) (actM mb2LC3 (2 ^ j)) ^^^
      actM mb2LC3 (actM (mb2Ms3.getD i []) (2 ^ j))) ∈ combos uSBasis := by
  decide +kernel

theorem mb2c3_lenM : ∀ M ∈ mb2Ms3, M.length = 6 := by decide +kernel

theorem mb2c3_ltM : ∀ M ∈ mb2Ms3, ∀ x ∈ M, x < 2 ^ 6 := by decide +kernel

theorem mb2c3_invB :
    ∀ g ∈ genGroup mb2Gens3, ∀ b ∈ maskSub 11 mb3L10, g b ∈ maskSub 11 mb3L10 := by
  rw [genGroup_mb2Gens3]
  refine invariant_of_commV_le_mat ?_
  exact (le_sup_left : commV (imgCd sxP0) ≤ commV (imgCd sxP0) ⊔ US).trans
    (le_of_eq std3_commV_sup)

theorem mb2c3_invU : ∀ g ∈ genGroup mb2Gens3, ∀ u ∈ US, g u ∈ US := by
  rw [genGroup_mb2Gens3]
  exact fun g hg u hu => ((imgCd_P0_le_stab hg) u).2 hu

@[expose] noncomputable def mb2Model3 : MB2Model 6 (maskSub 11 mb3L10) US mb2Gens3 :=
  MB2Model.ofMasks mb2c3_data mb2Gens3 mb2Cols3 mb2Ms3 mb2c3_hgens rfl mb2c3_lenM mb2c3_ltM
    mb2c3_check mb2c3_invB mb2c3_invU

private theorem mb2c3_ltA : ∀ x ∈ mb2A3, x < 2 ^ 6 := by decide +kernel

private theorem mb2c3_commA : ∀ i < 2, ∀ m < 2 ^ 6,
    actM (mb2Ms3.getD i []) (actM mb2A3 m) = actM mb2A3 (actM (mb2Ms3.getD i []) m) := by
  decide +kernel

private theorem mb2c3_rootA :
    ∀ m < 2 ^ 6, actM mb2A3 (actM mb2A3 m) ^^^ actM mb2A3 m ^^^ m = 0 := by
  decide +kernel

private theorem mb2c3_hW : ∀ j < 6, algAct mb2Ms3 (mb2W3.getD j []) [1] = 2 ^ j := by
  decide +kernel

private theorem mb2c3_count :
    ((tuples 6 [1].length).filter (commCheck mb2Ms3 mb2W3 6)).length ≤ 4 := by
  decide +kernel

theorem mb2_std_row3 :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥(commutant (maskSub 11 mb3L10) US
        ((imgCd sxP0 : Subgroup (MulAut W11)) : Set (MulAut W11))) ≃+* K) := by
  haveI := mb2Model3.finite_commutant
  haveI := mb2Model3.nontrivial_commutant (by norm_num : 0 < 6)
  have h := exists_field4_of_data (mb2Model3.field4Data (MA := mb2A3) rfl mb2c3_ltA mb2c3_commA
    mb2c3_rootA [1] mb2W3 mb2c3_hW mb2c3_count)
  rwa [genGroup_mb2Gens3] at h

end CFSG.Quasithin.H13.Mat
