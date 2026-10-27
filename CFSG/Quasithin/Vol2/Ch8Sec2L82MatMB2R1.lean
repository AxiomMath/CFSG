module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2C
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR1

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.L34Z CFSG.Quasithin.H.Coc CFSG.Quasithin.H13 CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H13.L828T CFSG.Quasithin.H13.Mat.MB2C

@[expose] def mb2LC1 : List ℕ := [258, 96, 65, 448]

@[expose] noncomputable def mb2Gens1 : List (MulAut W9) := [rho9 x2G, rho9 y2G]

@[expose] def mb2Cols1 : List (List ℕ) := [colsX2, colsY2]

@[expose] def mb2Ms1 : List (List ℕ) := [[2, 1, 13, 11], [4, 8, 7, 5]]

@[expose] def mb2A1 : List ℕ := [12, 6, 2, 15]

@[expose] def mb2W1 : List (List (ℕ × List ℕ)) :=
  [[(0, [])], [(0, [0])], [(0, [1])], [(0, [1, 0])]]

theorem mb2c1_data :
    MaskCoordsData (MaskCoords.std 9) (maskSub 9 mbL8_mb) U0 4 mbL8_mb U0Basis mb2LC1 :=
  MaskCoordsData.std mbL8_mb_lt U0Basis_lt (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel)

theorem genGroup_mb2Gens1 : genGroup mb2Gens1 = P2 :=
  genGroup_two _ _

theorem mb2c1_hgens : ∀ i < mb2Gens1.length, ∀ m,
    mb2Gens1.getD i 1 ((MaskCoords.std 9).vm m) =
      (MaskCoords.std 9).vm (actM (mb2Cols1.getD i []) m) :=
  hgens_two actsBy_rho9_x2 actsBy_rho9_y2

theorem mb2c1_check : ∀ i < 2, ∀ j < 4,
    (actM (mb2Cols1.getD i []) (actM mb2LC1 (2 ^ j)) ^^^
      actM mb2LC1 (actM (mb2Ms1.getD i []) (2 ^ j))) ∈ combos U0Basis := by
  decide +kernel

theorem mb2c1_lenM : ∀ M ∈ mb2Ms1, M.length = 4 := by decide +kernel

theorem mb2c1_ltM : ∀ M ∈ mb2Ms1, ∀ x ∈ M, x < 2 ^ 4 := by decide +kernel

theorem mb2c1_invB :
    ∀ g ∈ genGroup mb2Gens1, ∀ b ∈ maskSub 9 mbL8_mb, g b ∈ maskSub 9 mbL8_mb := by
  rw [genGroup_mb2Gens1]
  exact invariant_of_commV_le_mat commP_le_mb

theorem mb2c1_invU : ∀ g ∈ genGroup mb2Gens1, ∀ u ∈ U0, g u ∈ U0 := by
  rw [genGroup_mb2Gens1]
  exact fun g hg u hu => ((P2_le hg).2 u).2 hu

@[expose] noncomputable def mb2Model1 : MB2Model 4 (maskSub 9 mbL8_mb) U0 mb2Gens1 :=
  MB2Model.ofMasks mb2c1_data mb2Gens1 mb2Cols1 mb2Ms1 mb2c1_hgens rfl mb2c1_lenM mb2c1_ltM
    mb2c1_check mb2c1_invB mb2c1_invU

private theorem mb2c1_ltA : ∀ x ∈ mb2A1, x < 2 ^ 4 := by decide +kernel

private theorem mb2c1_commA : ∀ i < 2, ∀ m < 2 ^ 4,
    actM (mb2Ms1.getD i []) (actM mb2A1 m) = actM mb2A1 (actM (mb2Ms1.getD i []) m) := by
  decide +kernel

private theorem mb2c1_rootA :
    ∀ m < 2 ^ 4, actM mb2A1 (actM mb2A1 m) ^^^ actM mb2A1 m ^^^ m = 0 := by
  decide +kernel

private theorem mb2c1_hW : ∀ j < 4, algAct mb2Ms1 (mb2W1.getD j []) [1] = 2 ^ j := by
  decide +kernel

private theorem mb2c1_count :
    ((tuples 4 [1].length).filter (commCheck mb2Ms1 mb2W1 4)).length ≤ 4 := by
  decide +kernel

theorem mb2_std_row1 :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥(commutant (maskSub 9 mbL8_mb) U0
        ((P2 : Subgroup (MulAut W9)) : Set (MulAut W9))) ≃+* K) := by
  haveI := mb2Model1.finite_commutant
  haveI := mb2Model1.nontrivial_commutant (by norm_num : 0 < 4)
  have h := exists_field4_of_data (mb2Model1.field4Data (MA := mb2A1) rfl mb2c1_ltA mb2c1_commA
    mb2c1_rootA [1] mb2W1 mb2c1_hW mb2c1_count)
  rwa [genGroup_mb2Gens1] at h

end CFSG.Quasithin.H13.Mat
