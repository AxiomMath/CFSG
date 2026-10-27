module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2C
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR2S

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.Quasithin.H.Code22 CFSG.Quasithin.E3
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.L828T CFSG.Quasithin.H13.Mat.MB2C

@[expose] def mb2LC2 : List ℕ := [1, 148, 944, 337, 444]

@[expose] noncomputable def mb2Gens2 : List (MulAut W10) :=
  [rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩, rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩]

@[expose] def mb2Cols2 : List (List ℕ) := [hbACols, hbBCols]

@[expose] def mb2Ms2 : List (List ℕ) := [[2, 8, 16, 1, 31], [4, 11, 1, 13, 16]]

@[expose] def mb2W2 : List (List (ℕ × List ℕ)) :=
  [[(0, [])], [(0, [0])], [(0, [1])], [(0, [0, 0])], [(0, [0, 1])]]

private theorem rhoA_act_mb2r2 :
    ActsBy (n := 10) (rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩) hbACols :=
  actsBy_rho_arr hbA_mem hasArr_hbA hbCols_eq.1

private theorem rhoB_act_mb2r2 :
    ActsBy (n := 10) (rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩) hbBCols :=
  actsBy_rho_arr hbB_mem hasArr_hbB hbCols_eq.2.1

private theorem rhoA_mem_mb2r2 :
    rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩ ∈ imgC hbQ :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbA_mem_Q)

private theorem rhoB_mem_mb2r2 :
    rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩ ∈ imgC hbQ :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbB_mem_Q)

private theorem hbQ_rho_mem_mb2r2 : ∀ τ ∈ hbQ, ∀ h : τ ∈ mog22,
    rhoC10 mog22 mog22_le_mog22plus ⟨τ, h⟩ ∈ Subgroup.closure
      ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
        rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)) := by
  intro τ hτ
  change τ ∈ Subgroup.closure ({hbA, hbB} : Set (Equiv.Perm (Fin 24))) at hτ
  induction hτ using Subgroup.closure_induction with
  | mem x hx =>
    intro h
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  | one =>
    intro h
    have e : (⟨(1 : Equiv.Perm (Fin 24)), h⟩ : ↥mog22) = 1 := rfl
    rw [e, map_one]
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    intro h
    have hx' : x ∈ mog22 := hbQ_le hx
    have hy' : y ∈ mog22 := hbQ_le hy
    have e : (⟨x * y, h⟩ : ↥mog22) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := Subtype.ext rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (ihx hx') (ihy hy')
  | inv x hx ihx =>
    intro h
    have hx' : x ∈ mog22 := hbQ_le hx
    have e : (⟨x⁻¹, h⟩ : ↥mog22) = (⟨x, hx'⟩ : ↥mog22)⁻¹ := Subtype.ext rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ (ihx hx')

private theorem imgC_hbQ_eq_mb2r2 : imgC hbQ = Subgroup.closure
    ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
      rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)) := by
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hbQ_rho_mem_mb2r2 _ (Subgroup.mem_subgroupOf.1 hσ) σ.2
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl)
    · exact rhoA_mem_mb2r2
    · exact rhoB_mem_mb2r2

theorem mb2c2_data :
    MaskCoordsData (MaskCoords.std 10) (maskSub 10 mb2B9) UC 5 mb2B9 hbU0Basis mb2LC2 :=
  MaskCoordsData.std mb2B9_lt hbU0Basis_lt (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel)

theorem genGroup_mb2Gens2 : genGroup mb2Gens2 = imgC hbQ := by
  rw [imgC_hbQ_eq_mb2r2]
  exact genGroup_two _ _

theorem mb2c2_hgens : ∀ i < mb2Gens2.length, ∀ m,
    mb2Gens2.getD i 1 ((MaskCoords.std 10).vm m) =
      (MaskCoords.std 10).vm (actM (mb2Cols2.getD i []) m) :=
  hgens_two rhoA_act_mb2r2 rhoB_act_mb2r2

theorem mb2c2_check : ∀ i < 2, ∀ j < 5,
    (actM (mb2Cols2.getD i []) (actM mb2LC2 (2 ^ j)) ^^^
      actM mb2LC2 (actM (mb2Ms2.getD i []) (2 ^ j))) ∈ combos hbU0Basis := by
  decide +kernel

theorem mb2c2_lenM : ∀ M ∈ mb2Ms2, M.length = 5 := by decide +kernel

theorem mb2c2_ltM : ∀ M ∈ mb2Ms2, ∀ x ∈ M, x < 2 ^ 5 := by decide +kernel

theorem mb2c2_invB :
    ∀ g ∈ genGroup mb2Gens2, ∀ b ∈ maskSub 10 mb2B9, g b ∈ maskSub 10 mb2B9 := by
  rw [genGroup_mb2Gens2]
  exact invariant_of_commV_le_mat std2_commP_le_B9

theorem mb2c2_invU : ∀ g ∈ genGroup mb2Gens2, ∀ u ∈ UC, g u ∈ UC := by
  rw [genGroup_mb2Gens2]
  exact fun g hg u hu => ((imgC_hbQ_le hg).2 u).2 hu

@[expose] noncomputable def mb2Model2 : MB2Model 5 (maskSub 10 mb2B9) UC mb2Gens2 :=
  MB2Model.ofMasks mb2c2_data mb2Gens2 mb2Cols2 mb2Ms2 mb2c2_hgens rfl mb2c2_lenM mb2c2_ltM
    mb2c2_check mb2c2_invB mb2c2_invU

private theorem mb2c2_hW : ∀ j < 5, algAct mb2Ms2 (mb2W2.getD j []) [1] = 2 ^ j := by
  decide +kernel

private theorem mb2c2_count :
    ((tuples 5 [1].length).filter (commCheck mb2Ms2 mb2W2 5)).length ≤ 2 := by
  decide +kernel

theorem mb2_std_row2 :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (↥(commutant (maskSub 10 mb2B9) UC
        ((imgC hbQ : Subgroup (MulAut W10)) : Set (MulAut W10))) ≃+* K) := by
  have h := mb2Model2.exists_field2 (by norm_num : 0 < 5) [1] mb2W2 mb2c2_hW mb2c2_count
  rwa [genGroup_mb2Gens2] at h

end CFSG.Quasithin.H13.Mat
