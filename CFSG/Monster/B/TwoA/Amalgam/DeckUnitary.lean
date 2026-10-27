module

public import CFSG.Monster.B.TwoA.Amalgam.DeckData
public import CFSG.Monster.B.Classical.UnitaryPanels

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary Module
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Monster.B.Classical.UnitaryPanels

abbrev B6 : V6 →ₛₗ[hF4.bar] V6 →ₗ[CFSG.Fischer.F4] CFSG.Fischer.F4 := gramForm hF4 hGram

theorem gramForm_hGram_apply (x y : V6) : B6 x y = hU y x := by
  rw [gramForm_apply, hU_eq_dotProduct, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    hGram_transpose, dotProduct_comm]
  congr 2

theorem B6_isSymm : B6.IsSymm := gramForm_isSymm hF4 hGram_hermitian

theorem B6_separatingLeft : B6.SeparatingLeft := gramForm_separatingLeft hF4 det_hGram_ne_zero

theorem finrank_V6 : finrank CFSG.Fischer.F4 V6 = 6 := Module.finrank_fin_fun _

theorem exists_SUh_of_mem {g : LinearMap.GeneralLinearGroup CFSG.Fischer.F4 V6}
    (hg : g ∈ sesqSpecialUnitaryGroup B6) :
    ∃ N : SUh, ∀ X : Submodule CFSG.Fischer.F4 V6,
      sigmaAct X (suElt N) = X.map (g : V6 →ₗ[CFSG.Fischer.F4] V6) := by
  set gM : GL (Fin 6) CFSG.Fischer.F4 := Matrix.GeneralLinearGroup.toLin.symm g with hgM
  have hg' : Matrix.GeneralLinearGroup.toLin gM = g := MulEquiv.apply_symm_apply _ g
  have hmem : gM ∈ gramSU hF4 hGram := by
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, hg']
    exact hg
  have hN : trGL gM ∈ SUh := by
    rw [mem_SUh_iff_trGL, trGL_trGL]
    exact hmem
  refine ⟨⟨trGL gM, hN⟩, fun X => ?_⟩
  rw [sigmaAct_suElt, subMul]
  congr 1
  refine LinearMap.ext fun v => ?_
  rw [Matrix.vecMulLinear_apply]
  change Matrix.vecMul v (gM : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4).transpose = _
  rw [Matrix.vecMul_transpose, ← hg', Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]

theorem suElt_mem_psuSub (N : SUh) : suElt N ∈ psuSub := ⟨(N : SUh ⧸ Zh), rfl⟩

theorem Rsp_lt_Hsp : Rsp < Hsp :=
  lt_of_le_of_ne Rsp_le_Hsp fun h => by
    have := congrArg (fun S : Submodule CFSG.Fischer.F4 V6 => finrank CFSG.Fischer.F4 S) h
    simp only [finrank_Rsp, finrank_Hsp] at this
    omega

theorem Hsp_lt_Tsp : Hsp < Tsp :=
  lt_of_le_of_ne Hsp_le_Tsp fun h => by
    have := congrArg (fun S : Submodule CFSG.Fischer.F4 V6 => finrank CFSG.Fischer.F4 S) h
    simp only [finrank_Hsp, uIso_Tsp.1] at this
    omega

theorem B6_Tsp :
    ∀ x ∈ Tsp, ∀ y ∈ Tsp, B6 x y = 0 := fun x hx y hy => by
  rw [gramForm_hGram_apply]
  exact uIso_Tsp.2 y hy x hx

theorem exists_psu_of_psuFlagStabilizer {X Y : Submodule CFSG.Fischer.F4 V6}
    {u : sesqSpecialUnitaryGroup B6 ⧸ Subgroup.center (sesqSpecialUnitaryGroup B6)}
    (hu : u ∈ psuFlagStabilizer hF4 B6_isSymm B6_separatingLeft finrank_V6 Rsp Hsp Tsp)
    (huX : psuSubspaceAction hF4 B6_isSymm B6_separatingLeft finrank_V6 u X = Y) :
    ∃ x ∈ psuSub ⊓ flagStabU, sigmaAct X x = Y := by
  obtain ⟨g, hg, hact, hR, hH, hT⟩ := exists_rep_of_mem_psuFlagStabilizer hF4 B6_isSymm
    B6_separatingLeft finrank_V6 hu
  obtain ⟨N, hN⟩ := exists_SUh_of_mem hg
  refine ⟨suElt N, ⟨suElt_mem_psuSub N, ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
  · change sigmaAct Rsp (suElt N) = Rsp
    rw [hN, hR]
  · change sigmaAct Hsp (suElt N) = Hsp
    rw [hN, hH]
  · change sigmaAct Tsp (suElt N) = Tsp
    rw [hN, hT]
  · rw [hN, ← hact, huX]

theorem exists_psu_flag_moves {X : Submodule CFSG.Fischer.F4 V6}
    (hX : (finrank CFSG.Fischer.F4 X = 1 ∧ X < Hsp ∧ X ≠ Rsp) ∨
      (Rsp < X ∧ X < Tsp ∧ finrank CFSG.Fischer.F4 X = 2 ∧ X ≠ Hsp) ∨
      (Hsp < X ∧ UIso 3 X ∧ X ≠ Tsp)) :
    ∃ x ∈ psuSub ⊓ flagStabU, sigmaAct X x ≠ X := by
  obtain ⟨-, ⟨hR4, -, hRtr⟩, ⟨hH4, -, hHtr⟩, ⟨hT2, -, hTtr⟩⟩ :=
    unitary_six_derived_flag_panel_actions hF4 B6_isSymm B6_separatingLeft finrank_V6
      Rsp_lt_Hsp Hsp_lt_Tsp finrank_Rsp finrank_Hsp uIso_Tsp.1 B6_Tsp
  rcases hX with hX | hX | ⟨hX1, hX2, hX3⟩
  · obtain ⟨Y, hY, hYX⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hR4]; norm_num) X
    obtain ⟨u, hu, huX⟩ := hRtr X hX Y hY
    obtain ⟨x, hx, hxX⟩ := exists_psu_of_psuFlagStabilizer hu huX
    exact ⟨x, hx, hxX ▸ hYX⟩
  · obtain ⟨Y, hY, hYX⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hH4]; norm_num) X
    obtain ⟨u, hu, huX⟩ := hHtr X hX Y hY
    obtain ⟨x, hx, hxX⟩ := exists_psu_of_psuFlagStabilizer hu huX
    exact ⟨x, hx, hxX ▸ hYX⟩
  · have hXT : X ∈ {T' : Submodule CFSG.Fischer.F4 V6 | Hsp < T' ∧
        finrank CFSG.Fischer.F4 T' = 3 ∧ (∀ x ∈ T', ∀ y ∈ T', B6 x y = 0) ∧ T' ≠ Tsp} :=
      ⟨hX1, hX2.1, fun x hx y hy => by rw [gramForm_hGram_apply]; exact hX2.2 y hy x hx, hX3⟩
    obtain ⟨Y, hY, hYX⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hT2]; norm_num) X
    obtain ⟨u, hu, huX⟩ := hTtr X hXT Y hY
    obtain ⟨x, hx, hxX⟩ := exists_psu_of_psuFlagStabilizer hu huX
    exact ⟨x, hx, hxX ▸ hYX⟩

end CFSG.Monster.B.TwoA.Amalgam
