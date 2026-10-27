module

public import CFSG.Quasithin.Background.HB82L34Gen
public import CFSG.Quasithin.Background.HZL34B
public import CFSG.Quasithin.Background.HB82Base

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Open CFSG.Fischer Matrix CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H13.Ch9.L34M
open scoped commutatorElement

abbrev U0 : Subgroup W9 := maskSub 9 U0Basis

theorem maps_U0 {g : MulAut W9} {c : List ℕ} (hg : ∀ m < 512, g (toW 9 m) = toW 9 (actM c m))
    (hf : ∀ m ∈ combos U0Basis, actM c m ∈ combos U0Basis) : ∀ u ∈ U0, g u ∈ U0 := by
  rintro _ ⟨m, hm, rfl⟩
  have hm' : m < 512 := lt_of_lt_of_eq (combos_lt U0Basis_lt _ hm) (by norm_num)
  rw [hg m hm']
  exact toW_mem_maskSub (hf m hm)

@[expose] def x2G : GL (Fin 3) F4 := glOf x2M x2Mi x2_inv

@[expose] def y2G : GL (Fin 3) F4 := glOf y2M y2Mi y2_inv

@[expose] noncomputable def P2 : Subgroup (MulAut W9) := Subgroup.closure {rho9 x2G, rho9 y2G}

theorem x2_mem_P2 : rho9 x2G ∈ P2 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem y2_mem_P2 : rho9 y2G ∈ P2 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem rho9_x2_mem_stabSub : rho9 x2G ∈ stabSub U0 := by
  have hinv : ∀ m < 512, (rho9 x2G)⁻¹ (toW 9 m) = toW 9 (actM colsX2i m) := fun m hm => by
    rw [← map_inv]
    exact rho9_toW_cols x2G⁻¹ cols_x2.2.2.1 hm
  exact mem_stabSub_of_maps (maps_U0 (c := colsX2) (fun m hm => rho9_toW_cols x2G cols_x2.1 hm)
    (fun m hm => (l2_pres m hm).1)) (maps_U0 (c := colsX2i) hinv
    (fun m hm => (l2_pres m hm).2.2.1))

theorem rho9_y2_mem_stabSub : rho9 y2G ∈ stabSub U0 := by
  have hinv : ∀ m < 512, (rho9 y2G)⁻¹ (toW 9 m) = toW 9 (actM colsY2i m) := fun m hm => by
    rw [← map_inv]
    exact rho9_toW_cols y2G⁻¹ cols_x2.2.2.2 hm
  exact mem_stabSub_of_maps (maps_U0 (c := colsY2)
    (fun m hm => rho9_toW_cols y2G cols_x2.2.1 hm) (fun m hm => (l2_pres m hm).2.1))
    (maps_U0 (c := colsY2i) hinv (fun m hm => (l2_pres m hm).2.2.2))

theorem P2_le : P2 ≤ img9 ⊓ stabSub U0 := by
  refine (Subgroup.closure_le (img9 ⊓ stabSub U0)).2 ?_
  rintro _ (rfl | rfl)
  · exact ⟨rho9_mem_img9 det_x2M, rho9_x2_mem_stabSub⟩
  · exact ⟨rho9_mem_img9 det_y2M, rho9_y2_mem_stabSub⟩

@[expose] def c0G2 : GL (Fin 3) F4 := ⁅x2G, y2G⁆

@[expose] def c2G2 : GL (Fin 3) F4 := ⁅x2G, y2G * y2G⁆

theorem coe_c0G2 : (c0G2 : Matrix (Fin 3) (Fin 3) F4) = c0M2 := by
  show ((x2G * y2G * x2G⁻¹ * y2G⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = _
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  rfl

theorem coe_c2G2 : (c2G2 : Matrix (Fin 3) (Fin 3) F4) = c2M2 := by
  show ((x2G * (y2G * y2G) * x2G⁻¹ * (y2G * y2G)⁻¹ : GL (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) F4) = _
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, _root_.mul_inv_rev,
    Units.val_mul]
  rfl

theorem coe_c02_2 : ([c0G2, c2G2].map Units.val) = [c0M2, c2M2] := by
  rw [List.map_cons, List.map_cons, List.map_nil, coe_c0G2, coe_c2G2]

theorem commutator_P2 : ⁅P2, P2⁆ = P2 := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact P2.mul_mem (P2.mul_mem (P2.mul_mem ha hb) (P2.inv_mem ha)) (P2.inv_mem hb)) ?_
  have hc : ∀ g ∈ [c0G2, c2G2], rho9 g ∈ ⁅P2, P2⁆ := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [c0G2, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator x2_mem_P2 y2_mem_P2
    · rw [c2G2, map_commutatorElement, map_mul]
      exact Subgroup.commutator_mem_commutator x2_mem_P2 (P2.mul_mem y2_mem_P2 y2_mem_P2)
  show Subgroup.closure ({rho9 x2G, rho9 y2G} : Set (MulAut W9)) ≤ ⁅P2, P2⁆
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have hx : cols ((wGL [c0G2, c2G2] xWord2 : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        colsX2 := (congrArg cols (coe_wGL [c0G2, c2G2] xWord2)).trans
          ((congrArg (fun l => cols (wM l xWord2)) coe_c02_2).trans perfect2_words.1)
    have e : rho9 x2G = rho9 (wGL [c0G2, c2G2] xWord2) := rho9_eq_of_cols (cols_x2.1.trans hx.symm)
    rw [e]
    exact rho9_wGL_mem hc xWord2
  · have hy : cols ((wGL [c0G2, c2G2] yWord2 : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        colsY2 := (congrArg cols (coe_wGL [c0G2, c2G2] yWord2)).trans
          ((congrArg (fun l => cols (wM l yWord2)) coe_c02_2).trans perfect2_words.2)
    have e : rho9 y2G = rho9 (wGL [c0G2, c2G2] yWord2) :=
      rho9_eq_of_cols (cols_x2.2.1.trans hy.symm)
    rw [e]
    exact rho9_wGL_mem hc yWord2

theorem Rbar_le_U0 : Rbar ≤ img9 ⊓ stabSub U0 := by
  intro φ hφ
  obtain ⟨t, ht, rfl⟩ := mem_Rbar.1 hφ
  have hinv : ∀ m < 512, (rho9 (uG t))⁻¹ (toW 9 m) = toW 9 (actM (colsU.getD t []) m) :=
    fun m hm => by
      rw [← map_inv, show (uG t)⁻¹ = uG t from Units.ext rfl]
      exact rho9_uG_toW ht hm
  exact ⟨(Rbar_le_L34.trans L34_le_img9) hφ, mem_stabSub_of_maps
    (maps_U0 (c := colsU.getD t []) (fun m hm => rho9_uG_toW ht hm) (u_pres t ht))
    (maps_U0 (c := colsU.getD t []) hinv (u_pres t ht))⟩

theorem toW_mem_commV_P2 {m : ℕ}
    (hm : m ∈ combos (cvData2.map fun e => lAct2 e.1 (2 ^ e.2) ^^^ 2 ^ e.2)) :
    toW 9 m ∈ commV P2 := by
  refine mem_of_combos (fun m => toW 9 m ∈ commV P2) ?_ ?_ _ ?_ m hm
  · rw [toW_zero]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    obtain ⟨⟨g, j⟩, hgj, rfl⟩ := List.mem_map.1 ha
    have hj : 2 ^ j < 512 :=
      lt_of_lt_of_eq (Nat.pow_lt_pow_right (by norm_num) (cvData2_lt _ hgj)) (by norm_num)
    by_cases hg : g = 0
    · have h := mem_commV x2_mem_P2 (toW 9 (2 ^ j))
      have e1 : toW 9 (lAct2 g (2 ^ j) ^^^ 2 ^ j) =
          rho9 x2G (toW 9 (2 ^ j)) * (toW 9 (2 ^ j))⁻¹ := by
        rw [rho9_toW_cols x2G cols_x2.1 hj, toW_inv, toW_xor, lAct2, ite_eq_left hg]
      show toW 9 (lAct2 g (2 ^ j) ^^^ 2 ^ j) ∈ _
      rw [e1]
      exact h
    · have h := mem_commV y2_mem_P2 (toW 9 (2 ^ j))
      have e1 : toW 9 (lAct2 g (2 ^ j) ^^^ 2 ^ j) =
          rho9 y2G (toW 9 (2 ^ j)) * (toW 9 (2 ^ j))⁻¹ := by
        rw [rho9_toW_cols y2G cols_x2.2.1 hj, toW_inv, toW_xor, lAct2, ite_eq_right hg]
      show toW 9 (lAct2 g (2 ^ j) ^^^ 2 ^ j) ∈ _
      rw [e1]
      exact h

theorem W0_le_commV_P2 : W0 ≤ commV P2 := by
  rintro _ ⟨m, hm, rfl⟩
  refine mem_of_combos (fun m => toW 9 m ∈ commV P2) ?_ ?_ w0Basis ?_ m hm
  · rw [toW_zero]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor]
    exact Subgroup.mul_mem _ ha hb
  · intro a ha
    exact toW_mem_commV_P2 (w0_in_cv2 a ha)

theorem not_W0_le_U0 : ¬ W0 ≤ U0 := by
  intro h
  obtain ⟨m, hm, he⟩ := h (toW_mem_maskSub w0_notin.1)
  have hlt : m < 2 ^ 9 := combos_lt U0Basis_lt _ hm
  have e := toW_inj hlt (by norm_num) he
  rw [e] at hm
  exact w0_notin.2 hm

theorem hbConcl_std {X : Subgroup (MulAut W9)} (hX : fixV X = U0)
    {z : W9} (hz1 : z ≠ 1) {S : Subgroup (MulAut W9)} (hSH : S ≤ img9 ⊓ stabSub U0)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥img9).factorization 2) (hzS : z ∈ fixV S) :
    HBConcl img9 X z :=
  hbConcl_of_std Rbar_le_U0 isPGroup_Rbar fix_Rbar P2_le commutator_P2
    ((le_of_eq vZ_std).trans W0_le_commV_P2) (fun h => not_W0_le_U0 (vZ_std ▸ h)) hX hz1 hSH
    hS hzS

end CFSG.Quasithin.H.L34Z
