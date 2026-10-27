module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Main
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6LSideCert
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelF4
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortSp
public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelGen

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide

open Subgroup CFSG.SeitzReduction.F4Pilot CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Chevalley (finiteExceptionalAut_pinnedX_long finiteExceptionalAut_pinnedX_short)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Open
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

local instance lsNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance lsNeZeroRankReeF4 : NeZero ReeTag.F4.tag.rank := ⟨by decide⟩

theorem f4_nodes_zero_three_check :
    ReeTag.F4.quadForm (Pi.single 3 1 : Fin Tag.F4.rank → ℤ) = 2 ∧
      ReeTag.F4.quadForm (-Pi.single 3 1 : Fin Tag.F4.rank → ℤ) = 2 ∧
      ReeTag.F4.dualRoot (Pi.single 3 1 : Fin Tag.F4.rank → ℤ) = Pi.single 0 1 ∧
      ReeTag.F4.dualRoot (-Pi.single 3 1 : Fin Tag.F4.rank → ℤ) = -Pi.single 0 1 := by
  decide +kernel

section Par


variable {K : Type} [Field K] [CharP K 2]

variable
  [Finite K]

theorem c3LeviEquiv_x_single_zero (c : K) :
    ((c3LeviEquiv K (Sp.x 3 K (Pi.single 0 1) c) : C3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (Pi.single 3 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  rw [c3LeviEquiv_x, c3ToF4_single, f4Par_eq_pinnedX_charTwo (isRoot_single _ _)]
  rfl

theorem c3LeviEquiv_x_neg_single_zero (c : K) :
    ((c3LeviEquiv K (Sp.x 3 K (-Pi.single 0 1) c) : C3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (-Pi.single 3 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  rw [c3LeviEquiv_x, map_neg, c3ToF4_single, f4Par_eq_pinnedX_charTwo (isRoot_neg_single _ _)]
  rfl

end Par

section Graph


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem graphAutF4_pinnedX_single_three (c : K) :
    graphAutF4 K ⟨pinnedX .F4 K (Pi.single 3 1) c, pinnedX_mem_adjointGroup _ c⟩ =
      ⟨pinnedX .F4 K (Pi.single 0 1) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have hs : (Pi.single 3 1 : Fin Tag.F4.rank → ℤ) ∈ ReeTag.F4.shortRoots :=
    ⟨isRoot_single _ _, ReeTag.lengthParam_eq_one_iff.2 f4_nodes_zero_three_check.1⟩
  have e := finiteExceptionalAut_pinnedX_short (K := K) hs c
  rw [f4_nodes_zero_three_check.2.2.1] at e
  exact e

theorem graphAutF4_pinnedX_neg_single_three (c : K) :
    graphAutF4 K ⟨pinnedX .F4 K (-Pi.single 3 1) c, pinnedX_mem_adjointGroup _ c⟩ =
      ⟨pinnedX .F4 K (-Pi.single 0 1) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have hs : (-Pi.single 3 1 : Fin Tag.F4.rank → ℤ) ∈ ReeTag.F4.shortRoots :=
    ⟨isRoot_neg_single _ _, ReeTag.lengthParam_eq_one_iff.2 f4_nodes_zero_three_check.2.1⟩
  have e := finiteExceptionalAut_pinnedX_short (K := K) hs c
  rw [f4_nodes_zero_three_check.2.2.2] at e
  exact e

end Graph

section B3


variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
noncomputable def lsB3Equiv : ↥(StatedSp 3 K) ≃* ↥(B3Levi K) :=
  (c3LeviEquiv K).trans (c3LeviEquivB3Levi K)

theorem coe_lsB3Equiv (g : StatedSp 3 K) :
    ((lsB3Equiv K g : B3Levi K) : adjointGroup .F4 K) =
      graphAutF4 K ((c3LeviEquiv K g : C3Levi K) : adjointGroup .F4 K) := rfl

theorem lsB3Equiv_x_single_zero (c : K) :
    ((lsB3Equiv K (Sp.x 3 K (Pi.single 0 1) c) : B3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (Pi.single 0 1) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have h := graphAutF4_pinnedX_single_three (K := K) c
  rw [coe_lsB3Equiv, c3LeviEquiv_x_single_zero, h]

theorem lsB3Equiv_x_neg_single_zero (c : K) :
    ((lsB3Equiv K (Sp.x 3 K (-Pi.single 0 1) c) : B3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (-Pi.single 0 1) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have h := graphAutF4_pinnedX_neg_single_three (K := K) c
  rw [coe_lsB3Equiv, c3LeviEquiv_x_neg_single_zero, h]

theorem lsB3Equiv_x_single_two (c : K) :
    ((lsB3Equiv K (Sp.x 3 K (Pi.single 2 1) c) : B3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (Pi.single 2 1) c, pinnedX_mem_adjointGroup _ _⟩ := by
  have h := graphAutF4_pinnedX_single_one (K := K) c
  rw [coe_lsB3Equiv, c3LeviEquiv_x_single_two, h]

theorem lsB3Equiv_x_neg_single_two (c : K) :
    ((lsB3Equiv K (Sp.x 3 K (-Pi.single 2 1) c) : B3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (-Pi.single 2 1) c, pinnedX_mem_adjointGroup _ _⟩ := by
  have h := graphAutF4_pinnedX_neg_single_one (K := K) c
  rw [coe_lsB3Equiv, c3LeviEquiv_x_neg_single_two, h]

end B3

section Matrices

open CFSG.ClassicalInvolution.Balance (x_simple_fst x_simple_snd simpleIdx)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt mat_elt mat_apply)

theorem mat6_x_simple_zero_fst :
    mat6 (Sp.x 3 (ZMod 2) (Pi.single 0 1) 1) = dec6 lsX0p := by
  rw [x_simple_fst, mat6_apply]
  have h := mat_elt (n := 3) (simpleIdx (0 : Fin 3)).1 (1 : ZMod 2)
  rw [mat_apply] at h
  rw [h]
  decide +kernel

theorem mat6_x_simple_zero_snd :
    mat6 (Sp.x 3 (ZMod 2) (-Pi.single 0 1) 1) = dec6 lsX0m := by
  rw [x_simple_snd, mat6_apply]
  have h := mat_elt (n := 3) (simpleIdx (0 : Fin 3)).2 (1 : ZMod 2)
  rw [mat_apply] at h
  rw [h]
  decide +kernel

theorem mat6_x_simple_two_fst :
    mat6 (Sp.x 3 (ZMod 2) (Pi.single 2 1) 1) = dec6 lsX2p := by
  rw [x_simple_fst, mat6_apply]
  have h := mat_elt (n := 3) (simpleIdx (2 : Fin 3)).1 (1 : ZMod 2)
  rw [mat_apply] at h
  rw [h]
  decide +kernel

theorem mat6_x_simple_two_snd :
    mat6 (Sp.x 3 (ZMod 2) (-Pi.single 2 1) 1) = dec6 lsX2m := by
  rw [x_simple_snd, mat6_apply]
  have h := mat_elt (n := 3) (simpleIdx (2 : Fin 3)).2 (1 : ZMod 2)
  rw [mat_apply] at h
  rw [h]
  decide +kernel

theorem x0pH_eq : x0pH = Sp.x 3 (ZMod 2) (Pi.single 0 1) 1 :=
  mat6_injective (by rw [mat6_x0pH, mat6_x_simple_zero_fst])

theorem x0mH_eq : x0mH = Sp.x 3 (ZMod 2) (-Pi.single 0 1) 1 :=
  mat6_injective (by rw [mat6_x0mH, mat6_x_simple_zero_snd])

theorem x2pH_eq : x2pH = Sp.x 3 (ZMod 2) (Pi.single 2 1) 1 :=
  mat6_injective (by rw [mat6_x2pH, mat6_x_simple_two_fst])

theorem x2mH_eq : x2mH = Sp.x 3 (ZMod 2) (-Pi.single 2 1) 1 :=
  mat6_injective (by rw [mat6_x2mH, mat6_x_simple_two_snd])

end Matrices

section E0


local notation "𝔽₂" => GaloisField 2 1

noncomputable def E0 : ↥(B3Levi 𝔽₂) ≃* H6 :=
  (lsB3Equiv 𝔽₂).symm.trans (statedSpCongr zeta2 3)

theorem E0_symm_x (γ : Fin 3 → ℤ) :
    E0.symm (Sp.x 3 (ZMod 2) γ 1) = lsB3Equiv 𝔽₂ (Sp.x 3 𝔽₂ γ 1) := by
  show lsB3Equiv 𝔽₂ ((statedSpCongr zeta2 3).symm (Sp.x 3 (ZMod 2) γ 1)) = _
  congr 1
  rw [MulEquiv.symm_apply_eq, statedSpCongr_x, map_one]

theorem pinnedX_single_mem_Lv (j : Fin (Tag.rank .F4)) (c : 𝔽₂) :
    (⟨pinnedX .F4 𝔽₂ (Pi.single j 1) c, pinnedX_mem_adjointGroup _ c⟩ :
      ↥(adjointGroup .F4 𝔽₂)) ∈ Lv 𝔽₂ {j} := by
  rw [← f4Par_eq_pinnedX_charTwo (isRoot_single _ j), Lv_eq_rootSL2,
    rootSL2_eq_sup (isRoot_single _ j)]
  exact Subgroup.mem_sup_left (Adjoint.xPar_mem (isRoot_single _ j) c)

theorem pinnedX_neg_single_mem_Lv (j : Fin (Tag.rank .F4)) (c : 𝔽₂) :
    (⟨pinnedX .F4 𝔽₂ (-Pi.single j 1) c, pinnedX_mem_adjointGroup _ c⟩ :
      ↥(adjointGroup .F4 𝔽₂)) ∈ Lv 𝔽₂ {j} := by
  rw [← f4Par_eq_pinnedX_charTwo (isRoot_neg_single _ j), Lv_eq_rootSL2,
    rootSL2_eq_sup (isRoot_single _ j)]
  exact Subgroup.mem_sup_right (Adjoint.xPar_mem (isRoot_neg_single _ j) c)

noncomputable def SL (j : Fin (Tag.rank .F4)) : Subgroup H6 :=
  ((Lv 𝔽₂ {j}).subgroupOf (B3Levi 𝔽₂)).map E0.toMonoidHom

theorem card_SL {j : Fin (Tag.rank .F4)} (hj : j ≠ 3) : Nat.card ↥(SL j) = 6 := by
  have hle : Lv 𝔽₂ {j} ≤ B3Levi 𝔽₂ := Lv_le_B3Levi (by simpa [eq_comm] using hj)
  rw [SL, Subgroup.card_map_of_injective E0.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_Lv_single]

theorem mem_SL_of {j : Fin (Tag.rank .F4)} {x : H6}
    (h : ((E0.symm x : B3Levi 𝔽₂) : ↥(adjointGroup .F4 𝔽₂)) ∈ Lv 𝔽₂ {j}) : x ∈ SL j :=
  ⟨E0.symm x, Subgroup.mem_subgroupOf.2 h, E0.apply_symm_apply x⟩

theorem x0pH_mem_SL : x0pH ∈ SL 0 := by
  refine mem_SL_of ?_
  rw [x0pH_eq, E0_symm_x, lsB3Equiv_x_single_zero]
  exact pinnedX_single_mem_Lv 0 (1 ^ 2)

theorem x0mH_mem_SL : x0mH ∈ SL 0 := by
  refine mem_SL_of ?_
  rw [x0mH_eq, E0_symm_x, lsB3Equiv_x_neg_single_zero]
  exact pinnedX_neg_single_mem_Lv 0 (1 ^ 2)

theorem x2pH_mem_SL : x2pH ∈ SL 2 := by
  refine mem_SL_of ?_
  rw [x2pH_eq, E0_symm_x, lsB3Equiv_x_single_two]
  exact pinnedX_single_mem_Lv 2 1

theorem x2mH_mem_SL : x2mH ∈ SL 2 := by
  refine mem_SL_of ?_
  rw [x2mH_eq, E0_symm_x, lsB3Equiv_x_neg_single_two]
  exact pinnedX_neg_single_mem_Lv 2 1

theorem SL_zero_eq : SL 0 = Subgroup.closure ({wH, x0pH} : Set H6) := by
  have hle : Subgroup.closure ({wH, x0pH} : Set H6) ≤ SL 0 := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact mul_mem x0pH_mem_SL x0mH_mem_SL
    · rw [Set.mem_singleton_iff.1 hx]
      exact x0pH_mem_SL
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_SL (by decide)]
  exact six_le_card (a := x0pH) (b := wH) (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) orderOf_x0p orderOf_w

theorem SL_two_eq : SL 2 = Subgroup.closure ({zH 2, x2pH} : Set H6) := by
  have hle : Subgroup.closure ({zH 2, x2pH} : Set H6) ≤ SL 2 := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · rw [← x2p_mul_x2m]
      exact mul_mem x2pH_mem_SL x2mH_mem_SL
    · rw [Set.mem_singleton_iff.1 hx]
      exact x2pH_mem_SL
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_SL (by decide)]
  exact six_le_card (a := x2pH) (b := zH 2) (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) orderOf_x2p orderOf_z2

noncomputable def E1 : ↥(B3Levi 𝔽₂) ≃* H6 := E0.trans (MulAut.conj gamH⁻¹)

theorem map_E1_Lv_zero :
    ((Lv 𝔽₂ {0}).subgroupOf (B3Levi 𝔽₂)).map E1.toMonoidHom = K4s := by
  have h1 : ((Lv 𝔽₂ {0}).subgroupOf (B3Levi 𝔽₂)).map E1.toMonoidHom =
      (SL 0).map (MulAut.conj gamH⁻¹).toMonoidHom := by
    rw [SL, Subgroup.map_map]
    rfl
  rw [h1, SL_zero_eq, MonoidHom.map_closure, Set.image_pair, K4s]
  have e1 : (MulAut.conj gamH⁻¹).toMonoidHom wH = zH 0 * zH 1 ^ 2 := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← gam_v]
    group
  have e2 : (MulAut.conj gamH⁻¹).toMonoidHom x0pH = sigH := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← gam_sig]
    group
  rw [e1, e2]

theorem map_E1_Lv_two :
    ((Lv 𝔽₂ {2}).subgroupOf (B3Levi 𝔽₂)).map E1.toMonoidHom = J2s := by
  have h1 : ((Lv 𝔽₂ {2}).subgroupOf (B3Levi 𝔽₂)).map E1.toMonoidHom =
      (SL 2).map (MulAut.conj gamH⁻¹).toMonoidHom := by
    rw [SL, Subgroup.map_map]
    rfl
  rw [h1, SL_two_eq, MonoidHom.map_closure, Set.image_pair, J2s]
  have e1 : (MulAut.conj gamH⁻¹).toMonoidHom (zH 2) = zH 2 := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    conv_lhs => rw [← gam_z2]
    group
  have e2 : (MulAut.conj gamH⁻¹).toMonoidHom x2pH = x2pH := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    conv_lhs => rw [← gam_x2p]
    group
  rw [e1, e2]

end E0

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
