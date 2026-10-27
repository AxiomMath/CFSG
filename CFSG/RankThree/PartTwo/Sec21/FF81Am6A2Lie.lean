module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6LSideRoots
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2Chain
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Lv
public import CFSG.LargeExtraspecial.A2ModFrCMat
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeA2
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundAll
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.LargeExtraspecial.A2ModCfg
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogSp6
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofStatements
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne
public import CFSG.RankThree.PartTwo.Sec21.Item233
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
public import CFSG.RankThree.PartTwo.Sec8.Hering418Orders

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2

open Subgroup CFSG.SeitzReduction.F4Pilot CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Ree (ReeTag)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Open
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6

local instance a2NeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Matrices

open CFSG.ClassicalInvolution.Balance (x_simple_fst x_simple_snd simpleIdx)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt mat_elt mat_apply)

noncomputable def x1pH : H6 := ofCode (a2S12, a2S12) (by decide +kernel)

noncomputable def x1mH : H6 := ofCode (a2S21, a2S21) (by decide +kernel)

theorem mat6_x1pH : mat6 x1pH = dec6 a2S12 := mat6_ofCode _ _

theorem mat6_x1mH : mat6 x1mH = dec6 a2S21 := mat6_ofCode _ _

theorem mat6_x_simple_one_fst :
    mat6 (Sp.x 3 (ZMod 2) (Pi.single 1 1) 1) = dec6 a2S12 := by
  rw [x_simple_fst, mat6_apply]
  have h := mat_elt (n := 3) (simpleIdx (1 : Fin 3)).1 (1 : ZMod 2)
  rw [mat_apply] at h
  rw [h]
  decide +kernel

theorem mat6_x_simple_one_snd :
    mat6 (Sp.x 3 (ZMod 2) (-Pi.single 1 1) 1) = dec6 a2S21 := by
  rw [x_simple_snd, mat6_apply]
  have h := mat_elt (n := 3) (simpleIdx (1 : Fin 3)).2 (1 : ZMod 2)
  rw [mat_apply] at h
  rw [h]
  decide +kernel

theorem x1pH_eq : x1pH = Sp.x 3 (ZMod 2) (Pi.single 1 1) 1 :=
  mat6_injective (by rw [mat6_x1pH, mat6_x_simple_one_fst])

theorem x1mH_eq : x1mH = Sp.x 3 (ZMod 2) (-Pi.single 1 1) 1 :=
  mat6_injective (by rw [mat6_x1mH, mat6_x_simple_one_snd])

end Matrices

section Rel


local notation "𝔽₂" => GaloisField 2 1

theorem lsB3Equiv_x_single_one (c : 𝔽₂) :
    ((lsB3Equiv 𝔽₂ (Sp.x 3 𝔽₂ (Pi.single 1 1) c) : B3Levi 𝔽₂) : adjointGroup .F4 𝔽₂) =
      ⟨pinnedX .F4 𝔽₂ (Pi.single 1 1) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have h := graphAutF4_pinnedX_single_two (K := 𝔽₂) c
  rw [coe_lsB3Equiv, c3LeviEquiv_x_single_one, h]

theorem lsB3Equiv_x_neg_single_one (c : 𝔽₂) :
    ((lsB3Equiv 𝔽₂ (Sp.x 3 𝔽₂ (-Pi.single 1 1) c) : B3Levi 𝔽₂) : adjointGroup .F4 𝔽₂) =
      ⟨pinnedX .F4 𝔽₂ (-Pi.single 1 1) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have h := graphAutF4_pinnedX_neg_single_two (K := 𝔽₂) c
  rw [coe_lsB3Equiv, c3LeviEquiv_x_neg_single_one, h]

noncomputable def Xp (j : Fin (Tag.rank .F4)) : ↥(adjointGroup .F4 𝔽₂) :=
  ⟨pinnedX .F4 𝔽₂ (Pi.single j 1) 1, pinnedX_mem_adjointGroup _ 1⟩

noncomputable def Xm (j : Fin (Tag.rank .F4)) : ↥(adjointGroup .F4 𝔽₂) :=
  ⟨pinnedX .F4 𝔽₂ (-Pi.single j 1) 1, pinnedX_mem_adjointGroup _ 1⟩

noncomputable def aP : ↥(B3Levi 𝔽₂) := E0.symm x2pH

noncomputable def aM : ↥(B3Levi 𝔽₂) := E0.symm x2mH

noncomputable def bP : ↥(B3Levi 𝔽₂) := E0.symm x1pH

noncomputable def bM : ↥(B3Levi 𝔽₂) := E0.symm x1mH

theorem coe_aP : ((aP : B3Levi 𝔽₂) : adjointGroup .F4 𝔽₂) = Xp 2 := by
  rw [aP, x2pH_eq, E0_symm_x, lsB3Equiv_x_single_two]
  rfl

theorem coe_aM : ((aM : B3Levi 𝔽₂) : adjointGroup .F4 𝔽₂) = Xm 2 := by
  rw [aM, x2mH_eq, E0_symm_x, lsB3Equiv_x_neg_single_two]
  rfl

theorem coe_bP : ((bP : B3Levi 𝔽₂) : adjointGroup .F4 𝔽₂) = Xp 1 := by
  rw [bP, x1pH_eq, E0_symm_x, lsB3Equiv_x_single_one, one_pow]
  rfl

theorem coe_bM : ((bM : B3Levi 𝔽₂) : adjointGroup .F4 𝔽₂) = Xm 1 := by
  rw [bM, x1mH_eq, E0_symm_x, lsB3Equiv_x_neg_single_one, one_pow]
  rfl

theorem rel_ap_bm : aP * bM = bM * aP := by
  apply E0.injective
  rw [map_mul, map_mul, aP, bM, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact commute_of_commutes6 mat6_x2pH mat6_x1mH (by decide +kernel)

theorem rel_am_bp : aM * bP = bP * aM := by
  apply E0.injective
  rw [map_mul, map_mul, aM, bP, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact commute_of_commutes6 mat6_x2mH mat6_x1pH (by decide +kernel)

theorem ne_am_bm : aM * bM ≠ bM * aM := by
  intro h
  have h' := congrArg E0 h
  rw [map_mul, map_mul, aM, bM, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  have := commutes6_of_commute mat6_x2mH mat6_x1mH h'
  revert this
  decide +kernel

theorem ne_ap_bp : aP * bP ≠ bP * aP := by
  intro h
  have h' := congrArg E0 h
  rw [map_mul, map_mul, aP, bP, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  have := commutes6_of_commute mat6_x2pH mat6_x1pH h'
  revert this
  decide +kernel

theorem aP_sq : aP * aP = 1 := by
  apply E0.injective
  rw [map_mul, aP, MulEquiv.apply_symm_apply, map_one]
  exact x2p_sq

theorem aM_sq : aM * aM = 1 := by
  apply E0.injective
  rw [map_mul, aM, MulEquiv.apply_symm_apply, map_one]
  exact mul_eq_of_code mat6_x2mH mat6_x2mH (by rw [map_one, dec6_one6]) (by decide +kernel)

theorem aP_ne_one : aP ≠ 1 := by
  intro h
  apply x2p_ne_one
  have := congrArg E0 h
  rwa [aP, MulEquiv.apply_symm_apply, map_one] at this

theorem aM_ne_one : aM ≠ 1 := by
  intro h
  have h0 : x2mH = 1 := by
    have := congrArg E0 h
    rwa [aM, MulEquiv.apply_symm_apply, map_one] at this
  have h1 := congrArg mat6 h0
  rw [mat6_x2mH, map_one, ← dec6_one6] at h1
  have h2 := dec6_injective (by decide +kernel) canon6_one6 h1
  revert h2
  decide +kernel

theorem aP_ne_aM : aP ≠ aM := by
  intro h
  have h0 : x2pH = x2mH := E0.symm.injective h
  have h1 := congrArg mat6 h0
  rw [mat6_x2pH, mat6_x2mH] at h1
  have h2 := dec6_injective (by decide +kernel) (by decide +kernel) h1
  revert h2
  decide +kernel

theorem orderOf_aP_mul_aM : orderOf (aP * aM) = 3 := by
  have h : aP * aM = E0.symm (zH 2) := by
    rw [aP, aM, ← map_mul, x2p_mul_x2m]
  rw [h, MulEquiv.orderOf_eq]
  exact orderOf_z2

theorem Lv_eq_closure_pair (j : Fin (Tag.rank .F4)) :
    Lv 𝔽₂ {j} = Subgroup.closure ({Xp j, Xm j} : Set ↥(adjointGroup .F4 𝔽₂)) := by
  have h01 : ∀ c : 𝔽₂, c = 0 ∨ c = 1 := fun c => by
    have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases h (zeta2 c) with h | h
    · left
      exact zeta2.injective (by rw [h, map_zero])
    · right
      exact zeta2.injective (by rw [h, map_one])
  apply le_antisymm
  · rw [Lv_eq_rootSL2, rootSL2_eq_sup (isRoot_single _ j)]
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨c, hc⟩ := (mem_rootGroup_iff_pinnedX (isRoot_single _ j)).1 hg
      rcases h01 c with rfl | rfl
      · have : g = 1 := Subtype.ext (by rw [← hc, pinnedX_zero]; rfl)
        rw [this]
        exact one_mem _
      · have : g = Xp j := Subtype.ext hc.symm
        rw [this]
        exact Subgroup.subset_closure (by simp)
    · intro g hg
      obtain ⟨c, hc⟩ := (mem_rootGroup_iff_pinnedX (isRoot_neg_single _ j)).1 hg
      rcases h01 c with rfl | rfl
      · have : g = 1 := Subtype.ext (by rw [← hc, pinnedX_zero]; rfl)
        rw [this]
        exact one_mem _
      · have : g = Xm j := Subtype.ext hc.symm
        rw [this]
        exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact pinnedX_single_mem_Lv j 1
    · exact pinnedX_neg_single_mem_Lv j 1

open CFSG.RankThree.Chevalley (F4A2Kind f4A2Equiv
  F4_native_long_and_short_A2_faithful_SL3_all_characteristics)
open CFSG.RankThree.Chevalley.SteinbergBN (qx qy left_mem_pair right_mem_pair)

noncomputable def A2e : ↥(Lv 𝔽₂ {2, 3}) ≃* Matrix.SpecialLinearGroup (Fin 3) 𝔽₂ :=
  LvA2Equiv (K := 𝔽₂) .short

theorem Xp_two_mem : Xp 2 ∈ Lv 𝔽₂ {2, 3} := Lv_two_le_A (pinnedX_single_mem_Lv 2 1)

theorem Xm_two_mem : Xm 2 ∈ Lv 𝔽₂ {2, 3} := Lv_two_le_A (pinnedX_neg_single_mem_Lv 2 1)

theorem Xp_three_mem : Xp 3 ∈ Lv 𝔽₂ {2, 3} := Lv_three_le_A (pinnedX_single_mem_Lv 3 1)

theorem Xm_three_mem : Xm 3 ∈ Lv 𝔽₂ {2, 3} := Lv_three_le_A (pinnedX_neg_single_mem_Lv 3 1)

theorem A2e_Xp_two : A2e ⟨Xp 2, Xp_two_mem⟩ =
    f4A2Equiv 𝔽₂ .short (qx (left_mem_pair F4A2Kind.short.i F4A2Kind.short.j) 1) := by
  show f4A2Equiv 𝔽₂ .short _ = f4A2Equiv 𝔽₂ .short _
  congr 1
  exact Subtype.ext (pinnedX_single _ _ 2 1)

theorem A2e_Xm_two : A2e ⟨Xm 2, Xm_two_mem⟩ =
    f4A2Equiv 𝔽₂ .short (qy (left_mem_pair F4A2Kind.short.i F4A2Kind.short.j) 1) := by
  show f4A2Equiv 𝔽₂ .short _ = f4A2Equiv 𝔽₂ .short _
  congr 1
  exact Subtype.ext (pinnedX_neg_single _ _ 2 1)

theorem A2e_Xp_three : A2e ⟨Xp 3, Xp_three_mem⟩ =
    f4A2Equiv 𝔽₂ .short (qx (right_mem_pair F4A2Kind.short.i F4A2Kind.short.j) 1) := by
  show f4A2Equiv 𝔽₂ .short _ = f4A2Equiv 𝔽₂ .short _
  congr 1
  exact Subtype.ext (pinnedX_single _ _ 3 1)

theorem A2e_Xm_three : A2e ⟨Xm 3, Xm_three_mem⟩ =
    f4A2Equiv 𝔽₂ .short (qy (right_mem_pair F4A2Kind.short.i F4A2Kind.short.j) 1) := by
  show f4A2Equiv 𝔽₂ .short _ = f4A2Equiv 𝔽₂ .short _
  congr 1
  exact Subtype.ext (pinnedX_neg_single _ _ 3 1)

theorem A2e_gen :
    ((A2e ⟨Xp 2, Xp_two_mem⟩ : Matrix.SpecialLinearGroup (Fin 3) 𝔽₂) :
        Matrix (Fin 3) (Fin 3) 𝔽₂) = 1 + Matrix.single 0 1 1 ∧
      ((A2e ⟨Xm 2, Xm_two_mem⟩ : Matrix.SpecialLinearGroup (Fin 3) 𝔽₂) :
        Matrix (Fin 3) (Fin 3) 𝔽₂) = 1 + Matrix.single 1 0 1 ∧
      ((A2e ⟨Xp 3, Xp_three_mem⟩ : Matrix.SpecialLinearGroup (Fin 3) 𝔽₂) :
        Matrix (Fin 3) (Fin 3) 𝔽₂) = 1 + Matrix.single 1 2 1 ∧
      ((A2e ⟨Xm 3, Xm_three_mem⟩ : Matrix.SpecialLinearGroup (Fin 3) 𝔽₂) :
        Matrix (Fin 3) (Fin 3) 𝔽₂) = 1 + Matrix.single 2 1 1 := by
  have h := (F4_native_long_and_short_A2_faithful_SL3_all_characteristics (K := 𝔽₂) .short).1 1
  rw [A2e_Xp_two, A2e_Xm_two, A2e_Xp_three, A2e_Xm_three]
  exact h

noncomputable def toZ2 : Matrix.SpecialLinearGroup (Fin 3) 𝔽₂ →* G3 :=
  Matrix.SpecialLinearGroup.map (zeta2 : 𝔽₂ →+* ZMod 2)

noncomputable def PhiHom (c : H6) : ↥(Lv 𝔽₂ {2, 3}) →* H6 :=
  ((MulAut.conj c).toMonoidHom.comp Slev).comp (toZ2.comp A2e.toMonoidHom)

theorem toZ2_eq_transvection {t : Matrix.SpecialLinearGroup (Fin 3) 𝔽₂} {i j : Fin 3}
    (hij : i ≠ j) (h : (t : Matrix (Fin 3) (Fin 3) 𝔽₂) = 1 + Matrix.single i j 1) :
    toZ2 t = Matrix.SpecialLinearGroup.transvection hij 1 := by
  apply Subtype.ext
  rw [toZ2, Matrix.SpecialLinearGroup.map_apply_coe, h,
    Matrix.SpecialLinearGroup.transvection_coe]
  rw [RingHom.mapMatrix_apply, Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1
  ext a b
  simp [Matrix.single_apply]


theorem PhiHom_Xp_two (c : H6) : PhiHom c ⟨Xp 2, Xp_two_mem⟩ = c * Slev tv01 * c⁻¹ := by
  simp only [PhiHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [toZ2_eq_transvection (by decide) A2e_gen.1]
  rfl

theorem PhiHom_Xm_two (c : H6) : PhiHom c ⟨Xm 2, Xm_two_mem⟩ = c * Slev tv10 * c⁻¹ := by
  simp only [PhiHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [toZ2_eq_transvection (by decide) A2e_gen.2.1]
  rfl

theorem PhiHom_Xp_three (c : H6) : PhiHom c ⟨Xp 3, Xp_three_mem⟩ = c * Slev tv12 * c⁻¹ := by
  simp only [PhiHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [toZ2_eq_transvection (by decide) A2e_gen.2.2.1]
  rfl

theorem PhiHom_Xm_three (c : H6) : PhiHom c ⟨Xm 3, Xm_three_mem⟩ = c * Slev tv21 * c⁻¹ := by
  simp only [PhiHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [toZ2_eq_transvection (by decide) A2e_gen.2.2.2]
  rfl

theorem PhiHom_gY :
    PhiHom gYH ⟨Xp 2, Xp_two_mem⟩ = pH ∧ PhiHom gYH ⟨Xm 2, Xm_two_mem⟩ = qH ∧
      PhiHom gYH ⟨Xp 3, Xp_three_mem⟩ = ePH ∧ PhiHom gYH ⟨Xm 3, Xm_three_mem⟩ = eMH := by
  obtain ⟨h1, h2, h3, h4⟩ := Slev_conj_gY
  exact ⟨(PhiHom_Xp_two _).trans h1, (PhiHom_Xm_two _).trans h2,
    (PhiHom_Xp_three _).trans h3, (PhiHom_Xm_three _).trans h4⟩

theorem PhiHom_gYJ :
    PhiHom (gYH * jH) ⟨Xp 2, Xp_two_mem⟩ = qH ∧ PhiHom (gYH * jH) ⟨Xm 2, Xm_two_mem⟩ = pH ∧
      PhiHom (gYH * jH) ⟨Xp 3, Xp_three_mem⟩ = eMH ∧
        PhiHom (gYH * jH) ⟨Xm 3, Xm_three_mem⟩ = ePH := by
  obtain ⟨h1, h2, h3, h4⟩ := Slev_conj_gYJ
  exact ⟨(PhiHom_Xp_two _).trans h1, (PhiHom_Xm_two _).trans h2,
    (PhiHom_Xp_three _).trans h3, (PhiHom_Xm_three _).trans h4⟩

noncomputable def gp (j : Fin (Tag.rank .F4)) : ↥(Lv 𝔽₂ {j}) := ⟨Xp j, pinnedX_single_mem_Lv j 1⟩

noncomputable def gm (j : Fin (Tag.rank .F4)) : ↥(Lv 𝔽₂ {j}) :=
  ⟨Xm j, pinnedX_neg_single_mem_Lv j 1⟩

theorem closure_Lv_gens (j : Fin (Tag.rank .F4)) :
    Subgroup.closure ({gp j, gm j} : Set ↥(Lv 𝔽₂ {j})) = ⊤ := by
  apply Subgroup.map_injective (Lv 𝔽₂ {j}).subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact (Lv_eq_closure_pair j).symm

theorem Lv_hom_ext {G' : Type*} [Group G'] (j : Fin (Tag.rank .F4))
    {f₁ f₂ : ↥(Lv 𝔽₂ {j}) →* G'} (hp : f₁ (gp j) = f₂ (gp j)) (hm : f₁ (gm j) = f₂ (gm j)) :
    f₁ = f₂ := by
  refine MonoidHom.eq_of_eqOn_dense (closure_Lv_gens j) fun x hx => ?_
  rcases hx with rfl | hx
  · exact hp
  · rw [Set.mem_singleton_iff.1 hx]
    exact hm

theorem conclusion_of_values {G : Type} [Group G] (θP : ↥(B3Levi 𝔽₂) →* G) (M X : Subgroup G)
    (F : H6 →* G) (c : H6) (hF : F.range ≤ M)
    (hpl : F (PhiHom c ⟨Xp 2, Xp_two_mem⟩) = θP aP)
    (hmi : F (PhiHom c ⟨Xm 2, Xm_two_mem⟩) = θP aM)
    (h3p : F (PhiHom c ⟨Xp 3, Xp_three_mem⟩) ∈ X) (h3m : F (PhiHom c ⟨Xm 3, Xm_three_mem⟩) ∈ X) :
    ∃ θA : ↥(Lv 𝔽₂ {2, 3}) →* G,
      (∀ (x : ↥(adjointGroup .F4 𝔽₂)) (hx : x ∈ Lv 𝔽₂ {2}),
        θA ⟨x, Lv_two_le_A hx⟩ = θP ⟨x, Lv_two_le_P hx⟩) ∧
      (∀ (x : ↥(adjointGroup .F4 𝔽₂)) (hx : x ∈ Lv 𝔽₂ {3}), θA ⟨x, Lv_three_le_A hx⟩ ∈ X) ∧
      θA.range ≤ M := by
  obtain ⟨θA, hθA⟩ : ∃ θA : ↥(Lv 𝔽₂ {2, 3}) →* G, ∀ y, θA y = F (PhiHom c y) :=
    ⟨F.comp (PhiHom c), fun y => rfl⟩
  refine ⟨θA, ?_, ?_, ?_⟩
  · intro x hx
    have haP : (⟨Xp 2, Lv_two_le_P (pinnedX_single_mem_Lv 2 1)⟩ : ↥(B3Levi 𝔽₂)) = aP :=
      Subtype.ext coe_aP.symm
    have haM : (⟨Xm 2, Lv_two_le_P (pinnedX_neg_single_mem_Lv 2 1)⟩ : ↥(B3Levi 𝔽₂)) = aM :=
      Subtype.ext coe_aM.symm
    have hext : θA.comp (Subgroup.inclusion Lv_two_le_A) =
        θP.comp (Subgroup.inclusion Lv_two_le_P) := by
      refine Lv_hom_ext 2 ?_ ?_
      · show θA ⟨Xp 2, _⟩ = θP ⟨Xp 2, _⟩
        rw [hθA, hpl, haP]
      · show θA ⟨Xm 2, _⟩ = θP ⟨Xm 2, _⟩
        rw [hθA, hmi, haM]
    exact DFunLike.congr_fun hext ⟨x, hx⟩
  · intro x hx
    have hext : (⊤ : Subgroup ↥(Lv 𝔽₂ {3})) ≤
        X.comap (θA.comp (Subgroup.inclusion Lv_three_le_A)) := by
      rw [← closure_Lv_gens 3, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · show θA ⟨Xp 3, _⟩ ∈ X
        rw [hθA]
        exact h3p
      · show θA ⟨Xm 3, _⟩ ∈ X
        rw [hθA]
        exact h3m
    exact hext (Subgroup.mem_top ⟨x, hx⟩)
  · rintro _ ⟨y, rfl⟩
    rw [hθA]
    exact hF ⟨_, rfl⟩

end Rel

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2
