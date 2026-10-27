module

public import CFSG.Monster.AxisCount.BabyGroups
public import CFSG.Monster.AxisCount.BabyCoverGroup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.Baby

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.VisCert
  CFSG.Monster.B CFSG.Monster.B.Short

@[expose] noncomputable def uStarCls : L2 := dec 12288

theorem uStarCls_eq_classOf : uStarCls = classOf (vMinus 0 1) := dec_shortSeed

theorem uStarCls_eq_phi0 : uStarCls = phi0 (coordOf rStar) :=
  uStarCls_eq_classOf.trans (phi0_coordOf_rMinus (by decide : (0 : Fin 24) < 1)).symm

theorem uStarCls_mem_shortSet : uStarCls ∈ shortSet := by
  rw [uStarCls_eq_classOf]
  exact classOf_vMinus_mem_shortSet

theorem conjQ_rStar_of_mem_Jstar {p : Pvis} (hg : thetaEquiv p ∈ Jstar) :
    conjQ p rStar = rStar := by
  have hfix : thetaEquiv p (axis rStar) = axis rStar := fix_aStar_of_mem_Jstar hg
  refine axis_injOn_short (isShortCoord_conjQ p isShortCoord_rStar) isShortCoord_rStar ?_
  rw [← thetaEquiv_axis p isShortCoord_rStar]
  exact hfix

theorem psiVis_smul_uStarCls {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Jstar) :
    psiVis ⟨g, Jstar_le_Gvis hg⟩ • uStarCls = uStarCls := by
  obtain ⟨p, rfl⟩ := mem_Gvis.1 (Jstar_le_Gvis hg)
  have h2 := phi0_coordOf_conjQ p rStar
  rw [conjQ_rStar_of_mem_Jstar hg] at h2
  rw [uStarCls_eq_phi0]
  exact (psiVis_smul_thetaEquiv p _).trans h2.symm

theorem psiAmb_smul_uStarCls {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Jstar) :
    psiAmb g • uStarCls = uStarCls := by
  rw [psiAmb_of_mem (Jstar_le_Gvis hg)]
  exact psiVis_smul_uStarCls hg

@[expose] def babyDelta : Set L2 := {x | x ∈ frameDelta ∧ x + uStarCls ∈ shortSet}

theorem psiAmb_smul_mem_babyDelta
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Jstar) {x : L2}
    (hx : x ∈ babyDelta) : psiAmb g • x ∈ babyDelta := by
  have hu : psiVis ⟨g, Jstar_le_Gvis hg⟩ ∈ Hvis := psiVis_mem_Hvis _
  rw [psiAmb_of_mem (Jstar_le_Gvis hg)]
  refine ⟨(smul_mem_frameDelta_iff hu).2 hx.1, ?_⟩
  have h : psiVis ⟨g, Jstar_le_Gvis hg⟩ • x + uStarCls =
      psiVis ⟨g, Jstar_le_Gvis hg⟩ • (x + uStarCls) := by
    rw [smul_add, psiVis_smul_uStarCls hg]
  rw [h]
  exact smul_mem_shortSet_of_mem_Hvis hu hx.2

@[expose] def wPlus (i : ℕ) : ℤ := if i = 0 then 4 else if i = 1 then 4 else 0

theorem wPlus_apply : ∀ i : Fin 24, wPlus i = vPlus 0 1 i := by decide +kernel

theorem wPlus_eq : (fun i : Fin 24 => wPlus i) = vPlus 0 1 := funext wPlus_apply

theorem rowCheck_wPlus : rowCheck wPlus 12351 = true := by decide +kernel

theorem dec_12351 : dec 12351 = classOf (vPlus 0 1) := by
  have hw : (fun i : Fin 24 => wPlus i) ∈ codeLattice C := wPlus_eq ▸ (vPlus_mem (by decide)).1
  rw [← cls_eq_dec_of_rowCheck hw rowCheck_wPlus, classOf_eq_cls (vPlus_mem (by decide)).1]
  exact cls_congr hw wPlus_eq

theorem twoΩCls_add_uStarCls_mem_shortSet : twoΩCls + uStarCls ∈ shortSet := by
  have h : twoΩCls + uStarCls = classOf (vPlus 0 1) := by
    rw [← dec_12351, ← dec_frameSeed, uStarCls, ← dec_xor]
    rfl
  rw [h]
  exact ⟨vPlus 0 1, vPlus_mem (by decide), rfl⟩

theorem twoΩCls_mem_babyDelta : twoΩCls ∈ babyDelta :=
  ⟨twoΩCls_mem_frameDelta, twoΩCls_add_uStarCls_mem_shortSet⟩

theorem psiAmb_inv_smul_twoΩCls_mem_babyDelta
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Jstar) :
    (psiAmb g)⁻¹ • twoΩCls ∈ babyDelta := by
  rw [← psiAmb_inv (Jstar_le_Gvis hg)]
  exact psiAmb_smul_mem_babyDelta (Jstar.inv_mem hg) twoΩCls_mem_babyDelta

theorem natCard_L2 : Nat.card L2 = 2 ^ 24 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_L2]

theorem exists_dec (x : L2) : ∃ v < 2 ^ 24, dec v = x := by
  have hinj : Set.InjOn dec (Finset.range (2 ^ 24) : Set ℕ) := fun a ha b hb h =>
    dec_injective (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
  have hcard : (dec '' (Finset.range (2 ^ 24) : Set ℕ)).ncard = Nat.card L2 := by
    rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range, natCard_L2]
  have himg : dec '' (Finset.range (2 ^ 24) : Set ℕ) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [hcard, Set.ncard_univ])
  have hx : x ∈ dec '' (Finset.range (2 ^ 24) : Set ℕ) := himg ▸ Set.mem_univ x
  obtain ⟨v, hv, rfl⟩ := hx
  exact ⟨v, Finset.mem_range.1 hv, rfl⟩

theorem shortSet_eq_image_shortFound :
    shortSet = dec '' (shortFound CFSG.Monster.B.Short.Native.shortTables : Set ℕ) := by
  have hsub := shortFacts.image_shortFound_subset_orbit kGenN_smul_dec
  rw [closure_kGenN_Iio, dec_shortSeed] at hsub
  have hcard := shortFacts.ncard_image_shortFound dec_inj
  have horb : MulAction.orbit Kvis (classOf (vMinus 0 1)) ⊆ shortSet := by
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    exact smul_mem_shortSet_of_mem_Hvis (Kvis_le_Hvis hu) classOf_vMinus_mem_shortSet
  exact (Set.eq_of_subset_of_ncard_le (hsub.trans horb)
    (by rw [ncard_shortSet, hcard]; rfl)).symm

end CFSG.Monster.AxisCount.Baby
