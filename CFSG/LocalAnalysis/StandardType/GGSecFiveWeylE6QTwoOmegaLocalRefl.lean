module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalLin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux7
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalReflAux

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open CFSG.RankThree.Classical2

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

theorem six_le_ncard_isReflection_fix_of_omegaPlus (hK : Nat.card K = 2) {Bs L : Subgroup G}
    {x : G} (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {e : G} (heBs : e ∈ Bs) (heL : e ∈ L)
    (hsupp : Module.finrank K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (omPlusLin hK θ ⟨e, heL⟩)) = 0 ∨
      Module.finrank K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (omPlusLin hK θ ⟨e, heL⟩)) = 6) :
    6 ≤ Set.ncard {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ GGIsReflection 3 r ∧
      r ⟨e, heBs⟩ = ⟨e, heBs⟩} := by
  classical
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  obtain ⟨hxBs, hxL, hxord, hEbot, hExbot⟩ := bstar_basic hZ2 hBs hx1 hBL
  have hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs) :=
    bstar_isComplement hBs hcard hcardE hxBs hxord hExbot
  obtain ⟨Θ, hsigned, hnosgn, hlifts, hfixdim⟩ :=
    frameSignedData_RPlus (K := K) hK (E := Ebar Bs L θ) (Ebar_isElemAbelian θ hBs hEbot)
      (Ebar_card θ hEbot hcardE)
      (fun g hg hg3 => Ebar_selfCent hZ2 hBs hcard hcardE hx1 hLx hBL hstar θ g hg hg3)
  set ΘE := ΘE Bs L θ Θ hEbot with hΘEdef
  have hΘE : ∀ ee, Θ (ΘE ee) = qE Bs L θ ee := fun ee => ΘE_apply Bs L θ Θ hEbot ee
  set e' : ↥(Bs ⊓ L) := ⟨e, Subgroup.mem_inf.mpr ⟨heBs, heL⟩⟩ with he'def
  set f : Fin 4 → Multiplicative (ZMod 3) := ΘE e' with hfdef
  have hq : (Θ f : OrthRest.RPlus K 4) = qMap (K := K) θ ⟨e, heL⟩ := by
    have h1 : ((Θ (ΘE e') : ↥(Ebar Bs L θ)) : OrthRest.RPlus K 4) =
        qMap (K := K) θ ⟨e, heL⟩ := by
      rw [hΘE e']
      simpa using qE_apply Bs L θ e'
    rw [hfdef]
    exact h1
  have hlin : omPlusLin hK θ ⟨e, heL⟩ =
      ((CFSG.StandardType.OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (Θ f) :
        ↥(orthDerived (TableBOrth.qPlusForm K 4))) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := by
    rw [omPlusLin, ← hq]
  have hcardT : (Finset.univ.filter (fun a => f a = 1)).card = 0 ∨
      (Finset.univ.filter (fun a => f a = 1)).card = 3 := by
    have h := hfixdim f
    have hsupp' := hsupp
    rw [hlin] at hsupp'
    rcases hsupp' with h0 | h6
    · left; omega
    · right; omega
  have hY : 6 ≤ (Finset.univ.filter (fun y : OmPlusIdx 4 => omPlusRefl 3 y f = f)).card :=
    six_le_card_fix_omPlusRefl f hcardT
  choose g hgN hgrel using hlifts
  have hlift : ∀ y : OmPlusIdx 4, ∃ l : ↥(NL L Bs), NLqMap Bs L θ l = g y := by
    intro y
    obtain ⟨l, hl, hlNL⟩ := exists_lift_mem_NL hZ2 hBs hcard hcardE hx1 hLx hBL θ (hgN y)
    exact ⟨⟨l, hlNL⟩, by rw [NLqMap_apply]; exact hl⟩
  choose l hl using hlift
  have hconjC : ∀ y, conjC Bs L θ ΘE (l y) = omPlusRefl 3 y := by
    intro y
    refine MulEquiv.ext fun f' => Θ.injective (Subtype.ext ?_)
    rw [← conjC_relation Bs L θ Θ ΘE hΘE (l y) f']
    rw [hl y]
    exact hgrel y f'
  have hreflE : ∀ y, (conjE L Bs (l y)) ^ 2 = 1 ∧
      Nat.card {ee : ↥(Bs ⊓ L) // conjE L Bs (l y) ee = ee} * 3 = Nat.card ↥(Bs ⊓ L) := by
    intro y
    have hconjE : conjE L Bs (l y) = (MulAut.congr ΘE).symm (omPlusRefl 3 y) := by
      apply (MulAut.congr ΘE).injective
      change (MulAut.congr ΘE) (conjE L Bs (l y)) =
        (MulAut.congr ΘE) ((MulAut.congr ΘE).symm (omPlusRefl 3 y))
      rw [show (MulAut.congr ΘE) (conjE L Bs (l y)) = conjC Bs L θ ΘE (l y) from rfl,
        hconjC y, MulEquiv.apply_symm_apply]
    constructor
    · rw [hconjE, ← map_pow, (isReflection_omPlusRefl y).1, map_one]
    · rw [← card_fixedPoints_congr ΘE (conjE L Bs (l y)), hconjE, MulEquiv.apply_symm_apply,
        (isReflection_omPlusRefl y).2, ← Nat.card_congr ΘE.toEquiv]
  have hrefl : ∀ y, GGIsReflection 3 (conjBs L Bs (l y)) := fun y =>
    isReflection_conjE hcompl hxBs hxord hcard hcardE hLx (l y) (hreflE y).1 (hreflE y).2
  have hmem : ∀ y, conjBs L Bs (l y) ∈ ggAutomizer L Bs := by
    intro y
    rw [ggAutomizer_eq_range_conjBs L Bs]
    exact MonoidHom.mem_range.mpr ⟨l y, rfl⟩
  have hfix_e : ∀ y, omPlusRefl 3 y f = f → conjBs L Bs (l y) ⟨e, heBs⟩ = ⟨e, heBs⟩ := by
    intro y hy
    have h1 : conjC Bs L θ ΘE (l y) f = f := by rw [hconjC y, hy]
    rw [hfdef] at h1
    rw [conjC_apply] at h1
    have h3 : conjE L Bs (l y) e' = e' := ΘE.injective h1
    apply Subtype.ext
    rw [conjBs_coe]
    have h4 := congrArg (fun z : ↥(Bs ⊓ L) => (z : G)) h3
    rw [conjE_coe] at h4
    simpa [he'def] using h4
  have hinj : Set.InjOn (fun y : OmPlusIdx 4 => conjBs L Bs (l y))
      ↑(Finset.univ.filter (fun y : OmPlusIdx 4 => omPlusRefl 3 y f = f)) := by
    intro y _ y' _ h
    have h' : conjBs L Bs (l y) = conjBs L Bs (l y') := h
    have hconjE_eq : conjE L Bs (l y) = conjE L Bs (l y') := by
      refine MulEquiv.ext fun ee => ?_
      apply Subtype.ext
      have h1 : ((conjBs L Bs (l y)) ⟨(ee : G), (Subgroup.mem_inf.mp ee.2).1⟩ : ↥Bs) =
          ((conjBs L Bs (l y')) ⟨(ee : G), (Subgroup.mem_inf.mp ee.2).1⟩ : ↥Bs) := by rw [h']
      have h2 : (l y : G) * (ee : G) * (l y : G)⁻¹ =
          (l y' : G) * (ee : G) * (l y' : G)⁻¹ := by
        have h2' := congrArg (fun z : ↥Bs => (z : G)) h1
        rwa [conjBs_coe, conjBs_coe] at h2'
      rw [conjE_coe, conjE_coe]
      exact h2
    have hconjC_eq : conjC Bs L θ ΘE (l y) = conjC Bs L θ ΘE (l y') := by
      show (MulAut.congr ΘE) (conjE L Bs (l y)) =
        (MulAut.congr ΘE) (conjE L Bs (l y'))
      rw [hconjE_eq]
    rw [hconjC y, hconjC y'] at hconjC_eq
    exact omPlusRefl_injective (m := 4) (p := 3) (by norm_num) (by norm_num) hconjC_eq
  have hcard_img : (Finset.image (fun y => conjBs L Bs (l y))
      (Finset.univ.filter (fun y : OmPlusIdx 4 => omPlusRefl 3 y f = f))).card =
      (Finset.univ.filter (fun y : OmPlusIdx 4 => omPlusRefl 3 y f = f)).card :=
    Finset.card_image_of_injOn hinj
  have hsub : ((Finset.image (fun y => conjBs L Bs (l y))
      (Finset.univ.filter (fun y : OmPlusIdx 4 => omPlusRefl 3 y f = f))) :
      Set (MulAut ↥Bs)) ⊆
      {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ GGIsReflection 3 r ∧
        r ⟨e, heBs⟩ = ⟨e, heBs⟩} := by
    intro r hr
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨hmem y, hrefl y, hfix_e y (Finset.mem_filter.mp hy).2⟩
  calc 6 ≤ (Finset.univ.filter (fun y : OmPlusIdx 4 => omPlusRefl 3 y f = f)).card := hY
    _ = (Finset.image (fun y => conjBs L Bs (l y))
          (Finset.univ.filter (fun y : OmPlusIdx 4 => omPlusRefl 3 y f = f))).card :=
        hcard_img.symm
    _ = ((Finset.image (fun y => conjBs L Bs (l y))
          (Finset.univ.filter (fun y : OmPlusIdx 4 => omPlusRefl 3 y f = f)) :
          Finset (MulAut ↥Bs)) : Set (MulAut ↥Bs)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end CFSG.StandardType.E6QTwo

end
