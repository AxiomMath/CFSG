module

public import CFSG.Monster.Existence.TwoPoint.Fi23
public import CFSG.Monster.Existence.TwoPoint.Fi22Conj
import all CFSG.Sporadic.Bridge.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels imgWords)
open CFSG.Sporadic.Fi23.Native (dLetters)

theorem fiRelEq : TauCeti.Sporadic.fi23Presentation.relatorLetters = rels :=
  CFSG.Sporadic.Bridge.Fi23.relatorLetters_eq

theorem fiGenEq : TauCeti.Sporadic.fi23Presentation.generatorCount = 10 :=
  CFSG.Sporadic.Bridge.Fi23.generatorCount_eq


theorem fi22Check_parts :
    (wordLin (fiRhoT ++ fiCGamma) = wordLin (fiCGamma ++ fiWU[0]!) ∧
        wordLin (fiRhoT ++ fiCDelta) = wordLin (fiCDelta ++ fiWDelta)) ∧
      fiImgConjCheck 0 27 = true :=
  fi22Check_ok

theorem fi_toJ_bijective :
    Function.Bijective CFSG.Sporadic.Bridge.Fi23.toJ := by
  have hfc := CFSG.Sporadic.Presentation.Fi23.finite_card_le
  have : Finite TauCeti.Sporadic.fi23Presentation.Group := hfc.1
  exact CFSG.Sporadic.Bridge.Fi23.toJ_surjective.bijective_of_nat_card_le
    (by rw [CFSG.Sporadic.Fi23.card_J]; exact hfc.2)

noncomputable def fiPresEquiv :

    TauCeti.Sporadic.fi23Presentation.Group ≃* CFSG.Sporadic.Fi23.J :=
  MulEquiv.ofBijective CFSG.Sporadic.Bridge.Fi23.toJ fi_toJ_bijective

theorem fiPres_simple :
    IsSimpleGroup TauCeti.Sporadic.fi23Presentation.Group :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_J fiPresEquiv

theorem fiHom_injective' :
    Function.Injective (fiHom TauCeti.Sporadic.fi23Presentation fiRelEq) :=
  have := fiPres_simple
  fiHom_injective _ fiRelEq fiGenEq

@[expose] noncomputable def fiK :
    Subgroup MGriess :=
  (fiHom TauCeti.Sporadic.fi23Presentation fiRelEq).range

theorem fiK_le :
    fiK ≤ cent2 fiAlpha fiBeta := range_fiHom_le _ fiRelEq fiGenEq

theorem fiE_mem_fiK
    {i : ℕ} (hi : i < 10) : fiE i ∈ fiK :=
  ⟨PresentedGroup.of ⟨i, by rw [fiGenEq]; exact hi⟩, fiHom_of _ fiRelEq _⟩

noncomputable def fiPhi :
    fiK ≃* CFSG.Sporadic.Fi23.J :=
  (MonoidHom.ofInjective fiHom_injective').symm.trans fiPresEquiv

theorem fi_toJ_of
    {i : ℕ} (hi : i < 10) :
    CFSG.Sporadic.Bridge.Fi23.toJ (PresentedGroup.of ⟨i, by rw [fiGenEq]; exact hi⟩) =
      CFSG.Sporadic.Bridge.Fi23.img i := by
  have h := CFSG.Sporadic.Bridge.presHom_presGen TauCeti.Sporadic.fi23Presentation
    CFSG.Sporadic.Bridge.Fi23.img CFSG.Sporadic.Bridge.Fi23.relators_eval
    (by rw [fiGenEq]; exact hi : i < TauCeti.Sporadic.fi23Presentation.generatorCount)
  rw [CFSG.Sporadic.Bridge.presGen, dite_eq_left (by rw [fiGenEq]; exact hi)] at h
  exact h

theorem fiPhi_fiE
    {i : ℕ} (hi : i < 10) :
    fiPhi ⟨fiE i, fiE_mem_fiK hi⟩ = CFSG.Sporadic.Bridge.Fi23.img i := by
  have h1 : (MonoidHom.ofInjective fiHom_injective').symm ⟨fiE i, fiE_mem_fiK hi⟩ =
      PresentedGroup.of ⟨i, by rw [fiGenEq]; exact hi⟩ := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply]
    exact (fiHom_of _ fiRelEq ⟨i, by rw [fiGenEq]; exact hi⟩).symm
  show fiPresEquiv ((MonoidHom.ofInjective fiHom_injective').symm ⟨fiE i, fiE_mem_fiK hi⟩) = _
  rw [h1]
  exact fi_toJ_of hi

theorem fiImgConj_parts (h : fiImgConjCheck 0 27 = true) :
    imgWords[0]! = imgWords[0]!.take 27 ++ fiDPowWord ++ fiInvWord (imgWords[0]!.take 27) ∧
      ∀ z ∈ imgWords[0]!.take 27, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by
  unfold fiImgConjCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
  refine ⟨h.1, fun z hz => ?_⟩
  have := h.2 z hz
  simpa [beq_iff_eq, or_assoc] using this

theorem fi_genG_neg {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    CFSG.Sporadic.Fi23.genG (-z) = (CFSG.Sporadic.Fi23.genG z)⁻¹ := by
  rcases hz with rfl | rfl | rfl | rfl <;> simp [CFSG.Sporadic.Fi23.genG]

theorem fi_wordG_append {G : Type*} [Group G] (g : ℤ → G) (a b : List ℤ) :
    CFSG.Sporadic.Th.wordG g (a ++ b) =
      CFSG.Sporadic.Th.wordG g a * CFSG.Sporadic.Th.wordG g b := by
  simp [CFSG.Sporadic.Th.wordG]

theorem fi_wordG_dLetters :
    CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG dLetters =
      CFSG.Sporadic.Fi23.wordJ CFSG.Sporadic.Fi23.Native.dWord := by
  unfold CFSG.Sporadic.Th.wordG dLetters CFSG.Sporadic.Fi23.wordJ
  rw [List.map_map]
  exact congrArg List.prod
    (List.map_congr_left fun x _ => by by_cases hx : x = 0 <;> simp [hx, CFSG.Sporadic.Fi23.genG])

theorem fi_wordG_dPowWord :
    CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG fiDPowWord = CFSG.Sporadic.Fi23.d := by
  have h : CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG fiDPowWord =
      (CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG dLetters) ^ 7 := by
    simp only [CFSG.Sporadic.Th.wordG, fiDPowWord, List.map_flatten, List.prod_flatten,
      List.map_replicate, List.prod_replicate]
  rw [h, fi_wordG_dLetters]
  rfl

theorem fi_wordG_invWord
    {u : List ℤ} (hu : ∀ z ∈ u, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG (fiInvWord u) =
      (CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG u)⁻¹ := by
  unfold CFSG.Sporadic.Th.wordG fiInvWord
  have h1 : List.map CFSG.Sporadic.Fi23.genG (List.map (fun z => -z) u.reverse) =
      ((List.map CFSG.Sporadic.Fi23.genG u).map fun x => x⁻¹).reverse := by
    rw [List.map_map, List.map_map, ← List.map_reverse]
    apply List.map_congr_left
    intro z hz
    have hz' := hu z (List.mem_reverse.1 hz)
    simp [Function.comp, fi_genG_neg hz']
  rw [h1, ← List.prod_inv_reverse]

@[expose] noncomputable def fiU : CFSG.Sporadic.Fi23.J :=
  CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG (imgWords[0]!.take 27)

theorem fiU_conj :
    fiU * CFSG.Sporadic.Fi23.d * fiU⁻¹ = CFSG.Sporadic.Bridge.Fi23.img 0 := by
  obtain ⟨hw, hu⟩ := fiImgConj_parts fi22Check_parts.2
  unfold CFSG.Sporadic.Bridge.Fi23.img
  conv_rhs => rw [hw]
  rw [fi_wordG_append, fi_wordG_append, fi_wordG_dPowWord, fi_wordG_invWord hu]
  rfl

end CFSG.Monster.Existence
