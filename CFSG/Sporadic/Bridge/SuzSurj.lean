module

public import CFSG.Sporadic.Suz.Simple
public import CFSG.Sporadic.Presentation.Suz
public import CFSG.Sporadic.Bridge.Common
public import Certificates.Certificate9219
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Bridge.Suz

open CFSG.Sporadic.Suz CFSG.KD.SuzB TauCeti

theorem facts : SuzMats.Facts := Certificates.certificate9219

@[expose] noncomputable def seedJ (i : ℕ) : J :=
  if i = 0 then a else b

@[expose] noncomputable def img (k : ℕ) : J :=
  wordProd seedJ (wordAt imgWords k)

theorem mat_inv (g : J) : mat g⁻¹ = (mat g)⁻¹ := by
  simp [mat, Matrix.coe_units_inv]

theorem mat_wordProd (x : ℕ → J) (w : List (ℕ × Bool)) :
    mat (wordProd x w) = SuzMats.wordM (fun i => mat (x i)) w := by
  induction w with
  | nil => simp [wordProd, SuzMats.wordM, mat_one]
  | cons l w ih =>
    simp only [wordProd, SuzMats.wordM, List.map_cons, List.prod_cons] at ih ⊢
    rw [mat_mul, ih]
    by_cases h : l.2 <;> simp [h, mat_inv]

theorem mat_seedJ : (fun i => mat (seedJ i)) = SuzMats.seeds := by
  funext i
  unfold seedJ SuzMats.seeds
  split_ifs
  exacts [a_val, b_val]

theorem mat_img : (fun k => mat (img k)) = SuzMats.img := by
  funext k
  rw [img, mat_wordProd, mat_seedJ]
  rfl

theorem img_of_le {k : ℕ} (hk : 7 ≤ k) : img k = 1 := by
  have hl : imgWords.length = 7 := rfl
  have h : wordAt imgWords k = [] := by
    unfold wordAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hl]; exact hk)]
    rfl
  rw [img, h]
  simp [wordProd]

private theorem presentation_eq : SporadicName.Suz.presentation = Sporadic.suzPresentation := rfl

theorem generatorCount_eq : Sporadic.suzPresentation.generatorCount = 7 := by
  simp [GroupPresentation.generatorCount]

theorem relators_eval :
    ∀ v ∈ Sporadic.suzPresentation.relatorLetters, wordProd img v = 1 := by
  intro v hv
  apply mat_injective
  rw [mat_wordProd, mat_img, mat_one]
  exact facts.rels v hv

@[expose] noncomputable def toJ :
    Sporadic.suzPresentation.Group →* J :=
  presHom Sporadic.suzPresentation img relators_eval

theorem img_mem_range (k : ℕ) :
    img k ∈ toJ.range := by
  by_cases hk : k < 7
  · exact ⟨presGen Sporadic.suzPresentation k,
      presHom_presGen _ _ _ (by rw [generatorCount_eq]; exact hk)⟩
  · rw [img_of_le (by omega)]
    exact one_mem _

theorem a_mem_range :
    a ∈ toJ.range := by
  have h : wordProd img (wordAt surjWords 0) = a := by
    apply mat_injective
    rw [mat_wordProd, mat_img, facts.surjA]
    exact a_val.symm
  rw [← h]
  exact wordProd_mem img_mem_range _

theorem b_mem_range :
    b ∈ toJ.range := by
  have h : wordProd img (wordAt surjWords 1) = b := by
    apply mat_injective
    rw [mat_wordProd, mat_img, facts.surjB]
    exact b_val.symm
  rw [← h]
  exact wordProd_mem img_mem_range _

theorem toJ_surjective :
    Function.Surjective toJ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact a_mem_range
  · exact b_mem_range

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Suz.Group)
    (hcard : Nat.card SporadicName.Suz.Group ≤ 448345497600) :
    Nonempty (Blueprint.NativeSporadic.Suz ≃* SporadicName.Suz.Group) := by
  revert hfin hcard
  show Finite SporadicName.Suz.presentation.Group →
    Nat.card SporadicName.Suz.presentation.Group ≤ 448345497600 →
    Nonempty (Blueprint.NativeSporadic.Suz ≃* SporadicName.Suz.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective toJ toJ_surjective hcard (by rw [card_J])
  exact ⟨suzEquivJ.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Suz ≃* SporadicName.Suz.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Suz.finite_card_le.1
    Presentation.Suz.finite_card_le.2

end CFSG.Sporadic.Bridge.Suz
