module

public import CFSG.LocalAnalysis.StandardType.GGKGAF4Defs
public import CFSG.LocalAnalysis.StandardType.GGKGAF4AutCard
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace KGA

theorem ggF4_basics_label
    {f : ℕ} :
    LargeEvenLabelAll ⟨.F4, 4, f⟩ fun R _ I _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ GGHasLabel ⟨.F4, 4, f⟩ R ∧
        ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r := by
  intro Q hQ
  obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
  letI : Field K := hField
  letI : Finite K := hFinite
  have hsimple : IsSimpleGroup (TableBF4.RecipeGroup K) := by
    haveI : IsSimpleGroup (AdjointQuotient .F4 K) :=
      CFSG.LieType.Simplicity.isSimpleGroup_adjointQuotient_f4 K
    obtain ⟨eR⟩ := centerQuot_chevGroup_equiv K .F4
    exact eR.isSimpleGroup
  have hnab : ∃ a b : TableBF4.RecipeGroup K, a * b ≠ b * a := by
    haveI : IsSimpleGroup (TableBF4.RecipeGroup K) := hsimple
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (1 : TableBF4.RecipeGroup K)
    have hxc : x ∈ Subgroup.center (TableBF4.RecipeGroup K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact h g x
    rw [TableBF4.center_recipeGroup_eq_bot K, Subgroup.mem_bot] at hxc
    exact hx hxc
  have hlabel : GGHasLabel ⟨.F4, 4, f⟩ (TableBF4.RecipeGroup K) :=
    ⟨K, hField, hFinite, hK, ⟨MulEquiv.refl _⟩⟩
  have hinn : ∀ φ ∈ TableBF4.RecipeID K, ∃ r : TableBF4.RecipeGroup K, φ = MulAut.conj r := by
    intro φ hφ
    obtain ⟨r, hr⟩ := TableBF4.idImage_subset_inn K hφ
    exact ⟨r, hr.symm⟩
  exact ⟨K, hField, hFinite, hK, hQ', hsimple, hnab, hlabel, hinn⟩

theorem ggF4_autOrder_label
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    LargeEvenLabelAll ⟨.F4, 4, f⟩ fun R _ _ _ => GGF4AutOrderAt p R := by
  intro Q hQ
  obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hField, hFinite, hK, hQ', ?_⟩
  intro E hE hr
  let e := TableBF4.recipeEquiv K
  let E' := E.map e.toMonoidHom
  have hE' : IsElemAbelian p E' := TableB.isElemAbelian_map hE e.toMonoidHom
  have hcardE : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective e.injective
  have hr' : p ^ 4 ≤ Nat.card E' := hr.trans hcardE.ge
  have hcard' : Nat.card E' = p ^ 4 := F4AutWeyl.card_eq_pow_four_of_le hp hp2 hE' hr'
  have h1152' : Nat.card (ggAutomizer ⊤ E') = 1152 :=
    ggAutomizer_adjointF4_card_eq_of_card hp hp2 hE' hcard'
  refine ⟨hcardE.symm.trans hcard', ?_⟩
  have hmap := F4AutWeyl.ggAutomizer_map_eq e.injective ⊤ E
    (show E.map e.toMonoidHom = E' from rfl)
  rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
  have hcardAut : Nat.card (ggAutomizer ⊤ E') = Nat.card (ggAutomizer ⊤ E) := by
    rw [hmap]
    exact Subgroup.card_map_of_injective (MulAut.congr _).injective
  exact hcardAut.symm.trans h1152'

end KGA

end CFSG.StandardType

end
