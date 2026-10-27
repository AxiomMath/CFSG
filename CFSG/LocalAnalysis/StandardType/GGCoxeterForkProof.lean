module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDAff

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGCoxeterForkBCDLabelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J → ∀ [Fact p.Prime]
      (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
      (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
      GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
      LinearIndependent (ZMod p) (ggOptFam ha h) →
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
      ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
      GGForkShapeBCD C b →
      (αa (h b) = 0 ∨ αa (h b) = 1) ∧
        (αa (h b) = 0 → Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤)

@[expose] def GGCoxeterForkRestLabelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J → ∀ [Fact p.Prime]
      (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
      (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
      GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
      LinearIndependent (ZMod p) (ggOptFam ha h) →
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
      ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
      ¬ GGForkShapeA C b → ¬ GGForkShapeBCD C b →
      (αa (h b) = 0 ∧ ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
          GGIntCartan M' (ggAttachCartan C c)) ∨
        (αa (h b) = 1 ∧ ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
          GGIntCartan M' (ggAttachCartan C b))

theorem ggCoxeterForkLabelInput_of_inputs (hX : GGTypeACrossLabelInput)
    (hBCD : GGCoxeterForkBCDLabelInput) (hR : GGCoxeterForkRestLabelInput) :
    GGCoxeterForkLabelInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc _ Λ _ _ M C V _ _ ι φ φa h α
    ha αa b c hM hC hF hlin hlina hind hL hK
  by_cases hA : GGForkShapeA C b
  · exact ggForkLabel_of_forkShapeA hX hcfg hOp hID hNT hnbr hsc ι hF hlin hlina hL hK hA
  by_cases hS : GGForkShapeBCD C b
  · have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
    obtain ⟨hu01, hspan⟩ := hBCD G p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc Λ M C V ι φ
      φa h α ha αa b c hM hC hF hlin hlina hind hL hK hS
    have hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs := fun i =>
      mem_ggInduced_top_of_mem_ggAutomizer (H := L)
        (by rw [hL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
    have hφa : φa ∈ ggInduced ⊤ Bs := mem_ggInduced_top_of_mem_ggAutomizer (H := K)
      (by rw [hK]; exact Subgroup.subset_closure (Or.inr rfl))
    have hu : αa (h b) = 1 := hu01.resolve_left fun hu =>
      ggFork_label_ne_zero_of_shapeBCD hp2 hNT ι hF hφ hφa hlin hlina hind (hspan hu) hS hu
    exact Or.inr ⟨hu, exists_weyl_ggAttachCartan_shapeBCD_b hS⟩
  exact hR G p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc Λ M C V ι φ φa h α ha αa b c hM
    hC hF hlin hlina hind hL hK hA hS

theorem ggCoxeterForkRestLabelInput_of_forkLabelInput (hd : GGCoxeterForkLabelInput) :
    GGCoxeterForkRestLabelInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc _ Λ _ _ M C V _ _ ι φ φa h α
    ha αa b c hM hC hF hlin hlina hind hL hK _ _
  exact hd G p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc Λ M C V ι φ φa h α ha αa b c hM
    hC hF hlin hlina hind hL hK

theorem ggCoxeterForkBCDLabelInput_of_forkLabelInput (hd : GGCoxeterForkLabelInput) :
    GGCoxeterForkBCDLabelInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc _ Λ _ _ M C V _ _ ι φ φa h α
    ha αa b c hM hC hF hlin hlina hind hL hK hS
  rcases hd G p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc Λ M C V ι φ φa h α ha αa b c hM
      hC hF hlin hlina hind hL hK with ⟨-, hW⟩ | ⟨hu, -⟩
  · exact absurd hW (not_exists_weyl_ggAttachCartan_shapeBCD_c
      (by rw [hF.bL c hF.ne.symm, ite_eq_left rfl]) hS)
  · exact ⟨Or.inr hu, fun h0 => absurd (h0.symm.trans hu) zero_ne_one⟩

theorem ggCoxeterLabelInput_of_forkInputs (hX : GGTypeACrossLabelInput)
    (hBCD : GGCoxeterForkBCDLabelInput) (hR : GGCoxeterForkRestLabelInput)
    (hR₂ : GGCoxeterLabelResidualInput) : GGCoxeterLabelInput :=
  ggCoxeterLabelInput_of_fork (ggCoxeterForkLabelInput_of_inputs hX hBCD hR) hR₂

theorem span_ggOptFam_eq_top_of_finrank {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type*} [Fintype Λ] {h : Λ → V} {ha : V}
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hrank : Module.finrank (ZMod p) V = Fintype.card Λ + 1) :
    Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤ :=
  hind.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_option, hrank])

end CFSG.StandardType
