module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofThree
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBSpanInput : Prop :=
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
      Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤

@[expose] def GGForkCrossInput : Prop :=
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
      αa (h b) = 0 ∨ αa (h b) = 1

@[expose] def GGForkCrossGe5Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J →
        ∀ [Fact p.Prime], 5 ≤ p →
      ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
      (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
      GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
      LinearIndependent (ZMod p) (ggOptFam ha h) →
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
      ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
      αa (h b) = 0 ∨ αa (h b) = 1

@[expose] def GGForkWeylExtInput : Prop :=
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
      (αa (h b) = 0 → ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
          GGIntCartan M' (ggAttachCartan C c)) ∧
        (αa (h b) = 1 → ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
          GGIntCartan M' (ggAttachCartan C b))

@[expose] def GGForkWeylExtRestInput : Prop :=
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
      (αa (h b) = 0 → ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
          GGIntCartan M' (ggAttachCartan C c)) ∧
        (αa (h b) = 1 → ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
          GGIntCartan M' (ggAttachCartan C b))

theorem ggFork_cross_of_tbSpan (hS : GGTBSpanInput) (G : Type) [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (hC : GGConfig p B Bs x L D J)
    (hO : GGOpAutTrivial p Bs) (hI : GGInnerDiagAll p B Bs x L D J) (hNT : GGNoTransvection p Bs)
    (y : G) (K : Subgroup G) (hN : GGNbr p B x D J y K) (hR : GGReflGenerated p (ggAutomizer K Bs))
    (hPm : GGScalarsOrWeyl' p B Bs x D J) [Fact p.Prime] (hp3 : p = 3)
    (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ)
    (hM : GGIsWeylMatrix M) (hCM : GGIntCartan M C) (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hK : ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa})) :
    αa (h b) = 0 ∨ αa (h b) = 1 := by
  have hspan := hS G p B Bs x L D J hC hO hI hNT y K hN hR hPm Λ M C V ι φ φa h α ha αa b c
    hM hCM hF hlin hlina hind hL hK
  have hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs := fun i =>
    mem_ggInduced_top_of_mem_ggAutomizer (H := L)
      (by rw [hL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hφa : φa ∈ ggInduced ⊤ Bs :=
    mem_ggInduced_top_of_mem_ggAutomizer (H := K)
      (by rw [hK]; exact Subgroup.subset_closure (Or.inr rfl))
  exact ggFork_cross_mem_of_p_three hp3 hNT ι hF hφ hφa hlin hlina hind hspan

theorem ggForkCrossInput_of_split (hS : GGTBSpanInput) (h5 : GGForkCrossGe5Input) :
    GGForkCrossInput := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ Λ _ _ M C V _ _ ι φ φa h α ha αa b c hM
    hCM hF hlin hlina hind hL hK
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
  by_cases hp3 : p = 3
  · exact ggFork_cross_of_tbSpan hS G p B Bs x L D J hC hO hI hNT y K hN hR hPm hp3 Λ M C V ι φ
      φa h α ha αa b c hM hCM hF hlin hlina hind hL hK
  · have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    have h2 := hp.two_le
    exact h5 G p B Bs x L D J hC hO hI hNT y K hN hR hPm (by omega) Λ M C V ι φ φa h α ha αa b c
      hM hCM hF hlin hlina hind hL hK

theorem ggCoxeterForkLabelInput_of_cross_ext (hX : GGForkCrossInput)
    (hW : GGForkWeylExtInput) : GGCoxeterForkLabelInput := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ Λ _ _ M C V _ _ ι φ φa h α ha αa b c hM
    hCM hF hlin hlina hind hL hK
  obtain ⟨h0, h1⟩ := hW G p B Bs x L D J hC hO hI hNT y K hN hR hPm Λ M C V ι φ φa h α ha αa b c
    hM hCM hF hlin hlina hind hL hK
  rcases hX G p B Bs x L D J hC hO hI hNT y K hN hR hPm Λ M C V ι φ φa h α ha αa b c hM hCM hF
    hlin hlina hind hL hK with hu | hu
  · exact Or.inl ⟨hu, h0 hu⟩
  · exact Or.inr ⟨hu, h1 hu⟩

theorem ggForkCrossInput_of_forkLabelInput (hd : GGCoxeterForkLabelInput) :
    GGForkCrossInput := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ Λ _ _ M C V _ _ ι φ φa h α ha αa b c hM
    hCM hF hlin hlina hind hL hK
  rcases hd G p B Bs x L D J hC hO hI hNT y K hN hR hPm Λ M C V ι φ φa h α ha αa b c hM hCM hF
    hlin hlina hind hL hK with ⟨hu, -⟩ | ⟨hu, -⟩
  · exact Or.inl hu
  · exact Or.inr hu

theorem ggForkWeylExtInput_of_forkLabelInput (hd : GGCoxeterForkLabelInput) :
    GGForkWeylExtInput := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ Λ _ _ M C V _ _ ι φ φa h α ha αa b c hM
    hCM hF hlin hlina hind hL hK
  rcases hd G p B Bs x L D J hC hO hI hNT y K hN hR hPm Λ M C V ι φ φa h α ha αa b c hM hCM hF
    hlin hlina hind hL hK with ⟨hu, hW⟩ | ⟨hu, hW⟩
  · exact ⟨fun _ => hW, fun h1 => absurd (hu.symm.trans h1) zero_ne_one⟩
  · exact ⟨fun h0 => absurd (h0.symm.trans hu) zero_ne_one, fun _ => hW⟩

theorem ggForkWeylExtInput_of_shapes (hS : GGTBSpanInput) (hR : GGForkWeylExtRestInput) :
    GGForkWeylExtInput := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR' hPm _ Λ _ _ M C V _ _ ι φ φa h α ha αa b c hM
    hCM hF hlin hlina hind hL hK
  by_cases hA : GGForkShapeA C b
  · obtain ⟨m, e, hm, hb, hCe⟩ := hA
    have hc : c = e ⟨m - 1, by omega⟩ :=
      eq_of_forkShapeA (by omega) hb hCe (by rw [hF.bL c hF.ne.symm, ite_eq_left rfl])
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [hc]
      exact exists_weyl_ggAttachCartan_forkShapeA_c hm hCe
    · rw [← hb]
      exact exists_weyl_ggAttachCartan_forkShapeA_b hCe
  by_cases hB : GGForkShapeBCD C b
  · have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
    have hspan := hS G p B Bs x L D J hC hO hI hNT y K hN hR' hPm Λ M C V ι φ φa h α ha αa b c
      hM hCM hF hlin hlina hind hL hK
    have hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs := fun i =>
      mem_ggInduced_top_of_mem_ggAutomizer (H := L)
        (by rw [hL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
    have hφa : φa ∈ ggInduced ⊤ Bs :=
      mem_ggInduced_top_of_mem_ggAutomizer (H := K)
        (by rw [hK]; exact Subgroup.subset_closure (Or.inr rfl))
    exact ⟨fun h0 => absurd h0
      (ggFork_label_ne_zero_of_shapeBCD hp2 hNT ι hF hφ hφa hlin hlina hind hspan hB),
      fun _ => exists_weyl_ggAttachCartan_shapeBCD_b hB⟩
  exact hR G p B Bs x L D J hC hO hI hNT y K hN hR' hPm Λ M C V ι φ φa h α ha αa b c hM hCM hF
    hlin hlina hind hL hK hA hB

theorem ggCoxeterForkLabelInput_of_split (hS : GGTBSpanInput) (h5 : GGForkCrossGe5Input)
    (hR : GGForkWeylExtRestInput) : GGCoxeterForkLabelInput :=
  ggCoxeterForkLabelInput_of_cross_ext (ggForkCrossInput_of_split hS h5)
    (ggForkWeylExtInput_of_shapes hS hR)

end CFSG.StandardType
