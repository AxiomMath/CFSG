module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProofFork
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Data

variable {G : Type} [Group G]

@[expose] def GGCoxeterStdDatum (p : ℕ) [Fact p.Prime] (Bs L K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix (Option Λ))
    (C : Matrix (Option Λ) (Option Λ) ℤ) (V : Type) (_ : AddCommGroup V)
    (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V) (φ : Option Λ → MulAut ↥Bs)
    (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod p) V) (b : Λ),
    GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧ LinearIndependent (ZMod p) h ∧
      (∀ o o', (o, o') ≠ (some b, none) → α o (h o') = (C o o' : ZMod p)) ∧
      C (some b) none = 0 ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none})

@[expose] def GGCoxeterForkDatum (p : ℕ) [Fact p.Prime] (Bs L K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
    GGIsWeylMatrix M ∧ GGIntCartan M C ∧ GGForkPairing C b c h α ha αa ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) ∧
      LinearIndependent (ZMod p) (ggOptFam ha h) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) ∧
      ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa})

end Data

@[expose] def GGCoxeterForkLabelInput : Prop :=
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
      (αa (h b) = 0 ∧ ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
          GGIntCartan M' (ggAttachCartan C c)) ∨
        (αa (h b) = 1 ∧ ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
          GGIntCartan M' (ggAttachCartan C b))

@[expose] def GGCoxeterLabelResidualInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J → ∀ [Fact p.Prime],
      ¬ GGCoxeterForkDatum p Bs L K → ¬ GGCoxeterStdDatum p Bs L K →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)

section Proofs

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

theorem ggWeylReflectionGroup_of_stdDatum (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {L K : Subgroup G} (hS : GGCoxeterStdDatum p Bs L K) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨Λ, _, _, M, C, V, _, _, ι, φ, h, α, b, hM, hC, hlin, hind, hP, hCba, hL, hK⟩ := hS
  have hα : ∀ o, α o (h o) = 2 := by
    intro o
    by_cases ho : (o, o) = (some b, none)
    · exact absurd ((Prod.mk.inj ho).1.symm.trans (Prod.mk.inj ho).2) (Option.some_ne_none b)
    · rw [hP o o ho, hC.1 o]
      simp
  have hφ : ∀ o, φ o ∈ ggInduced ⊤ Bs := by
    rintro (_ | i)
    · exact mem_ggInduced_top_of_mem_ggAutomizer (H := K)
        (by rw [hK]; exact Subgroup.subset_closure (Or.inr rfl))
    · exact mem_ggInduced_top_of_mem_ggAutomizer (H := L)
        (by rw [hL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  exact ggWeylReflectionGroup_sup_of_label_of_isFiniteType hp2 hNT hM hC
    (isFiniteType_of_ggIsWeylMatrixFixed (hM : GGIsWeylMatrixFixed M) hC) φ hφ ι h α hα
    (fun o => ggLin_eq_reflection ι (hα o) (hlin o)) hind b hP hCba hL hK

end Proofs

theorem ggCoxeterLabelInput_of_fork (hF : GGCoxeterForkLabelInput)
    (hR : GGCoxeterLabelResidualInput) : GGCoxeterLabelInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  by_cases hfork : GGCoxeterForkDatum p Bs L K
  · obtain ⟨Λ, _, _, M, C, V, _, _, ι, φ, φa, h, α, ha, αa, b, c, hM, hC, hP, hlin, hlina, hind,
      hL, hK⟩ := hfork
    exact ggWeylReflectionGroup_sup_of_fork hp2 hNT ι hP hlin hlina hind
      (hF G p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc Λ M C V ι φ φa h α ha αa b c hM hC
        hP hlin hlina hind hL hK) hL hK
  · by_cases hstd : GGCoxeterStdDatum p Bs L K
    · exact ggWeylReflectionGroup_of_stdDatum hp2 hNT hstd
    · exact hR G p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc hfork hstd

theorem ggCoxeterLabelResidualInput_of_coxeterLabelInput (hd : GGCoxeterLabelInput) :
    GGCoxeterLabelResidualInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc _ _ _
  exact hd G p B Bs x L D J hcfg hOp hID hNT y K hnbr hrefl hsc

end CFSG.StandardType
