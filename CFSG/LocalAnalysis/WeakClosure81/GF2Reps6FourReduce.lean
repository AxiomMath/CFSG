module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourCore
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6QuotRep
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

theorem inner_of_fourFacts_of_rep {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ρ : Q →* MulAut V) (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hL : CFSG.Open.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    (hX : FourFacts (↥L ⧸ center ↥L))
    (hAL : A ≤ normalizer (L : Set Q)) (hA4 : Nat.card A = 4) (hA2 : ∀ a ∈ A, a * a = 1)
    (hq : CFSG.LocalAnalysis.WeakClosure81.IsQuadraticOn ρ A)
    (hAC : A ⊓ centralizer (L : Set Q) = ⊥) :
    ∀ a ∈ A, ∃ l ∈ L, a * l⁻¹ ∈ centralizer (L : Set Q) := by
  obtain ⟨W, _, _, L', A', hW, hL', hZ', ⟨e⟩, hAL', hA4', hA2', hA', hAC', hfix', htr⟩ :=
    exists_quot_of_rep hV ρ hρ hL hZ hAL hA4 hA2 hq hAC
  exact htr (inner_of_fourFacts hW hL' hZ' (hX.of_mulEquiv e) hAL' hA4' hA2' hA' hAC' hfix')

end CFSG.LocalAnalysis.WeakClosure81.Asch6

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)

theorem asch6_5Four_of_facts
    (h : ∀ (Y : Type) [Group Y], (LieModel Y .PSL 3 2 2 ∨ LieModel Y .PSU 3 2 2) →
      Asch6.FourFacts Y) :
    Asch6_5Four := by
  intro Q _ _ V _ _ hV ρ hρ L A hL hZ hAL hA4 hA2 hquad hAC Y _ hcase hcover
  have hA2' : ∀ a ∈ A, a * a = 1 := fun a ha => by
    simpa [pow_two] using hA2.2 a ha
  obtain ⟨-, ⟨e⟩⟩ := hcover
  exact Asch6.inner_of_fourFacts_of_rep hV ρ hρ hL.2.2 hZ ((h Y hcase).of_mulEquiv e.symm) hAL
    hA4 hA2' hquad hAC

end CFSG.LocalAnalysis.WeakClosure81

end
