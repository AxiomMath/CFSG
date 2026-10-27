module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Core
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6QuotRep

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

theorem false_of_l3OddPointed_of_rep {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ρ : Q →* MulAut V) (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hL : CFSG.Open.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    {t₀ : ↥L ⧸ center ↥L} (hX : L3OddPointed (↥L ⧸ center ↥L) t₀)
    (hAL : A ≤ normalizer (L : Set Q)) (hA4 : Nat.card A = 4) (hA2 : ∀ a ∈ A, a * a = 1)
    (hq : CFSG.LocalAnalysis.WeakClosure81.IsQuadraticOn ρ A)
    (hAC : A ⊓ centralizer (L : Set Q) = ⊥) : False := by
  obtain ⟨W, _, _, L', A', hW, hL', hZ', ⟨e⟩, hAL', hA4', hA2', hA', hAC', hfix', -⟩ :=
    exists_quot_of_rep hV ρ hρ hL hZ hAL hA4 hA2 hq hAC
  exact false_of_l3OddPointed hW hL' hZ' (hX.of_mulEquiv e) hAL' hA4' hA2' hA' hAC' hfix'

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
