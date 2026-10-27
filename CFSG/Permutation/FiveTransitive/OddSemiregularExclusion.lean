module

public import CFSG.Permutation.FiveTransitive.OddSemiregularDiagramConsumer
public import CFSG.Permutation.FiveTransitive.OyamaFiveFixerTransitive

public section

namespace CFSG

namespace FiveTransitive.OddSemiregularExclusion

open MulAction OyamaMinimalOrbitDescent

theorem contradiction
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X)) (e : Fin 5 ↪ X)
    (S : Sylow 2 (stabilizer G e))
    (hfree : ∀ q : G, q ∈ ambientSylow e S → q ≠ 1 →
      ∀ x : X, x ∉ Set.range e → q • x ≠ x) : False := by
  apply OddSemiregularDiagramConsumer.contradiction_of_diagram
    X G hcard h5 hnotAlt hodd e S hfree
  intro a _ _ haa hafix hbound _ hseed _
  apply OyamaFiveFixerTransitive.fixer_transitive
    (by rw [Nat.card_eq_fintype_card]; omega) ?_ ?_ a haa hafix
  · intro s hs K hK hpres
    obtain ⟨b, _, hbne, hbb, _, hbfix, hbcomm⟩ := hseed s hs K hK hpres
    exact ⟨b, hbb, hbne, hbfix, fun k hk => (hbcomm k hk).symm.eq⟩
  · intro g hgg hgne
    exact hbound g (orderOf_eq_prime (by simpa only [pow_two] using hgg) hgne)

end FiveTransitive.OddSemiregularExclusion

end CFSG
