module

public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy

public section

namespace CFSG

namespace FiveTransitive.TupleSylowConjugacy

open MulAction

theorem exists_transporter
    (G X : Type*) [Group G] [Finite G] [MulAction G X]
    (k : ℕ) (hk : IsMultiplyPretransitive G X k)
    (e f : Fin k ↪ X) (H K : Subgroup G)
    (hH : H = fixingSubgroup G (Set.range e))
    (hK : K = fixingSubgroup G (Set.range f))
    {p : ℕ} [Fact p.Prime] (S : Sylow p H) (T : Sylow p K) :
    ∃ c : G, c • e = f ∧
      ((S : Subgroup H).map H.subtype).map (MulAut.conj c).toMonoidHom =
        (T : Subgroup K).map K.subtype := by
  rw [BaseSylowConjugacy.fixing_range_eq_stabilizer] at hH hK
  subst H
  subst K
  exact StabilizerSylowConjugacy.exists_conjugating_transporter e f
    (isMultiplyPretransitive_iff.mp hk e f) S T

end FiveTransitive.TupleSylowConjugacy

end CFSG
