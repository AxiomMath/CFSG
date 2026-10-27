module

public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.AutCyclic
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fixed
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.NearPSolvable

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

theorem signalizerMcBrideHypothesisA_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] {p : ℕ} (e : X ≃* Y) (h : signalizerMcBrideHypothesisA p X) :
    signalizerMcBrideHypothesisA p Y := by
  obtain ⟨hp, hsimple, ⟨a, b, hab⟩, hcop, hcyc, hrest⟩ := h
  refine ⟨hp, e.symm.isSimpleGroup, ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩,
    Nat.card_congr e.toEquiv ▸ hcop, TransportA.isCyclic_of_isPGroup_congr e hcyc, ?_⟩
  rcases hrest with hnear | hfix
  · exact Or.inl (TransportA.nearPSolvable_of_mulEquiv e hnear)
  · refine Or.inr fun f hf => ?_
    obtain ⟨h1, h2, h3⟩ := hfix (MulAut.congr e.symm f) (by rwa [MulEquiv.orderOf_eq])
    exact ⟨TransportA.not_le_normalizer_of_congr e f h1,
      TransportA.fitting_clause_of_congr e f h2, TransportA.eq_one_of_congr e f h3⟩

end CFSG.SignalizerFunctorTheorem
