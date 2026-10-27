module

public import CFSG.Yardstones.M3ea6b5821535.Definitions
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeCatalog
public import CFSG.Blueprint.NativeSporadicReps
public import CFSG.Open.StatedDefs
public import CFSG.Monster.Visible.AlgebraAction

public section

namespace CFSG.Yardstones.M3ea6b5821535

open CFSG.Blueprint.NativeSporadic in
theorem cfsg_classification_of_yardstones
    (hexhaustiveness : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      Blueprint.Catalog G)
    (hnative_converse : CatNativeConverse)
    (hsimple_transport : CatSimpleCatalogNativeTransport)
    (hrealization :
      (∀ p : ℕ, p.Prime →
        Finite (Multiplicative (ZMod p)) ∧ Nontrivial (Multiplicative (ZMod p)) ∧
          IsSimpleGroup (Multiplicative (ZMod p))) ∧
      (∀ n : ℕ, 5 ≤ n →
        Finite (alternatingGroup (Fin n)) ∧ Nontrivial (alternatingGroup (Fin n)) ∧
          IsSimpleGroup (alternatingGroup (Fin n))) ∧
      (∀ (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
        Assembly.LowTwoRank.StatedLieAdmissible t n p f →
        ∃ (H : Type) (_ : Group H), Finite H ∧ Nontrivial H ∧ IsSimpleGroup H ∧
          Blueprint.LieModel H t n p f) ∧
      (∀ s : TauCeti.SporadicName, Finite (nativeCarrier s) ∧ Nontrivial (nativeCarrier s) ∧
        IsSimpleGroup (nativeCarrier s))) :
    (∀ (G : Type) [Group G],
      Blueprint.NativeCatalog G ↔ Finite G ∧ Nontrivial G ∧ IsSimpleGroup G) ∧
    (∀ p : ℕ, p.Prime →
      Finite (Multiplicative (ZMod p)) ∧ Nontrivial (Multiplicative (ZMod p)) ∧
        IsSimpleGroup (Multiplicative (ZMod p))) ∧
    (∀ n : ℕ, 5 ≤ n →
      Finite (alternatingGroup (Fin n)) ∧ Nontrivial (alternatingGroup (Fin n)) ∧
        IsSimpleGroup (alternatingGroup (Fin n))) ∧
    (∀ (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
      Assembly.LowTwoRank.StatedLieAdmissible t n p f →
      ∃ (H : Type) (_ : Group H), Finite H ∧ Nontrivial H ∧ IsSimpleGroup H ∧
        Blueprint.LieModel H t n p f) ∧
    (∀ s : TauCeti.SporadicName, Finite (nativeCarrier s) ∧ Nontrivial (nativeCarrier s) ∧
      IsSimpleGroup (nativeCarrier s)) :=
  by
    refine ⟨?_, hrealization⟩
    intro G _
    constructor
    · exact hnative_converse G
    · rintro ⟨hfinite, _hnontrivial, hsimple⟩
      letI : Finite G := hfinite
      letI : IsSimpleGroup G := hsimple
      exact hsimple_transport G (hexhaustiveness G)

end CFSG.Yardstones.M3ea6b5821535
