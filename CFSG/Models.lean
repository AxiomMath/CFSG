module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Models

open Assembly.LowTwoRank

@[expose] def NamesTag : TauCeti.LieTypeIndex → StatedLieTag → ℕ → ℕ → Prop
  | .G2 q, .G2, p, f | .F4 q, .F4, p, f | .E6 q, .E6, p, f | .E7 q, .E7, p, f
  | .E8 q, .E8, p, f | .twistedE6 q, .twistedE6, p, f | .trialityD4 q, .trialityD4, p, f =>
      q.p = p ∧ q.exponent = f
  | .suzuki m, .twistedB2, p, f | .reeF4 m, .twistedF4, p, f => p = 2 ∧ f = 2 * m + 1
  | .reeG2 m, .twistedG2, p, f => p = 3 ∧ f = 2 * m + 1
  | .tits, .Tits, p, f => p = 2 ∧ f = 1
  | _, _, _, _ => False

@[expose] def LieModel (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ) : Prop :=
  StatedLieAdmissible t n p f ∧
    (StatedClassicalModel G t n p f ∨
      (n = 0 ∧ ∃ d : TauCeti.ValidLieTypeIndex, NamesTag d.1 t p f ∧ Nonempty (G ≃* d.Group)))

@[expose] def OddLieType (G : Type) [Group G] : Prop :=
  ∃ (t : StatedLieTag) (n p f : ℕ), p ≠ 2 ∧ LieModel G t n p f

@[expose] def EvenLieType (G : Type) [Group G] : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ), LieModel G t n 2 f

@[expose] def SporadicRep (G : Type) [Group G] : Prop :=
  ∃ s : TauCeti.SporadicName, Nonempty (G ≃* s.Group)

@[expose] def IsSporadic (G : Type) [Group G] (s : TauCeti.SporadicName) : Prop :=
  Nonempty (G ≃* s.Group)

end CFSG.Models
