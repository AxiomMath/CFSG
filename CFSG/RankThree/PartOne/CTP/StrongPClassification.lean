module

public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf)
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeHyp)

@[expose] def StronglyPEmbeddedClassification : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → TheoremThreeHyp ↥S →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ Y : Subgroup H, IsStronglyPEmbedded p Y →
        ∀ P : Subgroup H, IsSylowOf p P ⊤ →
          (∃ E : Subgroup H, E ≤ P ∧ IsElementaryAbelian p ↥E ∧ Nat.card E = p ^ 2) →
          (∃ q : TauCeti.PrimePower, q.p = p ∧ 2 ≤ q.exponent ∧ IsoLie ↥S (.A 1 q) ∧
              IsElementaryAbelian p ↥P ∧ Nat.card P = q.card) ∨
          (∃ q : TauCeti.PrimePower, q.p = p ∧ IsoLie ↥S (.twistedA 2 q) ∧
              (∀ x ∈ P, x ^ p = 1) ∧ ¬ IsMulCommutative ↥P) ∨
          Nonempty (↥S ≃* alternatingGroup (Fin (2 * p))) ∨
          (p = 5 ∧ IsoLie ↥S (.suzuki 2)) ∨
          (p = 5 ∧ IsoLie ↥S .tits) ∨
          (p = 5 ∧ Nonempty (↥S ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group) ∧
              (∀ x ∈ P, x ^ p = 1) ∧ ¬ IsMulCommutative ↥P) ∨
          (p = 5 ∧ Nonempty (↥S ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group)) ∨
          (p = 11 ∧ Nonempty (↥S ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group) ∧
              (∀ x ∈ P, x ^ p = 1) ∧ ¬ IsMulCommutative ↥P)

end CFSG.RankThree.PartOne.CTP
