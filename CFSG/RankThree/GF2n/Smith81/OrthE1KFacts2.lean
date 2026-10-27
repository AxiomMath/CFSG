module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

open scoped Matrix commutatorElement
open CFSG.Open

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.KFacts

open CFSG.RankThree.GF2n.Smith81.Smith23E1 CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Stroth80

@[expose] def siegelRadical (K : Type) [Field K] : Subgroup ↥(StatedSp 2 K) :=
  Subgroup.closure {g | ∃ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S ∧
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.fromBlocks 1 S 0 1}

@[expose] def WalterListLargeSylowStatement : Prop :=
  ∀ (D : Type) [Group D] [Finite D], WalterList D → ∀ P : Sylow 2 D, 16 ≤ Nat.card P →
    ∀ i : D, i * i = 1 → i ≠ 1 → IsPGroup 2 ↥(Subgroup.centralizer ({i} : Set D))

@[expose] def CaseASylowStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    E1CaseA M Q B t →
    ∃ S : Subgroup G, Q ≤ S ∧ S ≤ E1Dpre M Q B t ∧ (∀ s ∈ S, ⁅s, t⁆ ∈ Q) ∧
      QuotSat S Q (fun W _ => IsPGroup 2 W) ∧ ¬ 2 ∣ S.relIndex (E1Dpre M Q B t)

@[expose] def CaseASylowAbelianStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), E1Hyp M Q Z B t →
    E1CaseA M Q B t → (∃ x ∈ E1Xpre M Q B t, x ∈ E1Dpre M Q B t ∧ x ∉ Q) →
    ∀ S : Subgroup G, Q ≤ S → S ≤ E1Dpre M Q B t → (∀ s ∈ S, ⁅s, t⁆ ∈ Q) →
      QuotSat S Q (fun W _ => IsPGroup 2 W) → ¬ 2 ∣ S.relIndex (E1Dpre M Q B t) →
      ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ Q

end CFSG.RankThree.GF2n.Smith81.Smith23E1.KFacts
