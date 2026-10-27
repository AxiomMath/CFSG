module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

@[expose] def A23NoncyclicCenterFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    A23List S → ∀ P E Z : Subgroup S, IsSylowTwoOf P ⊤ → E ≤ P → IsElemAbelian 2 E →
      Nat.card E = 16 → Z ≤ P ⊓ Subgroup.centralizer (P : Set S) → IsElemAbelian 2 Z →
        Nat.card Z = 4 → IsLieChar2Big S

@[expose] def A23CyclicCenterFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 8)) ∨
      (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL n 2 1) ∨
      ChevalleyExceptionalModel S .trialityD4 2 1 ∨ ReeTitsModel S .Tits 2 1 ∨
      ∃ s : TauCeti.SporadicName,
        (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
          s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
        Nonempty (S ≃* NativeSporadic.Carrier s)) →
    ∀ T : Sylow 2 S, IsCyclic (Subgroup.center ↥(T : Subgroup S))

@[expose] def A23SmallTwoRankFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 7 ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 p f) ∨
          CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 3 p 1 ∨
          CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 3 p 1)) ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 3 2 1 ∨
      Nonempty (S ≃* NativeSporadic.Carrier .J1)) →
    ∀ E : Subgroup S, IsElemAbelian 2 E → Nat.card E ≤ 8

@[expose] def LieCentralIndexFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsLieChar2Big S → ∀ P : Subgroup S, IsSylowTwoOf P ⊤ →
    ∀ x ∈ P, (P ⊓ Subgroup.centralizer ({x} : Set S)).relIndex P ≤ 2 →
      x ∈ Subgroup.centralizer (P : Set S)

end CFSG.Quasithin.H13
