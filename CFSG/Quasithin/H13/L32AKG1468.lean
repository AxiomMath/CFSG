module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def KG1468Ident : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X),
    (Ch1.IsL34OrG24 X ∧ orderOf x = 2) ∨
      ((∃ s : TauCeti.SporadicName, Ch1.IsLemma115SporadicName s ∧ s ≠ .Ru ∧
          Nonempty (X ≃* NativeSporadic.Carrier s)) ∧
        IsTwoCentralInvolution (⊤ : Subgroup X) x) →
    ¬ (Nonempty (↥(oTwoUpper (Subgroup.centralizer ({x} : Set X))) ⧸
          CFSG.pCore 2 ↥(oTwoUpper (Subgroup.centralizer ({x} : Set X))) ≃*
            alternatingGroup (Fin 5)) ∧
      ∃ A : Subgroup X, A ≤ pCoreOf 2 (oTwoUpper (Subgroup.centralizer ({x} : Set X))) ∧
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
        oTwoUpper (Subgroup.centralizer ({x} : Set X)) ≤ Subgroup.normalizer (A : Set X) ∧
        16 ≤ (A ⊓ Subgroup.centralizer
          (pCoreOf 2 (oTwoUpper (Subgroup.centralizer ({x} : Set X))) : Set X)).relIndex A)

end CFSG.Quasithin.H13
