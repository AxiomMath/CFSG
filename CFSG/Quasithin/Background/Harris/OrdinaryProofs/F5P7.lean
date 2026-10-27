module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.F5Atom
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.F5Setup

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Background.Harris.KFact2d

variable {X : Type} [Group X]

@[expose] def CenMax (K T : Subgroup X) : Prop :=
  ∀ B : Subgroup X, T ⊓ K ≤ B → B ≤ cenZ K (T ⊓ K) →
    B = T ⊓ K ∨ B = cenZ K (T ⊓ K)

theorem maximal_of_cenMax {K T M : Subgroup X} [K.Normal] (hsup : K ⊔ T = ⊤)
    (hM : M ⊓ K = cenZ K (T ⊓ K)) (hC : CenMax K T) :
    ∀ B : Subgroup X, T ≤ B → B ≤ M → B = T ∨ B = M :=
  maximal_of_inf_maximal hsup (by rw [hM]; exact hC)

theorem V_le_pCoreOf_of_cenMax [Finite X] {K T M V : Subgroup X} [K.Normal]
    (hsup : K ⊔ T = ⊤) (hTM : T ≤ M) (hM : M ⊓ K = cenZ K (T ⊓ K)) (hC : CenMax K T)
    (hVT : V ≤ T) (hV : IsElemAbelian 2 V) (hA : AtomCond T M V) : V ≤ pCoreOf 2 M :=
  V_le_pCoreOf_of_maximal hTM hVT hV (maximal_of_cenMax hsup hM hC) hA

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
