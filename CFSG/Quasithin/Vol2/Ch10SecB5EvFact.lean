module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Fact10_2_5Lk2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T X : Subgroup G) (k : ℕ), (k = 4 ∨ k = 5) →
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL k 2 1 →
    IsPGroup 2 T → T ≤ Subgroup.normalizer (K : Set G) → IsSylowTwoOf (T ⊓ K) K →
    Nonempty (↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T) ≃*
      MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))) →
    X ≤ K → T ≤ Subgroup.normalizer (X : Set G) → oTwoUpper X = X →
    (pCoreOf 2 X).relIndex X = 9 → (∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) →
    (∀ g ∈ Subgroup.normalizer (K : Set G),
      (pCoreOf 2 (X ⊔ T ⊓ K)).map (MulAut.conj g).toMonoidHom ≤ T ⊓ K →
        (pCoreOf 2 (X ⊔ T ⊓ K)).map (MulAut.conj g).toMonoidHom = pCoreOf 2 (X ⊔ T ⊓ K)) ∧
      ∀ g ∈ K ⊓ Subgroup.normalizer (pCoreOf 2 (X ⊔ T ⊓ K) : Set G), orderOf g = 3 → g ∈ X

end CFSG.Quasithin.Vol2.Ch10.SecB
