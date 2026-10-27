module

public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_13_lie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D K₁ X Kh₁ : Subgroup G) (n k : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsFieldParam510 T H k →
    quasithinIsCComponent K₁ H → oTwoUpper H = conjClosure K₁ T → InH H X →
    IsHatComp X K₁ Kh₁ → oTwoUpper H < conjClosure Kh₁ T →
    ((SuzukiModel (O2Q (oTwoUpper H)) 2 k ∧ Is2F4 k (O2Q (conjClosure Kh₁ T))) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q (conjClosure Kh₁ T)))) →
      D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G)

@[expose] def Stmt5_1_13_main : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    quasithinIsCComponent K₁ H → oTwoUpper H = conjClosure K₁ T →
    InH H X → IsHatComp X K₁ Kh₁ → oTwoUpper H < conjClosure Kh₁ T →
    ¬ D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
    ((K₁ < oTwoUpper H ∧ LieModel (O2Q K₁) .PSL 2 2 2 ∧
        (IsSporadic .J1 (O2Q Kh₁) ∨
          ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
            IsPSL 2 p 1 (O2Q Kh₁))) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2 ∧ oTwoUpper H < conjClosure Kh₁ T ∧
        ¬ IsLieTypeChar2 (O2Q (conjClosure Kh₁ T)) ∧
        A314Statement (o2Img X T) (o2Img X (oTwoUpper H)) (o2Img X (conjClosure Kh₁ T)))) →
      LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2 ∧ n = 2 ∧ IsA5ModuleSum L V ∧
        conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
        (Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (O2Q (conjClosure Kh₁ T) ≃* NativeSporadic.J2) ∨
          Nonempty (O2Q (conjClosure Kh₁ T) ≃* NativeSporadic.M23)) ∧
        ∀ Kz₁ : Subgroup G,
          IsHatComp (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) K₁ Kz₁ →
            conjClosure Kz₁ T =
                oThreePrimeResidual
                  (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ∧
              (conjClosure Kh₁ T = conjClosure Kz₁ T ∨
                (Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) ∧
                  Nonempty (O2Q (conjClosure Kz₁ T) ≃* NativeSporadic.M23)))

end CFSG.Quasithin.H13
