module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Vol2.Ch5StatementsDS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_2_6_trC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
    (∃ L1' L2' : Subgroup G, ((L1' = L ∧ L2' = L₂) ∨ (L1' = L₂ ∧ L2' = L)) ∧
      (centerOf (sec52S M H) ≤ Subgroup.centralizer (L : Set G) ∨
          centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G) →
        centerOf (sec52S M H) ≤ Subgroup.centralizer (L1' : Set G)) ∧
      F112ListA L1' L2' (sec52S M H) ∧ F112Second L1' L2' (sec52S M H)) →
      L₂ = oTwoUpper H ∧ oTwoUpper H = perfectCore (sec52G2 M H D L₂) ∧
      pCoreOf 2 (sec52G1 M L H B L₂) = pCoreOf 2 L ∧
      pCoreOf 2 (sec52G2 M H D L₂) = pCoreOf 2 (oTwoUpper H) ∧
      Cases5_2_6 (sec52Alpha M L H B D L₂) L (oTwoUpper H) n ∧
      pCoreOf 2 (oTwoUpper H ⊔ T) = pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) ∧
      ((sec52S M H ≤ L ∧ sec52S M H ≤ oTwoUpper H ∧
          pCoreOf 2 (L ⊔ sec52S M H) = pCoreOf 2 L ∧
          pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) = pCoreOf 2 (oTwoUpper H)) ∨
        (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧ IsU4ExtTwo m (sec52Alpha M L H B D L₂) ∧
          ∃ t : G, orderOf t = 2 ∧ t ∉ pCoreOf 2 (oTwoUpper H) ∧
            pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) =
              pCoreOf 2 (oTwoUpper H) ⊔ Subgroup.zpowers t ∧
            ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
              ∃ P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F),
                IsMaxParabolic2 ⊤ P ∧
                Nonempty (↥(oTwoUpper H ⊓ Subgroup.centralizer ({t} : Set G)) ≃*
                  ↥(perfectCore P))))

end CFSG.Quasithin.H13
