module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522
public import CFSG.Quasithin.Vol2.Ch5StatementsDS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_2_bot_listC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n 3 → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥ →
    Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3)) →
    ∀ L1' L2' : Subgroup G,
      ((L1' = L₂ ∧ L2' = Dp ⊔ sec52S M H) ∨ (L1' = Dp ⊔ sec52S M H ∧ L2' = L₂)) →
      Hyp111 L1' L2' (sec52S M H) →
      (centerOf (sec52S M H) ≤ Subgroup.centralizer (L₂ : Set G) ∨
          centerOf (sec52S M H) ≤ Subgroup.centralizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) →
        centerOf (sec52S M H) ≤ Subgroup.centralizer (L1' : Set G)) →
      F112ListB L1' L2' (sec52S M H) → F112Second L1' L2' (sec52S M H) → False

end CFSG.Quasithin.H13
