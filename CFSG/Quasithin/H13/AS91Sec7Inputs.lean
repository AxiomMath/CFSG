module

public import CFSG.Quasithin.H13.AS91Sec5Tri
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.H13.AS91Sec5More

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction

@[expose] def Stmt5_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ u ∈ c.farP, ∀ p : G ⧸ c.G3, CInc c.G1 c.G3 c.x0 p → CInc c.G1 c.G3 u p → p = c.pi0

@[expose] def Stmt5_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ a ∈ c.ptsP, ∀ m ∈ c.lnsP, ¬ CInc c.G1 c.G2 a m →
      (∀ b, CInc c.G1 c.G2 b m → c.Delta.Adj a b) ∨
        {b | CInc c.G1 c.G2 b m ∧ c.Delta.Adj a b}.ncard = 3

structure Sec7Inputs : Prop where
  lineU : Stmt5_LineU
  gamma2 : Stmt5_Gamma2
  s532 : Stmt5_3_2
  s533 : Stmt5_3_3
  s54 : Stmt5_4
  s55 : Stmt5_5
  s56 : Stmt5_6
  s57 : Stmt5_7

theorem sec7Inputs_of (h2c : Stmt5_2c) (h312 : Stmt3_12) (h532 : Stmt5_3_2) (h533 : Stmt5_3_3)
    (h54 : Stmt5_4) (h56 : Stmt5_6) (h57 : Stmt5_7) : Sec7Inputs :=
  ⟨stmt5_lineU_of_2c h2c, stmt5_gamma2_of_2c h2c, h532, h533, h54, stmt5_5_of h2c h312, h56, h57⟩

end CFSG.Quasithin.H13.AS91
