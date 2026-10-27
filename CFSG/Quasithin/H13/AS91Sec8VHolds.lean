module

public import CFSG.Quasithin.H13.AS91Sec8V2
public import CFSG.Quasithin.H13.AS91Sec8V3
public import CFSG.Quasithin.H13.AS91Sec8V4
public import CFSG.Quasithin.H13.AS91Sec5Holds
public import CFSG.Quasithin.H13.AS91Sec5ResM24T

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup MulAction CFSG.Quasithin.Asc94

theorem stmt8_2_3_of_v1
    (hV1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      ∀ θ : ↥(c.G3 ⊓ stabilizer G c.x0) ≃* ↥(c.G3 ⊓ stabilizer G c.x0),
        ∃ (φ : ↥c.G3 ≃* ↥c.G3) (ψ : ↥(stabilizer G c.x0) ≃* ↥(stabilizer G c.x0)),
          autPres c.G3 (c.G3 ⊓ stabilizer G c.x0) φ ∧
          autPres (stabilizer G c.x0) (c.G3 ⊓ stabilizer G c.x0) ψ ∧
          ∀ b : ↥(c.G3 ⊓ stabilizer G c.x0),
            ((θ b : ↥(c.G3 ⊓ stabilizer G c.x0)) : G) = totFun φ (totFun ψ (b : G))) :
    Stmt8_2_3 := by
  intro G _ _ z hJ c y hy hyx
  have hLU : Stmt5_LineU := stmt5_lineU_of_2c stmt5_2c_holds
  have hG2 : Stmt5_Gamma2 := stmt5_gamma2_of_2c stmt5_2c_holds
  obtain ⟨r⟩ := resM24T_holds G z hJ c
  exact ⟨hV1 G z hJ c, Loc49.hypV_v2 hLU hJ c r hy hyx,
    Loc49.hypV_v3 hLU hG2 hJ c r.toResM24 hy hyx, Loc49.hypV_v4 hLU hJ c r.toResM24 hy hyx⟩

end CFSG.Quasithin.H13.AS91
