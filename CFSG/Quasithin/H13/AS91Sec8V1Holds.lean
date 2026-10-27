module

public import CFSG.Quasithin.H13.AS91Sec8VHolds
public import CFSG.Quasithin.H13.AS91Sec8V1Assembly
public import CFSG.Quasithin.H13.AS91Sec8V1Inner
public import CFSG.Quasithin.H13.AS91Sec8V1Alpha
public import CFSG.Quasithin.H13.AS91Sec8V1Beta
public import CFSG.Quasithin.H13.AS91Sec8V1Aut
public import CFSG.Quasithin.H13.AS91Sec8V1Mod
public import CFSG.Quasithin.H13.AS91Sec8V1Coc

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup MulAction CFSG.Quasithin.Asc94

theorem Loc49.hypV_v1
    {G : Type} [Group G] [Finite G] {z : G} (hJ : HypJ4 G z)
    (c : Loc49 G z) :
    ∀ θ : ↥(c.G3 ⊓ stabilizer G c.x0) ≃* ↥(c.G3 ⊓ stabilizer G c.x0),
      ∃ (φ : ↥c.G3 ≃* ↥c.G3) (ψ : ↥(stabilizer G c.x0) ≃* ↥(stabilizer G c.x0)),
        autPres c.G3 (c.G3 ⊓ stabilizer G c.x0) φ ∧
        autPres (stabilizer G c.x0) (c.G3 ⊓ stabilizer G c.x0) ψ ∧
        ∀ b : ↥(c.G3 ⊓ stabilizer G c.x0),
          ((θ b : ↥(c.G3 ⊓ stabilizer G c.x0)) : G) = totFun φ (totFun ψ (b : G)) := by
  have hLU : Stmt5_LineU := stmt5_lineU_of_2c stmt5_2c_holds
  have hG2 : Stmt5_Gamma2 := stmt5_gamma2_of_2c stmt5_2c_holds
  obtain ⟨r₀⟩ := resM24T_holds G z hJ c
  obtain ⟨r, hU⟩ := c.exists_resM24T_sextFin_zero r₀
  exact c.hypV_v1_of_parts r hU (M24G.sextStabCocycle_of_closure M24G.sextStab_eq_closure)
    (fun θ => c.isInnerCocycle_of_aut M24G.sextStabOffender_holds M24G.sextStabAutInner_holds
      M24G.sextStabEndScalar_holds r hU θ)
    (c.hasAlphaTwist hLU hG2 M24G.sextStabEndScalar_holds hJ r hU) (c.hasBetaTwist r hU)

theorem stmt8_2_3_holds :
    Stmt8_2_3 :=
  stmt8_2_3_of_v1 fun _ _ _ _ hJ c => c.hypV_v1 hJ

end CFSG.Quasithin.H13.AS91
