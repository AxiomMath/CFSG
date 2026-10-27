module

public import CFSG.Quasithin.H13.GoldschmidtI51A3Plane
public import CFSG.Quasithin.H13.GoldschmidtI51A3Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6 CFSG.Blueprint

theorem lieModel_psl42_of_mulEquiv_GL {G : Type} [Group G] (e : G ≃* GL (Fin 4) (ZMod 2)) :
    LieModel G .PSL 4 2 1 := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 4 2 1 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  refine Or.inl ⟨by decide, hadm, ZMod 2, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one], ?_⟩
  exact ⟨((e.trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm).trans
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
      (CFSG.QuasithinUnique.Setup.Family.scalars_zmod_two 4).symm))).trans
    (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 4 (ZMod 2))⟩

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

def pgData (hD : IsDSystem .A3 Gs) : PGData G (G ⧸ Gs 0) where
  Ln := Ln Gs
  swap12 := fun {_ _ _} h => Ln_swap12 h
  swap23 := fun {_ _ _} h => Ln_swap23 h
  smul := fun g {_ _ _} h => Ln_smul g h
  third := fun {_ _} hxy => Ln_exists hD hxy
  pl := Pl Gs
  pl_closed := fun {_ _ _} h hx hy => Pl_closed hD h hx hy
  pl_meet := fun {_ _ _} h => Pl_meet hD h
  pl_ne := exists_not_mem_Pl hD
  trans := inferInstance
  faith := fun _ hg => faithful_A3 hD hg

theorem stmtI_5_1_A3 (hD : IsDSystem .A3 Gs) : LieModel G .PSL 4 2 1 := by
  obtain ⟨e⟩ := exists_mulEquiv_GL (pgData hD) (card_Omega_A3 hD) (card_G_ge_A3 hD)
  exact lieModel_psl42_of_mulEquiv_GL e

end CFSG.Quasithin.H13.I51
