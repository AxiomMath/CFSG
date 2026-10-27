module

public import CFSG.Quasithin.MS93.S46Stmt

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def I4612 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → ∃ β γ ρ : Vtx (puAmalgam c.pu.le),
      (puAmalgam c.pu.le).treeGraph.Adj α β ∧ (puAmalgam c.pu.le).treeGraph.Adj β γ ∧
      (puAmalgam c.pu.le).treeGraph.Adj β ρ ∧
      ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α ∧
      ¬ ZM (puAmalgam c.pu.le) ρ ≤ Bloc c.pu.le L α ∧
      ∃ Nγ Nρ : Subgroup (puAmalgam c.pu.le).Universal,
        stab (puAmalgam c.pu.le) α ≤
          Subgroup.normalizer (Nγ : Set (puAmalgam c.pu.le).Universal) ∧
        ZM (puAmalgam c.pu.le) α ≤ Nγ ∧ Nγ ≤ Vv _ α ⊓ Qv _ γ ∧
        ¬ Nγ ≤ Bloc c.pu.le L α ∧
        stab (puAmalgam c.pu.le) α ≤
          Subgroup.normalizer (Nρ : Set (puAmalgam c.pu.le).Universal) ∧
        ZM (puAmalgam c.pu.le) α ≤ Nρ ∧ Nρ ≤ Vv _ α ⊓ Qv _ ρ ∧
        ¬ Nρ ≤ Bloc c.pu.le L α ∧
        Nγ ⊓ Nρ ≤ Bloc c.pu.le L α ∧
        (Bloc c.pu.le L α).relIndex (Vv (puAmalgam c.pu.le) α) ≤ Fintype.card F ^ 6

@[expose] def I4612Cfg {G : Type} [Group G] [Finite G] (M T L : Subgroup G) {F : Type}
    [Field F] [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  ∀ (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → ∃ β γ ρ : Vtx (puAmalgam c.pu.le),
      (puAmalgam c.pu.le).treeGraph.Adj α β ∧ (puAmalgam c.pu.le).treeGraph.Adj β γ ∧
      (puAmalgam c.pu.le).treeGraph.Adj β ρ ∧
      ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α ∧
      ¬ ZM (puAmalgam c.pu.le) ρ ≤ Bloc c.pu.le L α ∧
      ∃ Nγ Nρ : Subgroup (puAmalgam c.pu.le).Universal,
        stab (puAmalgam c.pu.le) α ≤
          Subgroup.normalizer (Nγ : Set (puAmalgam c.pu.le).Universal) ∧
        ZM (puAmalgam c.pu.le) α ≤ Nγ ∧ Nγ ≤ Vv _ α ⊓ Qv _ γ ∧
        ¬ Nγ ≤ Bloc c.pu.le L α ∧
        stab (puAmalgam c.pu.le) α ≤
          Subgroup.normalizer (Nρ : Set (puAmalgam c.pu.le).Universal) ∧
        ZM (puAmalgam c.pu.le) α ≤ Nρ ∧ Nρ ≤ Vv _ α ⊓ Qv _ ρ ∧
        ¬ Nρ ≤ Bloc c.pu.le L α ∧
        Nγ ⊓ Nρ ≤ Bloc c.pu.le L α ∧
        (Bloc c.pu.le L α).relIndex (Vv (puAmalgam c.pu.le) α) ≤ Fintype.card F ^ 6

end CFSG.Quasithin.MS93.S46
