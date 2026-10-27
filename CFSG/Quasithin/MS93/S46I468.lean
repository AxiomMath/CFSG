module

public import CFSG.Quasithin.MS93.S46Stmt

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def S468 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      ∀ g ∈ stab (puAmalgam c.pu.le) α,
        g ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) →
        (∀ z ∈ ZM (puAmalgam c.pu.le) α, ⁅z, g⁆ ∈ ZH _ β) → Odd (orderOf g) →
          ∀ x ∈ Vv (puAmalgam c.pu.le) β, ∀ v ∈ Vv (puAmalgam c.pu.le) α,
            ⁅⁅x, g⁆, v⁆ ∈ stabCenter _ α

@[expose] def S468Cfg {G : Type} [Group G] [Finite G] (M T L : Subgroup G) {F : Type} [Field F]
    [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  ∀ (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      ∀ g ∈ stab (puAmalgam c.pu.le) α,
        g ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) →
        (∀ z ∈ ZM (puAmalgam c.pu.le) α, ⁅z, g⁆ ∈ ZH _ β) → Odd (orderOf g) →
          ∀ x ∈ Vv (puAmalgam c.pu.le) β, ∀ v ∈ Vv (puAmalgam c.pu.le) α,
            ⁅⁅x, g⁆, v⁆ ∈ stabCenter _ α

end CFSG.Quasithin.MS93.S46
