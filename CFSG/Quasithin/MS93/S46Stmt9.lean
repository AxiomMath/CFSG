module

public import CFSG.Quasithin.MS93.S46Stmt

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def I469 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ≤ Vv _ α ∧
      ⁅Vv (puAmalgam c.pu.le) α, Vv _ α⁆ = Uloc c.pu.le L α ∧
      (∀ g ∈ stab (puAmalgam c.pu.le) α,
        g ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) →
        (∀ z ∈ ZM (puAmalgam c.pu.le) α, ⁅z, g⁆ ∈ ZH _ β) → Odd (orderOf g) →
          ∀ x ∈ Vv (puAmalgam c.pu.le) β, ⁅x, g⁆ ∈ ZH _ β) ∧
      ∀ γ : Vtx (puAmalgam c.pu.le), (puAmalgam c.pu.le).treeGraph.Adj β γ →
        ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α →
          Vv (puAmalgam c.pu.le) α ⊔ Qv _ γ = Qv _ β ∧
          Usup (puAmalgam c.pu.le) γ β = Usup _ α β ∧
          ¬ ZM (puAmalgam c.pu.le) α ≤ Bloc c.pu.le L γ

@[expose] def I469Cfg {G : Type} [Group G] [Finite G] (M T L : Subgroup G) {F : Type} [Field F]
    [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  ∀ (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ≤ Vv _ α ∧
      ⁅Vv (puAmalgam c.pu.le) α, Vv _ α⁆ = Uloc c.pu.le L α ∧
      (∀ g ∈ stab (puAmalgam c.pu.le) α,
        g ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) →
        (∀ z ∈ ZM (puAmalgam c.pu.le) α, ⁅z, g⁆ ∈ ZH _ β) → Odd (orderOf g) →
          ∀ x ∈ Vv (puAmalgam c.pu.le) β, ⁅x, g⁆ ∈ ZH _ β) ∧
      ∀ γ : Vtx (puAmalgam c.pu.le), (puAmalgam c.pu.le).treeGraph.Adj β γ →
        ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α →
          Vv (puAmalgam c.pu.le) α ⊔ Qv _ γ = Qv _ β ∧
          Usup (puAmalgam c.pu.le) γ β = Usup _ α β ∧
          ¬ ZM (puAmalgam c.pu.le) α ≤ Bloc c.pu.le L γ

end CFSG.Quasithin.MS93.S46
