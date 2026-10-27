module

public import CFSG.Quasithin.MS93.S46Stmt
public import CFSG.Quasithin.MS93.S4ASL3

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def KC4612Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α β γ : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
    (puAmalgam c.pu.le).treeGraph.Adj β γ → ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α →
    ∀ ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F), Function.Surjective ψ →
      IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1 →
      natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0 →
        Fintype.card F = 2 → ∀ k : ↥(stab (puAmalgam c.pu.le) α),
          toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
            ∀ z ∈ ZM (puAmalgam c.pu.le) γ,
              ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α

@[expose] def KC4612TwoCfg {G : Type} [Group G] [Finite G] (M T L : Subgroup G) {F : Type}
    [Field F] [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  ∀ (c : Hyp46 M T L φ) (α β γ : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
    (puAmalgam c.pu.le).treeGraph.Adj β γ → ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α →
    ∀ ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F), Function.Surjective ψ →
      IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1 →
      natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0 →
        Fintype.card F = 2 → ∀ k : ↥(stab (puAmalgam c.pu.le) α),
          toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
            ∀ z ∈ ZM (puAmalgam c.pu.le) γ,
              ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α

end CFSG.Quasithin.MS93.S46
