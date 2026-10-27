module

public import CFSG.Quasithin.MS93.S46Stmt

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Layer

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F] [Fintype F]

structure LastLayer (K Q U Z V : Subgroup 𝔾) (ψ : ↥K →* ↥(StatedSL 3 F)) (W : Subgroup 𝔾) :
    Prop where
  le : W ≤ V
  dual : IsSumOfNaturalModulesVia K W Z ψ true 1
  off : ∃ A : Subgroup 𝔾, A ≤ K ∧ (∀ a ∈ A, a ^ 2 ∈ Q) ∧ (∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ Q) ∧
    Fintype.card F ≤ Q.relIndex A ∧ U.relIndex (⁅W, A⁆ ⊔ U) ≤ Fintype.card F

end Layer

@[expose] def I46T : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → ∃ ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F),
      Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1 ∧
      ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ≤ Vv _ α ∧
      ∃ V₀ V₁ : Subgroup (puAmalgam c.pu.le).Universal,
        LastLayer (stab _ α) (Qv _ α) (Uloc c.pu.le L α) (ZM _ α) (Vv _ α) ψ V₀ ∧
        LastLayer (stab _ α) (Qv _ α) (Uloc c.pu.le L α) (ZM _ α) (Vv _ α) ψ V₁ ∧
        V₀ ⊓ V₁ = ZM _ α ∧ Vv _ α ≤ V₀ ⊔ V₁ ⊔ centerOf (Vv _ α)

@[expose] def I46TCfg {G : Type} [Group G] [Finite G] (M T L : Subgroup G) {F : Type} [Field F]
    [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  ∀ (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → ∃ ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F),
      Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1 ∧
      ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ≤ Vv _ α ∧
      ∃ V₀ V₁ : Subgroup (puAmalgam c.pu.le).Universal,
        LastLayer (stab _ α) (Qv _ α) (Uloc c.pu.le L α) (ZM _ α) (Vv _ α) ψ V₀ ∧
        LastLayer (stab _ α) (Qv _ α) (Uloc c.pu.le L α) (ZM _ α) (Vv _ α) ψ V₁ ∧
        V₀ ⊓ V₁ = ZM _ α ∧ Vv _ α ≤ V₀ ⊔ V₁ ⊔ centerOf (Vv _ α)

end CFSG.Quasithin.MS93.S46
