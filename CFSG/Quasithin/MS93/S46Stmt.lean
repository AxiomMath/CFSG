module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S4Stmt

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Hyp

variable {G : Type} [Group G] [Finite G]

structure Hyp46 (M T L : Subgroup G) {F : Type} [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) : Prop where
  pu : PUHyp M T L
  min : PUMin M T L
  b4 : critDist (puAmalgam pu.le) = 4
  via : IsSL3FullVia M T L φ

end Hyp

section Offender

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def IsOffenderOn (α : Vtx X) (Bs As : Subgroup X.Universal) : Prop :=
  (∃ ρ, X.treeGraph.Adj α ρ ∧ As ≤ Qv X ρ) ∧ ¬ As ≤ Qv X α ∧
    (∀ a ∈ As, a ^ 2 ∈ Qv X α) ∧ (∀ a ∈ As, ∀ b ∈ As, ⁅a, b⁆ ∈ Qv X α) ∧
    ∃ C₀ : Subgroup X.Universal, Bs ≤ C₀ ∧ C₀ ≤ Vv X α ∧ ⁅C₀, As⁆ ≤ Bs ∧
      C₀.relIndex (Vv X α) ≤ (Qv X α).relIndex As

end Offender

section Items

@[expose] def I461 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → centerOf (Vv _ α) ≤ Bloc c.pu.le L α

@[expose] def I462 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le))
    (As : Subgroup (puAmalgam c.pu.le).Universal), IsMVtx _ α →
    IsOffenderOn _ α (Bloc c.pu.le L α) As → ⁅Vv _ α, Vv _ α⁆ ≤ Uloc c.pu.le L α

@[expose] def I463 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → ⁅Vv _ α, Qv _ α⁆ ≤ centerOf (Vv _ α) ∧ ⁅Vv _ α, Vv _ α⁆ ≤ ZM _ α

@[expose] def I464 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β → Usup _ α β ≤ ZH _ β

@[expose] def I465 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      Nat.card ↥(Usup (puAmalgam c.pu.le) α β) = Fintype.card F ^ 2 ∧
        (ZH _ β).relIndex (ZM _ α) = Fintype.card F ∧ ⁅Vv _ α, Qv _ α⁆ ≤ ZM _ α

@[expose] def I466a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      (Qv _ α).relIndex (Qv _ β) = Fintype.card F ^ 2

@[expose] def I466b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → ¬ ⁅Vv _ α, Vv _ α⁆ ≤ stabCenter _ α

@[expose] def I467 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → Bloc c.pu.le L α = centerOf (Vv _ α)

end Items

end CFSG.Quasithin.MS93.S46
