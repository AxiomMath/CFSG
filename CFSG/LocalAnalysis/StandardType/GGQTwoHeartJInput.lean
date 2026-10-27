module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.ClassicalInvolution.RouteD.Root
public import CFSG.ClassicalInvolution.RouteD.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2LDatum.rootForm {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) (a : M.Λ → ℤ) : Module.Dual (ZMod p) M.V :=
  ∑ i, (a i : ZMod p) • M.root i

@[expose] def GGQ2LDatum.phiGraph {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) (yV : M.V) :
    SimpleGraph {a : M.Λ → ℤ // CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ∧
      M.rootForm a yV = 0} :=
  SimpleGraph.fromRel fun a b => (∑ i, ∑ j, a.1 i * M.cartan i j * b.1 j) ≠ 0

@[expose] def GGQ2HeartJInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ∀ [Fact p.Prime] {labL : LargeEvenLabel},
      labL.tag = .twE6 → LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) →
      ∀ M : GGQ2LDatum p Bs L x, GGQ2LabelWeyl labL M.coxeter → M.ShapeB →
        ∀ yB : ↥Bs, (yB : G) ∈ D → (yB : G) ∉ Subgroup.zpowers x →
          ∃ c : (M.phiGraph (M.model (Additive.ofMul yB))).ConnectedComponent,
            6 < Nat.card c.supp ∧
            ∀ b : ↥Bs, (∀ j ∈ J, (b : G) * j = j * (b : G)) ↔
              ∀ a : ↥c.supp, M.rootForm a.1.1 (M.model (Additive.ofMul b)) = 0

@[expose] def GGQ2HeartJCentralizes : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ∀ [Fact p.Prime] {labL : LargeEvenLabel},
      labL.tag = .twE6 → LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) →
      ∀ M : GGQ2LDatum p Bs L x, GGQ2LabelWeyl labL M.coxeter → M.ShapeB →
        ∀ yB : ↥Bs, (yB : G) ∈ D → (yB : G) ∉ Subgroup.zpowers x →
          ∃ c : (M.phiGraph (M.model (Additive.ofMul yB))).ConnectedComponent,
            6 < Nat.card c.supp ∧
            ∀ b : ↥Bs, (∀ j ∈ J, (b : G) * j = j * (b : G)) →
              ∀ a : ↥c.supp, M.rootForm a.1.1 (M.model (Additive.ofMul b)) = 0

end CFSG.StandardType

end
