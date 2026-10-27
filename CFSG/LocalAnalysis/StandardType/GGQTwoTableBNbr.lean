module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def ggBarCentralizer {G : Type} [Group G] [Finite G] (p : ℕ) (Bs K : Subgroup G) :
    Set G :=
  {b | b ∈ Bs ∧ b ∈ Subgroup.normalizer (K : Set G) ∧
    (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K}

structure GGQ2NbrDatum (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G] (Bs K : Subgroup G)
    where
  Λ : Type
  [instFintype : Fintype Λ]
  [instDecEq : DecidableEq Λ]
  coxeter : CoxeterMatrix Λ
  cartan : Matrix Λ Λ ℤ
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod p) V]
  model : Additive ↥Bs ≃+ V
  simple : Λ → MulAut ↥Bs
  coroot : Λ → V
  root : Λ → Module.Dual (ZMod p) V
  isWeyl : GGIsWeylMatrix coxeter
  isCartan : GGIntCartan coxeter cartan
  pairing : ∀ i j, root i (coroot j) = (cartan i j : ZMod p)
  simple_apply : ∀ i w, ggLin (p := p) model (simple i) w = w - root i w • coroot i
  automizer_K : ggAutomizer K Bs = Subgroup.closure (Set.range simple)
  fixed_ZK : ∀ b : ↥Bs, model (Additive.ofMul b) ∈
    ggFixedSubmodule (p := p) model (ggAutomizer K Bs) ↔ (b : G) ∈ ggBarCentralizer p Bs K

attribute [instance] GGQ2NbrDatum.instFintype GGQ2NbrDatum.instDecEq
  GGQ2NbrDatum.instAddCommGroup GGQ2NbrDatum.instModule

@[expose] def GGQ2TableBNbr : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
      ∀ [Fact p.Prime] {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
        ∃ M : GGQ2NbrDatum p Bs K, 3 ≤ Fintype.card M.Λ

end CFSG.StandardType

end
