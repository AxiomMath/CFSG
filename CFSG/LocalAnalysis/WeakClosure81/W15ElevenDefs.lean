module

public import CFSG.LocalAnalysis.WeakClosure81.W15TenCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def tSub15 (M V₀ V U P : Subgroup G) : Subgroup G :=
  P ⊓ F11.CTilde M V₀ V ⊓ centralizer (v1Sub15 V₀ U : Set G)

@[expose] def qSub15 (M V₀ V U H P : Subgroup G) : Subgroup G :=
  pCoreOf 2 (kHull15 V₀ H ⊔ tSub15 M V₀ V U P)

@[expose] def cSub15 (M V₀ V U H P : Subgroup G) : Subgroup G :=
  tSub15 M V₀ V U P ⊓ centralizer (kHull15 V₀ H : Set G)

@[expose] def zOmega15 (Q : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup (fun K _ => CFSG.elemThompsonCenterTorsion K 2) Q

@[expose] def OddCoreShape15 (I Q₀ : Subgroup G) [(I.subgroupOf Q₀).Normal] (p : ℕ) : Prop :=
  Nat.card (↥Q₀ ⧸ I.subgroupOf Q₀) = p ∨
    (Nat.card (↥Q₀ ⧸ I.subgroupOf Q₀) = p ^ 3 ∧ CFSG.IsExtraspecial p (↥Q₀ ⧸ I.subgroupOf Q₀) ∧
      Monoid.exponent (↥Q₀ ⧸ I.subgroupOf Q₀) = p)

@[expose] def W15Ten2b (G : Type) [Group G] [Finite G] : Prop :=
  ∀ M V₀ V U S H P Q₀ : Subgroup G, Std15 G → Cex15 M V₀ V U S → ∀ hP : Hyp1510 V₀ V U S H P,
    ∀ hQ : OddCore15 V₀ U H Q₀, ∃ p : ℕ, p.Prime ∧
      haveI := hQ.normal_subgroupOf hP
      OddCoreShape15 (iHull15 V₀ U H) Q₀ p

structure Cfg1511 (M V₀ V U S H P Q₀ : Subgroup G) (p : ℕ) : Prop where
  std : Std15 G
  inputs : NamedInputs15 G
  w81 : W15Eight1 G
  cex : Cex15 M V₀ V U S
  hyp : Hyp1510 V₀ V U S H P
  odd : OddCore15 V₀ U H Q₀
  prime : p.Prime
  shape : haveI := odd.normal_subgroupOf hyp
    OddCoreShape15 (iHull15 V₀ U H) Q₀ p

namespace Cfg1511

variable {M V₀ V U S H P Q₀ : Subgroup G} {p : ℕ}

theorem normal_subgroupOf (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    ((iHull15 V₀ U H).subgroupOf Q₀).Normal :=
  c.odd.normal_subgroupOf c.hyp

theorem P_le_M (c : Cfg1511 M V₀ V U S H P Q₀ p) : P ≤ M :=
  c.hyp.le_M c.inputs c.std c.cex

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
