module

public import CFSG.RankThree.GF2n.Tim79aCitedAS
public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

instance mbarNormal (M : Subgroup G) : ((inSubgroup (pCore 2) M).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (inSubgroup_pCore_two M).2.1).2
    (inSubgroup_pCore_two M).2.2

abbrev Mbar (M : Subgroup G) : Type := ↥M ⧸ (inSubgroup (pCore 2) M).subgroupOf M

@[expose] def RbarM (M V H : Subgroup G) : Subgroup (Mbar M) :=
  ((xOf V H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf M).map
    (QuotientGroup.mk' ((inSubgroup (pCore 2) M).subgroupOf M))

structure BigEndHyp (M V Q P H : Subgroup G) : Prop where
  setup : Sec23Setup M V Q P H
  q_big : 4 ≤ qBar V H
  three : Sec23Three V H
  centre : CentreClause V H
  tilde : Sec24bTilde V H P
  concl : Sec25Concl V H P
  module : Nat.card ↥(V ⊓ wOf V H) = qBar V H

@[expose] def BigNormalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Subgroup.normalClosure (RbarM M V H : Set (Mbar M)) = RbarM M V H → False

@[expose] def BigM12Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    NativeSporadic.IsSporadic ↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) .M12 → False

@[expose] def BigHJStatement : Prop :=
  AschbacherHJRepresentationStatement →
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    NativeSporadic.IsSporadic ↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) .J2 → False

@[expose] def BigA9Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Nonempty (↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) ≃*
      alternatingGroup (Fin 9)) → False

@[expose] def BigHJDataStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    NativeSporadic.IsSporadic ↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) .J2 →
    ∃ ρ : NativeSporadic.J2 →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2), Function.Injective ρ

theorem bigHJStatement_of_data (hD : BigHJDataStatement) : BigHJStatement := by
  intro hHJ G _ _ M V Q P H hH hJ
  obtain ⟨ρ, hρ⟩ := hD G M V Q P H hH hJ
  have := hHJ 8 ρ hρ
  omega

@[expose] def BigA9DataStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Nonempty (↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) ≃*
      alternatingGroup (Fin 9)) →
    ∃ (L U A : Type) (_ : Group L) (_ : AddCommGroup U) (_ : Module (ZMod 2) U)
      (_ : FiniteDimensional (ZMod 2) U) (_ : AddCommGroup A) (_ : Module (ZMod 2) A)
      (_ : FiniteDimensional (ZMod 2) A) (_ : L ≃* alternatingGroup (Fin 9))
      (ρ : Representation (ZMod 2) L U) (ρA : Representation (ZMod 2) L A)
      (κ : U →ₗ[ZMod 2] U →ₗ[ZMod 2] A), Function.Injective ρ ∧
      Module.finrank (ZMod 2) U = 8 ∧ Module.finrank (ZMod 2) A = 2 ∧
      (∀ (g : L) (x y : U), κ (ρ g x) (ρ g y) = ρA g (κ x y)) ∧
      (∀ l : Module.Dual (ZMod 2) A, (∀ x y, l (κ x y) = 0) → l = 0)

end CFSG.RankThree.GF2n.Tim79a
