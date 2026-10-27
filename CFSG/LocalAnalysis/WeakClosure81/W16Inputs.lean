module

public import CFSG.LocalAnalysis.WeakClosure81.W16Setup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Fam16 (M U S H : Subgroup G) : Prop :=
  S ≤ H ∧ H ≤ centralizer (U : Set G) ∧ ¬ H ≤ M

@[expose] def Fam16Q (M V₀ U R H : Subgroup G) : Prop :=
  R ≤ H ∧ ¬ H ⊓ centralizer (U : Set G) ≤ M ∧
    ∀ x ∈ conjClosure (U ⊔ V₀) H, ∀ y ∈ conjClosure (U ⊔ V₀) H, x * y = y * x

structure Cfg1620 (M V₀ V U S R H : Subgroup G) (g : G) (B : Subgroup G) : Prop where
  cex : Cex16 M V₀ V U S
  sylow : IsSylowIn 2 R (F11.CTilde M V₀ V)
  S_le : S ≤ R
  mem : Fam16Q M V₀ U R H
  min : ∀ H' : Subgroup G, H' ≤ H → Fam16Q M V₀ U R H' → H' = H
  g_mem : g ∈ H ⊓ centralizer (U : Set G)
  g_not : g ∉ M
  centralizer_eq : ∀ x ∈ conjSubgroup V₀ g, x ≠ 1 → V ⊓ centralizer ({x} : Set G) = U ⊔ V₀
  centralizer_L : V ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) = U
  B_le : B ≤ R
  B_conj : ∃ m ∈ M, B = conjSubgroup (conjSubgroup V₀ g) m
  not_comm : ¬ U ≤ centralizer (B : Set G)
  centralizer_B : ∀ x ∈ B, x ≠ 1 → V ⊓ centralizer ({x} : Set G) = V ⊓ centralizer (B : Set G)
  LK : V ⊔ conjSubgroup V g ⊔ conjClosure (U ⊔ V₀) H ≠ conjClosure V H

@[expose] def W16One (G : Type) [Group G] [Finite G] : Prop :=
  Std15 G → ∀ ⦃M V₀ V U : Subgroup G⦄ (hyp : Hyp15 M V₀ V),
    1 < mBar M V₀ V hyp.h6.elemAbelian → U ≤ V →
      E3.mQuot V (U ⊔ V₀) < mBar M V₀ V hyp.h6.elemAbelian →
        E3.wClos V 0 (M ⊓ centralizer (U : Set G)) ≤ centralizer (V : Set G)

@[expose] def W16Five (G : Type) [Group G] [Finite G] : Prop :=
  Std15 G → ∀ ⦃M V₀ V U S H : Subgroup G⦄, Cex16 M V₀ V U S → Fam16 M U S H →
    ¬ V ≤ pCoreOf 2 H → ∀ g ∈ H, (¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x) →
      V ⊓ conjSubgroup M g = U ⊔ V₀

@[expose] def W16Fifteen (G : Type) [Group G] [Finite G] : Prop :=
  Std15 G → ∀ ⦃M V₀ V U S : Subgroup G⦄, Cex16 M V₀ V U S → E3.wClos V 0 S = V

@[expose] def W16SixteenQ (G : Type) [Group G] [Finite G] : Prop :=
  Std15 G → ∀ ⦃M V₀ V U S R : Subgroup G⦄, Cex16 M V₀ V U S →
    IsSylowIn 2 R (F11.CTilde M V₀ V) → S ≤ R → ∃ H : Subgroup G, Fam16Q M V₀ U R H

end CFSG.LocalAnalysis.WeakClosure81
