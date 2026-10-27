module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.EmptyFaithful.S1421Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def tU (T : Subgroup G) (u : G) : Subgroup G := T ⊓ Subgroup.centralizer ({u} : Set G)

@[expose] def tZero (T : Subgroup G) (u : G) : Subgroup G :=
  centralizerMod (quasithinOmegaOneCenter T) T (Subgroup.zpowers u)

structure IsInvU (T M H : Subgroup G) (u : G) : Prop where
  mem : u ∈ conjClosure (VZ T M) H
  sylow : IsSylowTwoOf (tU T u) (H ⊓ Subgroup.centralizer ({u} : Set G))
  index_two : (tZero T u).relIndex T = 2
  not_central : u ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G)
  not_central_mul : ∀ t ∈ T, t ∉ tZero T u →
    u * (t * u * t⁻¹) ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G)
  normalizer_eq : Subgroup.normalizer (tZero T u : Set G) ⊓ mcOf T = T

@[expose] def IsI (T M : Subgroup G) (u : G) (I : Subgroup G) : Prop :=
  InH (tU T u) I ∧ ¬ I ≤ mcOf T ∧ ¬ I ≤ M

@[expose] def IsIStar (T M : Subgroup G) (u : G) (I : Subgroup G) : Prop :=
  IsI T M u I ∧ ∀ J : Subgroup G, IsI T M u J → ¬ (T ⊓ I < T ⊓ J)

@[expose] def IsIMin (T M : Subgroup G) (u : G) (I : Subgroup G) : Prop :=
  IsIStar T M u I ∧ ∀ J : Subgroup G, IsIStar T M u J → J ≤ I → J = I

@[expose] def lI (T M I : Subgroup G) : Subgroup G := oTwoUpper (yOfL22 T M ⊓ I)

@[expose] def oTwoPIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  preimageModTwoCore H (CFSG.pCore p (↥H ⧸ CFSG.pCore 2 ↥H))

@[expose] def OddCoreModTwoTrivial (H : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N ≤ H → (N.subgroupOf H).Normal → pCoreOf 2 H ≤ N →
    Odd ((pCoreOf 2 H).relIndex N) → N ≤ pCoreOf 2 H

@[expose] def IsChiefFactorOf (X A B : Subgroup G) : Prop :=
  B < A ∧ X ≤ Subgroup.normalizer (A : Set G) ∧ X ≤ Subgroup.normalizer (B : Set G) ∧
    ∀ C : Subgroup G, B < C → C < A → ¬ X ≤ Subgroup.normalizer (C : Set G)

@[expose] def HasTwoNoncentralChiefFactors (X : Subgroup G) : Prop :=
  ∃ A₁ B₁ A₂ B₂ : Subgroup G, A₂ ≤ pCoreOf 2 X ∧ IsChiefFactorOf X A₁ B₁ ∧
    IsChiefFactorOf X A₂ B₂ ∧ A₁ ≤ B₂ ∧ ¬ ⁅A₁, X⁆ ≤ B₁ ∧ ¬ ⁅A₂, X⁆ ≤ B₂

omit [Finite G] in
theorem le_centralizer_quasithinOmegaOneCenter (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.le_centralizer_iff.mp ((quasithinOmegaOneCenter_le_center T).trans inf_le_right)

omit [Finite G] in
theorem tU_le_tZero (T : Subgroup G) (u : G) : tU T u ≤ tZero T u := by
  intro x hx
  obtain ⟨hxT, hxu⟩ := hx
  refine ⟨hxT, Subgroup.centralizer_le_normalizer _
    (le_centralizer_quasithinOmegaOneCenter T hxT), fun w hw => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hc : Commute u x := (Subgroup.mem_centralizer_iff.mp hxu) u (Set.mem_singleton u)
  have hc' : Commute x (u ^ k) := (hc.zpow_left k).symm
  rw [hc'.eq]
  simp

variable {T M : Subgroup G} {u : G}

omit [Finite G] in
theorem IsIStar.of_le_inf {I J : Subgroup G} (hI : IsIStar T M u I) (hJ : IsI T M u J)
    (hTJ : T ⊓ I ≤ J) : IsIStar T M u J ∧ T ⊓ J = T ⊓ I := by
  have heq : T ⊓ J = T ⊓ I := by
    by_contra hne
    exact hI.2 J hJ (lt_of_le_of_ne (le_inf inf_le_left hTJ) (Ne.symm hne))
  refine ⟨⟨hJ, fun K hK => ?_⟩, heq⟩
  rw [heq]
  exact hI.2 K hK

omit [Finite G] in
theorem IsI.of_le {I J : Subgroup G} (hI : IsI T M u I) (hIJ : I ≤ J) (hJ : pCoreOf 2 J ≠ ⊥) :
    IsI T M u J :=
  ⟨⟨hI.1.1.trans hIJ, hJ⟩, fun h => hI.2.1 (hIJ.trans h), fun h => hI.2.2 (hIJ.trans h)⟩

omit [Finite G] in
theorem IsIStar.of_le {I J : Subgroup G} (hI : IsIStar T M u I) (hIJ : I ≤ J)
    (hJ : pCoreOf 2 J ≠ ⊥) : IsIStar T M u J ∧ T ⊓ J = T ⊓ I :=
  hI.of_le_inf (hI.1.of_le hIJ hJ) (inf_le_right.trans hIJ)

end CFSG.Quasithin
