module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Mc
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt SigmaOne4)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (calNOf)

structure Mz614 (G : Type) [Group G] [Finite G] extends Mc614 G where
  hMS : S.InMSigma
  Z : Subgroup G
  hZ : Mc614.IsZ toMc614 Z

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def H : Subgroup G := centralizer (m.Z : Set G)

@[expose] def A : Subgroup G := m.Z ⊔ m.E

@[expose] noncomputable def L : Subgroup G :=
  CFSG.LocalAnalysis.UniquenessCase.UC22.Opp m.r (inftyOf m.H)

@[expose] def K : Subgroup G := closure {x | ∃ g ∈ m.M, ∃ z ∈ m.Z, x = g * z * g⁻¹}

abbrev Kbar : Type := ↥m.K ⧸ CFSG.pPrimeCore m.r ↥m.K

@[expose] def V : Subgroup G := pCoreOf 2 m.M

@[expose] def C619 : Prop := m.H = m.L ⊔ (m.H ⊓ m.M)

@[expose] def C620 : Prop := m.A ≤ m.Z ⊔ m.L ∧ ¬ m.Z ≤ m.L

@[expose] def C624 : Prop :=
  m.r ≠ 3 → calNOf (m.A ⊔ m.L) = {normalizer (m.L : Set G)}

@[expose] def C629 : Prop := IsSimpleGroup m.Kbar ∧ ∃ a b : m.Kbar, a * b ≠ b * a

@[expose] def C632 : Prop := rankThreeGamma 1 m.r (m.A ⊓ m.L) ≤ m.M

@[expose] def C635 : Prop := 3 < m.r

@[expose] def C636 : Prop :=
  Odd (Nat.card ↥(m.K ⊓ normalizer (m.L : Set G))) ∧
    m.K ⊓ normalizer (m.L : Set G) ≤ centralizer (m.L : Set G)

end Mz614

structure UC6Inputs : Prop where
  r67 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G), S.InMSigma → TheoremCAt S.M → R6_7 (dataOfSetup4 hS hU S)
  c619 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.C619
  c620 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.C620
  c624 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.C624
  c629 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.C629
  c632 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.C632
  c635 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.C635
  c636 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.C636

end CFSG.LocalAnalysis.UniquenessCase.UC6
