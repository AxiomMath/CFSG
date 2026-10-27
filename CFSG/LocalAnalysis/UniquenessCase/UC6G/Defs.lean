module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Mc
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (calNOf)

structure Mz614 {G : Type} [Group G] [Finite G] (Dat : Data G) extends Mc614 Dat where
  Z : Subgroup G
  hZ : Mc614.IsZ toMc614 Z

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

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

end CFSG.LocalAnalysis.UniquenessCase.UC6G
