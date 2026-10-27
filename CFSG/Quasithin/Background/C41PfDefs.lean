module

public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Quasithin.Background.SmithC27Defs
public import CFSG.Quasithin.EmptyFaithful.SBc17Cases

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def C41KGBorel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K D S : Subgroup G),
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    ((∃ n : ℕ, 1 < n ∧ IsLin2Type K n) ∨ IsAltType K 3 ∨ IsAltType K 5) →
    ⁅D, D⁆ = D → D ≤ Subgroup.normalizer (K : Set G) → IsSylowTwoOf S K →
    D ≤ Subgroup.normalizer (S : Set G) → ⁅D, K⁆ ≤ pCoreOf 2 K

variable {G : Type} [Group G] [Finite G]

structure C41Post (H R M L V K : Subgroup G) : Prop where
  hyp : HypC28 H R M L V
  comp : K ∈ cComp H
  charTwo : CharTwo K
  quasi : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  not_le : ¬ K ≤ M
  le_normalizer : R ≤ Subgroup.normalizer (K : Set G)
  le : conjClosure L M ≤ K
  not_commutator_le : ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K

variable (G) in
@[expose] def C41Elim : Prop :=
  ∀ H R M L V K : Subgroup G, C41Post H R M L V K →
    SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SmithC27.C27Two R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    (SBc17.C27L2 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ∨
      SBc17.C27A5 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ∨
      SBc17.C27A7a H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ∨
      SBc17.C27A7b H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ∨
      SBc17.C27Hat6 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ∨
      SBc17.C27ExcA7 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ∨
      SBc17.C27G2 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) → False

variable (G) in
@[expose] def C41InspB : Prop :=
  ∀ H R M L V K : Subgroup G, C41Post H R M L V K →
    SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SmithC27.C27Two R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SBc17.C27Alt H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) → C41Conclusion H R M L V K

variable (G) in
@[expose] def C41InspE : Prop :=
  ∀ H R M L V K : Subgroup G, C41Post H R M L V K →
    SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SmithC27.C27Two R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SBc17.C27A6Sp4 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) → C41Conclusion H R M L V K

variable (G) in
@[expose] def C41InspG : Prop :=
  ∀ H R M L V K : Subgroup G, C41Post H R M L V K →
    SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SmithC27.C27Two R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SBc17.C27SL3 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) → C41Conclusion H R M L V K

variable (G) in
@[expose] def C41InspH : Prop :=
  ∀ H R M L V K : Subgroup G, C41Post H R M L V K →
    SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SmithC27.C27Two R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SBc17.C27L45 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) → C41Conclusion H R M L V K

end CFSG.Quasithin
