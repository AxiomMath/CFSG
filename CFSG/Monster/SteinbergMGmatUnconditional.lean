module

public import CFSG.Monster.SteinbergMHmatInnerAut
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Monster.SteinbergMCatalogSchreier
public import CFSG.Monster.SteinbergMCatalogOddCore
public import CFSG.Monster.SteinbergMBXInvolutionOddCore
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatSchreier

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Monster.Generated

theorem gmat_automorphisms_inner_unconditional :
    ∀ α : MulAut Gmat, ∃ g : Gmat, α = MulAut.conj g :=
  gmat_automorphisms_inner (Monster.Existence.Hmat_perfect_and_inner_of_Co1_inner
      (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)).2

theorem native_M_visible_centralizer_schreier_unconditional :
    Group.IsSolvable (Outer Hmat) ∧ (Qmat.subgroupOf Hmat).Characteristic ∧
      (∀ α : MulAut Hmat, ∃ g : Hmat, ∃ r ∈ quotKerAut (Qmat.subgroupOf Hmat),
        α = MulAut.conj g * r) ∧
      ∃ F : Subgroup (quotKerAut (Qmat.subgroupOf Hmat)), ∃ _ : F.Normal, IsPGroup 2 F ∧
        IsPGroup 3 (quotKerAut (Qmat.subgroupOf Hmat) ⧸ F) :=
  native_M_visible_centralizer_schreier (Monster.Existence.Hmat_perfect_and_inner_of_Co1_inner
      (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)).2

theorem native_M_rational_group_schreier_unconditional :
    Group.IsSolvable (Outer Gmat) :=
  native_M_rational_group_schreier (Monster.Existence.Hmat_perfect_and_inner_of_Co1_inner
      (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)).2

theorem simple_presentation_M_model_schreier_unconditional :
    ∀ (T : Type*) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
      Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.M) → Group.IsSolvable (Outer T) :=
  simple_presentation_M_model_schreier (Monster.Existence.Hmat_perfect_and_inner_of_Co1_inner
      (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)).2

theorem exact_M_full_original_group_involution_odd_core_unconditional
    :
    ∀ (X : Type*) [Group X] [Finite X], IsSimpleGroup (CFSG.generalizedFitting X) →
      (∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) →
      Nonempty (CFSG.generalizedFitting X ≃* CFSG.Blueprint.NativeSporadic.M) →
      CFSG.generalizedFitting X = ⊤ ∧ ∀ t : X, orderOf t = 2 →
        CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set X)) = ⊥ ∧
          CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ :=
  exact_M_full_original_group_involution_odd_core (Monster.Existence.Hmat_perfect_and_inner_of_Co1_inner
      (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)).2
    CFSG.Monster.Existence.native_M_all_involution_centralizers_odd_core_free

end CFSG.ComponentClassification.BMCase
