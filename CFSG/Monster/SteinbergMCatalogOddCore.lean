module

public import CFSG.Monster.SteinbergMCatalogNativeIso
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatFittingTransfer
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatInner

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.Monster.Generated

theorem exact_M_full_original_group_involution_odd_core
    (hautH : ∀ β : MulAut Hmat, ∃ h : Hmat, β = MulAut.conj h)
    (hodd : ∀ s : Gmat, orderOf s = 2 →
      CFSG.pPrimeCore 2 (Subgroup.centralizer {s}) = ⊥ ∧
        CFSG.oddCore (Subgroup.centralizer {s}) = ⊥) :
    ∀ (X : Type*) [Group X] [Finite X], IsSimpleGroup (CFSG.generalizedFitting X) →
      (∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) →
      Nonempty (CFSG.generalizedFitting X ≃* CFSG.Blueprint.NativeSporadic.M) →
      CFSG.generalizedFitting X = ⊤ ∧ ∀ t : X, orderOf t = 2 →
        CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set X)) = ⊥ ∧
          CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  intro X _ _ _ _ ⟨θ⟩
  exact gmat_generalizedFitting_transfer (gmat_automorphisms_inner hautH) hodd
    (MulEquiv.ofBijective _ (catalog_fM_comp_mulEquiv_bijective θ))

end CFSG.ComponentClassification.BMCase
