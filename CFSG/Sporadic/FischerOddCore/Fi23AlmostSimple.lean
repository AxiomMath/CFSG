module

public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.Sporadic.FischerOddCore.Fi23Cent
public import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem almost_simple_of_inner {Q : Type*} [Group Q]
    (hinner : ∀ φ : MulAut Q, ∃ g : Q, φ = MulAut.conj g)
    (hinv : ∀ t : Q, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set Q)) = ⊥)
    {X : Type*} [Group X] [Finite X] (S : Subgroup X) [S.Normal] (hS : Nonempty (S ≃* Q))
    (hC : Subgroup.centralizer (S : Set X) = ⊥) :
    S = ⊤ ∧ ∀ t : X, orderOf t = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  set θ := hS.some
  have hinj := conjTransport_injective θ hC
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, hg⟩ := hinner (conjTransport θ x)
    have e : conjTransport θ ((θ.symm g : S) : X) = conjTransport θ x := by
      rw [conjTransport_of_mem, MulEquiv.apply_symm_apply, hg]
    rw [← hinj e]
    exact (θ.symm g).2
  refine ⟨htop, fun t ht => ?_⟩
  set φ : X ≃* Q := (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans θ
  have ho : orderOf (φ t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ht
  have h := oddCore_centralizer_eq_bot_of_mulEquiv φ.symm (hinv _ ho)
  rwa [MulEquiv.symm_apply_apply] at h

theorem generalized_fitting_of_inner {Q : Type*} [Group Q] (hZ : Subgroup.center Q = ⊥)
    (hinner : ∀ φ : MulAut Q, ∃ g : Q, φ = MulAut.conj g)
    (hinv : ∀ t : Q, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set Q)) = ⊥)
    {X : Type*} [Group X] [Finite X] (hJ : Nonempty (CFSG.generalizedFitting X ≃* Q)) :
    CFSG.generalizedFitting X = ⊤ ∧ ∀ t : X, orderOf t = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  exact almost_simple_of_inner hinner hinv _ hJ
    (centralizer_generalizedFitting_eq_bot_of_center (center_eq_bot_of_mulEquiv hJ.some hZ))

theorem CTUC_Fi23_almost_simple_involution_centralizer_odd_core_trivial
    {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) [S.Normal] (hS : Nonempty (S ≃* Blueprint.NativeSporadic.Fi23))
    (hC : Subgroup.centralizer (S : Set X) = ⊥) :
    S = ⊤ ∧ ∀ t : X, orderOf t = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ :=
  @almost_simple_of_inner Blueprint.NativeSporadic.Fi23 Units.instGroup fi23_mulAut_eq_conj
    CTUC_Fi23_all_involution_centralizers_odd_core_trivial X _ _ S _ hS hC

theorem CTUC_Fi23_generalized_Fitting_involution_centralizer_odd_core_trivial
    {X : Type*}
    [Group X] [Finite X] (_hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.Fi23)) :
    CFSG.generalizedFitting X = ⊤ ∧ ∀ t : X, orderOf t = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ :=
  @generalized_fitting_of_inner Blueprint.NativeSporadic.Fi23 Units.instGroup center_fi23
    fi23_mulAut_eq_conj CTUC_Fi23_all_involution_centralizers_odd_core_trivial X _ _ hJ

end CFSG.Sporadic.FischerOddCore
