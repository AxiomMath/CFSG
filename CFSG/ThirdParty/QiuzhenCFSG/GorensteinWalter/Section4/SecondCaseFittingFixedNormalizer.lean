module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingInterNotCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingNontrivial
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The fixed part is nontrivial and self-normalizing  (source: refs/bender-dihedral-sylow.tex L685–693) -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Equation (3) writes `F(U) ⊓ M = K₀ ⊔ F` with `K₀` cyclic inside `K`;
since S4-05 makes `F(U) ⊓ M` noncyclic, `F` is nontrivial. -/
public theorem secondCase_fitting_fixed_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (K K0 F : Subgroup G)
    (hKcyc : IsCyclic K) (hK0le : K0 ≤ K)
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M) :
    F ≠ ⊥ :=
  secondCase_fitting_centralizer_ne_bot_of_inter_not_cyclic
    K K0 F (fittingSubgroupOf c.U ⊓ w.M) hKcyc hK0le hjoin
    (secondCase_fitting_inter_M_not_cyclic hmin c w)

/-- In a minimal counterexample, a nontrivial subgroup normal in the maximal
subgroup `M` has ambient normalizer exactly `M`. -/
public theorem secondCase_normalizer_fitting_fixed_eq_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (F : Subgroup G) (hFne : F ≠ ⊥)
    (hFnormal : IsNormalIn F w.M) :
    Subgroup.normalizer (F : Set G) = w.M := by
  have hFleM : F ≤ w.M := hFnormal.1
  have hFnormalSub : (F.subgroupOf w.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFleM]
    intro f m hf hm
    exact hFnormal.2 m hm f hf
  exact normalizer_eq_of_nontrivial_normal_in_coatom
    (minimalCounterexample_isSimple hmin) w.M_maximal hFleM hFne hFnormalSub

end CFSG.GorensteinWalter
