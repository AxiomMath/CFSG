module

import CFSG.RankThree.PartOne.S10.SectionTenHyperplaneLocalResidualObstruction
import CFSG.RankThree.PartOne.S10.SectionTenMaximalComponentQuotientActorKernelCyclic
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem commutator_le_theta_of_thetaQuotientCentralizer {G : Type*} [Group G] (p : ℕ)
    {A L : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ⁅L, thetaQuotientCentralizer p A L⁆ ≤ inSubgroup (aschbacherSolvableCore p) L := by
  have hEker := (sectionTen_quotient_action_kernel p hAL).2
  rw [Subgroup.commutator_le]
  intro l hl x hx
  have hx' := ((hEker x).mp hx).2 l hl
  have h1 : ⁅l, x⁆ = (x * l * x⁻¹ * l⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  exact Subgroup.inv_mem _ hx'

theorem inSubgroup_perfectResidual_local_sup_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {b : G} {L K : Subgroup G} (hK : K ∈ thetaComponentsAt p b)
    (hLK : sectionTenRel p L K) (hKL : sectionTenRel p K L) :
    inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G))) = K := by
  obtain ⟨U, hUset, hUK⟩ := mutual_theta_supplements_identify_local_residual hp hK hLK hKL
  rw [← eq_sup_of_coe_eq_mul hUset, hUK]

theorem exists_five_actor_with_bad_local_residual {G : Type} [Group G] [Finite G]
    {A L : Subgroup G} {c : G} {q : ℕ} {D R : Subgroup G}
    (hS10 : SteinbergBM.SectionTenSetup G 5 A) (hcrit : FiveCriticalData A L c q D R) :
    ∃ e ∈ thetaQuotientCentralizer 5 A L, e ≠ 1 ∧ e ∉ Subgroup.zpowers c ∧
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer ({e} : Set G)) ⊔
        inSubgroup (aschbacherSolvableCore 5) (Subgroup.centralizer ({e} : Set G))) ∉
          thetaComponentsAt 5 e := by
  have hp : (5 : ℕ).Prime := by norm_num
  obtain ⟨-, -, -, -, -, -, hAe, -, -, -⟩ := id hS10
  have hcA : c ∈ A := hcrit.c_mem
  have hc1 : c ≠ 1 := hcrit.c_ne_one
  have hLZ : L ∈ thetaComponentFamily 5 A := hcrit.mem_family.1.1
  have hLc : L ∈ thetaComponentsAt 5 c := hcrit.mem_family.2
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hcrit.A_normalizes
  have hEA : thetaQuotientCentralizer 5 A L ≤ A := inf_le_left
  obtain ⟨e, heE, he1, hnot⟩ := section_ten_hyperplane_local_residual_obstruction G 5 A hS10 L hLZ
    (thetaQuotientCentralizer 5 A L) hEA hcrit.E_card
    (commutator_le_theta_of_thetaQuotientCentralizer 5 hAL)
  refine ⟨e, heE, he1, fun hec => hnot ?_, hnot⟩
  have hordc : orderOf c = 5 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  have hordE : orderOf e = 5 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp (hEA heE) he1
  have hzp : Subgroup.zpowers e = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hec)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hordc, hordE])
  have hcent : Subgroup.centralizer ({e} : Set G) = Subgroup.centralizer ({c} : Set G) := by
    rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers e,
      SteinbergBY.centralizer_singleton_eq_centralizer_zpowers c, hzp]
  have hLe : L ∈ thetaComponentsAt 5 e := by
    have h : thetaComponentsAt 5 e = thetaComponentsAt 5 c := by
      unfold thetaComponentsAt
      rw [hcent]
    rw [h]
    exact hLc
  rw [inSubgroup_perfectResidual_local_sup_eq hp hLe (sectionTenRel_refl 5 L)
    (sectionTenRel_refl 5 L)]
  exact hLe

end CFSG.RankThree.PartOne
