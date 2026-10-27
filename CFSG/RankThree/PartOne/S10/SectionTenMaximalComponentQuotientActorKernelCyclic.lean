module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement Pointwise

theorem exists_subgroup_card_sq_of_not_isCyclic {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {E : Subgroup G} (hE : IsPGroup p E) (hnc : ¬ IsCyclic E) :
    ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hE
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    · have : Subsingleton E := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact hnc inferInstance
    · exact hnc (isCyclic_of_prime_card (p := p) (by simpa using hk))
  obtain ⟨B', hB'⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 2)
    (by rw [hk]; exact pow_dvd_pow p hk2)
  refine ⟨B'.map E.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hB']

theorem eq_sup_of_coe_eq_mul {G : Type*} [Group G] {U X Y : Subgroup G}
    (h : (U : Set G) = (X : Set G) * (Y : Set G)) : U = X ⊔ Y := by
  refine le_antisymm (fun x hx => ?_) (sup_le (fun x hx => ?_) (fun x hx => ?_))
  · have hx' : x ∈ (X : Set G) * (Y : Set G) := h ▸ hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx'
    exact (X ⊔ Y).mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hz)
  · have : x * 1 ∈ (X : Set G) * (Y : Set G) := Set.mul_mem_mul hx Y.one_mem
    rw [mul_one, ← h] at this
    exact this
  · have : 1 * x ∈ (X : Set G) * (Y : Set G) := Set.mul_mem_mul X.one_mem hx
    rw [one_mul, ← h] at this
    exact this

theorem section_ten_maximal_component_quotient_actor_kernel_cyclic_of
    (hE5 : SectionTenHyperplaneLocalResidualObstruction) :
    SectionTenMaximalComponentQuotientActorKernelCyclic := by
  intro hS G _ _ p A hS10 L hL
  have hp : p.Prime := sectionTenSetup_prime hS10
  have hp3 : 3 < p := sectionTenSetup_three_lt hS10
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS10).le
  obtain ⟨hsimple, hnonab, hK, -, -, -, hAe, hAcard, -, -⟩ := id hS10
  have : IsSimpleGroup G := hsimple
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he p hp hp3 A hAe L hL.1
  refine ⟨hAL, ?_⟩
  by_contra hnc
  set E := thetaQuotientCentralizer p A L with hEdef
  have hEA : E ≤ A := inf_le_left
  have hEp : IsPGroup p E := (IsElementaryAbelian.isPGroup p A).to_le hEA
  obtain ⟨B, hBE, hBcard⟩ := exists_subgroup_card_sq_of_not_isCyclic hp hEp hnc
  have hBA : B ≤ A := hBE.trans hEA
  have hEker := (sectionTen_quotient_action_kernel p hAL).2
  have hLE : ⁅L, E⁆ ≤ inSubgroup (aschbacherSolvableCore p) L := by
    rw [Subgroup.commutator_le]
    intro l hl x hx
    have hx' := ((hEker x).mp hx).2 l hl
    have h1 : ⁅l, x⁆ = (x * l * x⁻¹ * l⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact Subgroup.inv_mem _ hx'
  obtain ⟨b, hbB, hb1, hnot⟩ := hE5 G p A hS10 L hL.1 B hBA hBcard
    ((Subgroup.commutator_mono le_rfl hBE).trans hLE)
  apply hnot
  have hbA : b ∈ A := hBA hbB
  have hbE : b ∈ E := hBE hbB
  obtain ⟨K, hK, hLK⟩ := section_ten_trivial_actor_component_supplement hS G hnonab hK he p hp
    hp3 A hAe b hbA hb1 L hL.1
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hbE)).trans hLE)
  have hKF : K ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨b, hbA, hb1, hK⟩
  have hKL : sectionTenRel p K L := hL.2 K hKF hLK
  obtain ⟨U, hUset, hUK⟩ := mutual_theta_supplements_identify_local_residual hp hK hLK hKL
  have hU : U = (L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) :=
    eq_sup_of_coe_eq_mul hUset
  rw [← hU, hUK]
  exact hK

end CFSG.RankThree.PartOne
