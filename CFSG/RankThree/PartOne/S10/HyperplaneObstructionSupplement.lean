module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual

public section

namespace CFSG.RankThree.PartOne.HyperplaneObstruction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem le_inSubgroup_theta_of_normal_solvable [Finite G] {p : ℕ} (hp : p.Prime)
    {L W : Subgroup G} (hWL : W ≤ L) (hLW : L ≤ normalizer (W : Set G))
    (hWs : Group.IsSolvable W) (hWp : ¬ p ∣ Nat.card W) :
    W ≤ inSubgroup (aschbacherSolvableCore p) L := by
  have hmax := (solvable_prime_complement_core_characterization (H := L) hp).2.2.2.1
  have hn : (W.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hWL).mpr hLW
  have hs : Group.IsSolvable (W.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hWL).toMonoidHom) (subgroupOfEquivOfLe hWL).injective
  have hpd : ¬ p ∣ Nat.card (W.subgroupOf L) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv]
    exact hWp
  have h := hmax _ hn hs hpd
  intro x hx
  exact ⟨⟨x, hWL hx⟩, h hx, rfl⟩

theorem inf_inSubgroup_theta_le_inSubgroup_theta [Finite G] {p : ℕ} (hp : p.Prime)
    {X L : Subgroup G} (hLX : L = (L ⊓ X) ⊔ inSubgroup (aschbacherSolvableCore p) L) :
    L ⊓ inSubgroup (aschbacherSolvableCore p) X ≤ inSubgroup (aschbacherSolvableCore p) L := by
  set θX := inSubgroup (aschbacherSolvableCore p) X with hθX
  set θL := inSubgroup (aschbacherSolvableCore p) L with hθL
  obtain ⟨hθLL, hθLn⟩ := theta_le_and_normal p L
  obtain ⟨hθXs, hθXp⟩ := theta_solvable_and_not_dvd hp X
  obtain ⟨hθLs, hθLp⟩ := theta_solvable_and_not_dvd hp L
  have hLθL : L ≤ normalizer (θL : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hθLL).mp hθLn
  have hXθX : X ≤ normalizer (θX : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p X)
  set T := L ⊓ θX with hT
  have hTθX : T ≤ θX := inf_le_right
  have hTs : Group.IsSolvable T :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hTθX)
      (Subgroup.inclusion_injective hTθX)
  have hTp : ¬ p ∣ Nat.card T := fun h => hθXp (h.trans (Subgroup.card_dvd_of_le hTθX))
  have hTθL : T ≤ normalizer (θL : Set G) := inf_le_left.trans hLθL
  obtain ⟨hWs, hWp⟩ := isSolvable_and_not_dvd_sup hp hTθL hθLs hTs hθLp hTp
  have hWL : θL ⊔ T ≤ L := sup_le hθLL inf_le_left
  have hLW : L ≤ normalizer ((θL ⊔ T : Subgroup G) : Set G) := by
    refine hLX.le.trans (sup_le (fun m hm => ?_) (le_sup_left.trans Subgroup.le_normalizer))
    exact mem_normalizer_sup (hLθL hm.1) (mem_normalizer_inf (Subgroup.le_normalizer hm.1)
      (hXθX hm.2))
  exact le_sup_right.trans (le_inSubgroup_theta_of_normal_solvable hp hWL hLW hWs hWp)

theorem residual_supplement_of_perfect_cover [Finite G] {p : ℕ} (hp : p.Prime) {d : G}
    {X Ld K P₀ : Subgroup G} (hLd : Ld ∈ thetaComponentsAt p d)
    (hXP : X = inSubgroup (aschbacherSolvableCore p) X ⊔ P₀)
    (hLdP : Ld = inSubgroup (aschbacherSolvableCore p) Ld ⊔ P₀)
    (hP₀X : P₀ ≤ X) (hP₀Ld : P₀ ≤ Ld) (hK : ⁅K, K⁆ = K) (hKX : K ≤ X)
    (hKd : K ≤ Subgroup.centralizer ({d} : Set G))
    (hXK : (X : Set G) = (inSubgroup (aschbacherSolvableCore p) X : Set G) * (K : Set G)) :
    K ≤ Ld ∧ Ld = inSubgroup (aschbacherSolvableCore p) Ld ⊔ K := by
  have hθXX : inSubgroup (aschbacherSolvableCore p) X ≤ X := Subgroup.map_subtype_le _
  have hθLL : inSubgroup (aschbacherSolvableCore p) Ld ≤ Ld := Subgroup.map_subtype_le _
  have hXrel : X = (X ⊓ Ld) ⊔ inSubgroup (aschbacherSolvableCore p) X :=
    le_antisymm (hXP.le.trans (sup_le le_sup_right ((le_inf hP₀X hP₀Ld).trans le_sup_left)))
      (sup_le inf_le_left hθXX)
  have hLdrel : Ld = (Ld ⊓ X) ⊔ inSubgroup (aschbacherSolvableCore p) Ld :=
    le_antisymm (hLdP.le.trans (sup_le le_sup_right ((le_inf hP₀Ld hP₀X).trans le_sup_left)))
      (sup_le inf_le_left hθLL)
  obtain ⟨U, hUset, hUres⟩ := mutual_theta_supplements_identify_local_residual hp hLd hXrel hLdrel
  have hKU : K ≤ U := by
    intro k hk
    have h : k * 1 ∈ ((X ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) *
        (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({d} : Set G)) : Set G) :=
      Set.mul_mem_mul ⟨hKX hk, hKd hk⟩ (Subgroup.one_mem _)
    rw [mul_one, ← hUset] at h
    exact h
  have hKLd : K ≤ Ld := by
    have h := EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect hKU
      (Subgroup.isPerfect_iff.mpr hK)
    rwa [hUres] at h
  refine ⟨hKLd, le_antisymm ?_ (sup_le hθLL hKLd)⟩
  have hT := inf_inSubgroup_theta_le_inSubgroup_theta hp hLdrel
  refine hLdrel.le.trans (sup_le (fun m hm => ?_) le_sup_left)
  have hmX : (m : G) ∈ (inSubgroup (aschbacherSolvableCore p) X : Set G) * (K : Set G) := by
    rw [← hXK]
    exact hm.2
  obtain ⟨t, ht, k, hk, rfl⟩ := hmX
  have htLd : t ∈ Ld := by
    have := Ld.mul_mem hm.1 (Ld.inv_mem (hKLd hk))
    simpa using this
  exact Subgroup.mul_mem_sup (hT ⟨htLd, ht⟩) hk

end CFSG.RankThree.PartOne.HyperplaneObstruction
