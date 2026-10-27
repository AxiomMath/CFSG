module

import CFSG.RankThree.PartOne.S10.HyperplaneObstructionPlaneVanishing
import CFSG.RankThree.PartOne.S10.HyperplaneObstructionComponentAction
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.GroupTheory.SteinbergBYAschVanishing
public import CFSG.RankThree.GroupTheory.ThetaComponents
import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore

public section

namespace CFSG.RankThree.PartOne.HyperplaneObstruction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem not_dvd_card_of_isPGroup_two [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {V : Subgroup G} (hV : IsPGroup 2 V) : ¬ p ∣ Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem eq_bot_of_isPGroup_two_of_le_odd [Finite G] {Q T : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQT : Q ≤ T) (hT : Odd (Nat.card T)) : Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hQT
  rw [← Subgroup.card_eq_one]
  rcases k with _ | k
  · simpa using hk
  · exfalso
    rw [hk] at hdvd
    exact (Nat.not_even_iff_odd.mpr hT) (even_iff_two_dvd.mpr
      ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd))

theorem mem_normalizer_commutator_of_mem_normalizer {X Y : Subgroup G} {g : G}
    (hX : g ∈ normalizer (X : Set G)) (hY : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer (⁅X, Y⁆ : Subgroup G) := by
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    (mem_normalizer_iff_map_conj_eq).mp hX, (mem_normalizer_iff_map_conj_eq).mp hY]

theorem exists_inf_centralizer_two_core_commutator_ne_bot [Finite G]
    (hG : IsCharacteristicPType G 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B R K : Subgroup G}
    (hB : IsElementaryAbelian p B) (hBcard : p ^ 2 ≤ Nat.card B) (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) (hBR : B ≤ normalizer (R : Set G)) (hKR : K ≤ Subgroup.centralizer (R : Set G))
    (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) :
    ∃ a ∈ B, a ≠ 1 ∧
      ⁅inSubgroup (pCore 2) (normalizer (R : Set G)) ⊓ Subgroup.centralizer ({a} : Set G),
        K⁆ ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := normalizer (R : Set G) with hJ
  set T₂ := inSubgroup (pCore 2) J with hT₂
  have hT₂2 : IsPGroup 2 T₂ := (CFSG.pCore_isPGroup (p := 2) (G := J)).map J.subtype
  have hJT₂ : J ≤ normalizer (T₂ : Set G) :=
    SteinbergBM.le_normalizer_inSubgroup_pCore 2 J
  have hKJ : K ≤ J := hKR.trans (Subgroup.centralizer_le_normalizer _)
  by_contra hcon
  push Not at hcon
  have hT₂K : T₂ ≤ Subgroup.centralizer (K : Set G) :=
    SteinbergBM.le_of_forall_inf_centralizer_le hB hBcard (not_dvd_card_of_isPGroup_two hp hp2 hT₂2)
      (hBR.trans hJT₂) fun a ha ha1 =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon a ha ha1)
  have hKT₂c : K ≤ Subgroup.centralizer (T₂ : Set G) := Subgroup.le_centralizer_iff.mp hT₂K
  have hKT₂ : K ≤ T₂ := fun x hx =>
    SteinbergBM.mem_inSubgroup_pCore_of_isCharacteristicPType hG hR2 hR1 (hKJ hx)
      fun s hs => Subgroup.mem_centralizer_iff.mp (hKT₂c hx) s hs
  have hK2 : IsPGroup 2 K := hT₂2.to_le hKT₂
  have : Group.IsNilpotent K := hK2.isNilpotent
  have : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem false_of_perfect_cover_at_plane [Finite G] (hG : IsCharacteristicPType G 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hvan : SteinbergBY.AschVanishing G p) {A B R K : Subgroup G}
    (hAe : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3) (hBA : B ≤ A)
    (hBcard : Nat.card B = p ^ 2) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hBR : B ≤ normalizer (R : Set G)) (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥)
    (hKR : K ≤ Subgroup.centralizer (R : Set G)) (hKB : K ≤ Subgroup.centralizer (B : Set G))
    {Ld : G → Subgroup G} (hLd : ∀ d ∈ B, d ≠ 1 → Ld d ∈ thetaComponentsAt p d)
    (hKLd : ∀ d ∈ B, d ≠ 1 → K ≤ Ld d)
    (hLdK : ∀ d ∈ B, d ≠ 1 →
      Ld d ≤ K ⊔ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({d} : Set G))) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBe : IsElementaryAbelian p B := SteinbergBM.isElementaryAbelian_of_le hAe hBA
  obtain ⟨a, haB, ha1, hQne⟩ := exists_inf_centralizer_two_core_commutator_ne_bot hG hp hp2 hBe
    hBcard.ge hR2 hR1 hBR hKR hK hK1
  set J := normalizer (R : Set G) with hJ
  set T₂ := inSubgroup (pCore 2) J with hT₂
  have hT₂2 : IsPGroup 2 T₂ := (CFSG.pCore_isPGroup (p := 2) (G := J)).map J.subtype
  have hJT₂ : J ≤ normalizer (T₂ : Set G) :=
    SteinbergBM.le_normalizer_inSubgroup_pCore 2 J
  have hKJ : K ≤ J := hKR.trans (Subgroup.centralizer_le_normalizer _)
  set C := T₂ ⊓ Subgroup.centralizer ({a} : Set G) with hC
  set Q := ⁅C, K⁆ with hQ
  have hC2 : IsPGroup 2 C := hT₂2.to_le inf_le_left
  have hKa : ∀ c ∈ K, c * a = a * c := fun c hc =>
    (Subgroup.mem_centralizer_iff.mp (hKB hc) a haB).symm
  have hBa : ∀ c ∈ B, c * a = a * c := fun c hc =>
    congrArg Subtype.val (hBe.is_comm.comm ⟨c, hc⟩ ⟨a, haB⟩)
  have hKC : K ≤ normalizer (C : Set G) :=
    SteinbergBM.le_normalizer_inf_centralizer (hKJ.trans hJT₂) hKa
  have hBC : B ≤ normalizer (C : Set G) :=
    SteinbergBM.le_normalizer_inf_centralizer (hBR.trans hJT₂) hBa
  have hBK : B ≤ normalizer (K : Set G) :=
    (Subgroup.le_centralizer_iff.mpr hKB).trans (Subgroup.centralizer_le_normalizer _)
  have hQC : Q ≤ C := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing C K hKC
  have hQ2 : IsPGroup 2 Q := hC2.to_le hQC
  have hKQ : K ≤ normalizer (Q : Set G) := normalizer_commutator_ge_right C K
  have hBQ : B ≤ normalizer (Q : Set G) := fun g hg =>
    mem_normalizer_commutator_of_mem_normalizer (hBC hg) (hBK hg)
  have haA : a ∈ A := hBA haB
  have hQa : Q ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({a} : Set G)) := by
    rw [hQ, Subgroup.commutator_comm]
    exact commutator_two_group_le_theta_centralizer hp hp2 (hLd a haB ha1) (hKLd a haB ha1) hK
      (hLdK a haB ha1) hC2 inf_le_right hKC
  have hQB : ⁅Q, B⁆ = ⊥ :=
    vanishing_centralizes_plane_invariant_two_subgroups hp hvan hAe hAcard hBA hBcard haA ha1
      hQa hQ2 hBQ
  have hQcB : Q ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQB
  have hQ1T : ⁅Q, K⁆ ≤ thetaT p B := by
    refine le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 => ?_
    have hQd : Q ≤ Subgroup.centralizer ({d} : Set G) :=
      hQcB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd))
    rw [Subgroup.commutator_comm]
    exact commutator_two_group_le_theta_centralizer hp hp2 (hLd d hd hd1) (hKLd d hd hd1) hK
      (hLdK d hd hd1) hQ2 hQd hKQ
  obtain ⟨-, -, hodd⟩ := hvan A hAe hAcard B hBA hBcard a haA ha1
  have hQ1C : ⁅Q, K⁆ ≤ Q := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Q K hKQ
  have hQ1 : ⁅Q, K⁆ = ⊥ := eq_bot_of_isPGroup_two_of_le_odd (hQ2.to_le hQ1C) hQ1T hodd
  have hCK : ⁅K, C⁆ = ⊥ := by
    refine CFSG.LocalCores.perfect_double_commutator (Subgroup.isPerfect_iff.mpr hK) ?_
    rw [Subgroup.commutator_comm K C]
    exact hQ1
  apply hQne
  rw [hQ, Subgroup.commutator_comm]
  exact hCK

end CFSG.RankThree.PartOne.HyperplaneObstruction
