module

public import CFSG.RankThree.PartOne.N143.CaseB1Theta
public import CFSG.RankThree.PartOne.N143.Weyl613List
public import CFSG.RankThree.PartOne.S12.Sec12Two
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.N143
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_center_of_le_centralizer (hSLB : SectionListBound) [IsSimpleGroup G]
    (hKP : CFSG.IsKProper G) (hnonab : ∃ a b : G, a * b ≠ b * a) (he : evenRank G ≤ 3) {c : G}
    (hc1 : c ≠ 1) {K : Subgroup G} (hKc : K ≤ centralizer ({c} : Set G))
    (hq : CFSG.IsQuasisimple ↥K) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ7 : 7 ≤ ℓ) :
    ¬ ℓ ∣ Nat.card (center ↥K) := by
  have hne : centralizer ({c} : Set G) ≠ ⊤ :=
    EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hc1
  have hCK : CFSG.IsKGroup ↥(centralizer ({c} : Set G)) := hKP _ hne
  have hCe : evenRank ↥(centralizer ({c} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans he
  exact (hSLB _ hCK hCe (K.subgroupOf (centralizer ({c} : Set G))) ↥K hq
    (Subgroup.subgroupOfEquivOfLe hKc).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hKc).surjective).2 ℓ hℓ hℓ7

theorem aschbacherSolvableCore_le_center {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) : aschbacherSolvableCore p X ≤ center X :=
  normal_solvable_le_center hX inferInstance
    (solvable_prime_complement_core_characterization (H := X) hp).1

theorem exists_maximal_elementaryAbelian {p : ℕ} {A : Subgroup G} (hA : IsElementaryAbelian p A) :
    ∃ E : Subgroup G, IsElementaryAbelian p E ∧ E ≤ centralizer (A : Set G) ∧
      ∀ F : Subgroup G, IsElementaryAbelian p F → F ≤ centralizer (A : Set G) → E ≤ F → F = E := by
  have hAC : A ≤ centralizer (A : Set G) := fun a ha b hb =>
    congrArg Subtype.val (hA.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  let S : Set (Subgroup G) :=
    {F | IsElementaryAbelian p F ∧ F ≤ centralizer (A : Set G) ∧ A ≤ F}
  obtain ⟨E, hE, hmax⟩ := (Set.toFinite S).exists_maximalFor id S ⟨A, hA, hAC, le_rfl⟩
  refine ⟨E, hE.1, hE.2.1, fun F hF hFC hEF => ?_⟩
  exact le_antisymm (hmax ⟨hF, hFC, hE.2.2.trans hEF⟩ hEF) hEF

theorem inner_small (hSchreier : SchreierFor InCatalog) (hSLB : SectionListBound)
    (hI : Item613ListIdx) (hB : ∀ (X : Type) [Group X], ListEvenItem X → EvenLieTypeSmall X)
    {A : Subgroup G} (hS : SteinbergBM.SectionTenSetup G 7 A) {K : Subgroup G}
    (hK : K ∈ sectionTenZeroStar 7 A) (hK1 : K ∈ sectionTenOne 7 A) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (φ : ↥K →* X), Function.Surjective φ ∧
      φ.ker ≤ center ↥K ∧ IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧
      EvenLieTypeSmall X := by
  classical
  have hp : (7 : ℕ).Prime := by norm_num
  have : Fact (7 : ℕ).Prime := ⟨hp⟩
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, -, -, -⟩ := id hS
  have : IsSimpleGroup G := hsimple
  have he3 : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS).le
  obtain ⟨c, hcA, hc1, hKc⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset 7 A).2.2.1 hK.2)
  obtain ⟨hKq, hAK, hker⟩ := moving_maximal_data_at hSchreier hS hK hcA hc1 hKc
  have hcyc : IsCyclic ↥(thetaQuotientCentralizer 7 A K) := by
    rw [hker]
    infer_instance
  set C : Subgroup G := centralizer ({c} : Set G) with hCdef
  have hKC : K ≤ C := (mem_thetaComponentsAt_iff.mp hKc).1
  have hKθ : K.subgroupOf C ∈ thetaComponents 7 ↥C := (mem_thetaComponentsAt_iff.mp hKc).2
  have hZ : ¬ 7 ∣ Nat.card (center ↥K) :=
    not_dvd_card_center_of_le_centralizer hSLB hKP hnonab he3 hc1 hKC hKq hp le_rfl
  obtain ⟨E, hE1, hE2, hE3⟩ := exists_maximal_elementaryAbelian (p := 7) hAe
  have h12 : Sec12Hyp G 7 A c K E := ⟨hS, hcA, hc1, ⟨⟨hK, hK1⟩, hKc⟩, hE1, hE2, hE3⟩
  obtain ⟨A₀, hA₀K, hA₀e, hA₀c, S, hSK, hS1, hS2, hA₀S, hSA₀⟩ :=
    Sec12Two.exists_plane_data h12 hKq hAK hcyc hZ
  have hne : C ≠ ⊤ := EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hc1
  have hCK : CFSG.IsKGroup ↥C := hKP C hne
  have hCe : evenRank ↥C ≤ 3 := (Sec9A.evenRank_subgroup_le C).trans he3
  have hA₀C : A₀ ≤ C := hA₀K.trans hKC
  have hSC : S ≤ C := hSK.trans hKC
  have hA₀e' : IsElementaryAbelian 7 ↥(A₀.subgroupOf C) := by
    have := hA₀e
    exact IsElementaryAbelian.subgroupOf hA₀C
  have hcard : 7 ^ 2 ≤ Nat.card ↥(A₀.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀C).toEquiv, hA₀c]
  set L' : Subgroup ↥C := K.subgroupOf C with hL'
  let e : ↥L' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  have hθK : (aschbacherSolvableCore 7 ↥L').map e.toMonoidHom = aschbacherSolvableCore 7 ↥K :=
    aschbacherSolvableCore_map_mulEquiv hp e
  have hnotθ : ¬ (S.subgroupOf C).subgroupOf L' ≤ aschbacherSolvableCore 7 ↥L' := by
    intro h
    have hcen : ∀ s ∈ S, ∀ k ∈ K, s * k = k * s := by
      intro s hs k hk
      have hx : (⟨⟨s, hSC hs⟩, hSK hs⟩ : ↥L') ∈ aschbacherSolvableCore 7 ↥L' := h hs
      have h1 : e ⟨⟨s, hSC hs⟩, hSK hs⟩ ∈ aschbacherSolvableCore 7 ↥K := by
        rw [← hθK]
        exact Subgroup.mem_map_of_mem _ hx
      have h2 := aschbacherSolvableCore_le_center hp hKq h1
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp h2 ⟨k, hk⟩)).symm
    have hbot : ⁅S, A₀⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hcen s hs a (hA₀K ha)).symm
    exact hS1 (hSA₀.trans hbot)
  have hQ := item613With_listEven hSLB hI hSchreier ↥C hCK hCe 7 hp le_rfl L' hKθ
    (A₀.subgroupOf C) hA₀e' hcard (fun x hx => hA₀K hx)
    ⟨S.subgroupOf C, subgroupOf_ne_bot hSC hS1, isPGroup_subgroupOf hSC hS2,
      fun x hx => hSK hx, hnotθ, normalizer_subgroupOf_of_le hA₀S,
      (commutator_subgroupOf hSC hA₀C).trans (by rw [← hSA₀])⟩
  have hL'K : CFSG.IsKGroup ↥L' := isKGroup_subgroup hCK L'
  have hL'e : evenRank ↥L' ≤ 3 := (Sec9A.evenRank_subgroup_le L').trans hCe
  have hq : CFSG.IsQuasisimple (↥L' ⧸ aschbacherSolvableCore 7 ↥L') := hKθ.2.2
  obtain ⟨hZ', -⟩ := thetaQuotient_center_bot_and_list hSLB hL'K hL'e 7 hp le_rfl hq
  obtain ⟨⟨eZ⟩, -, hnonab'⟩ := simple_of_quasisimple_center_bot hq hZ'
  let φ : ↥K →* (↥L' ⧸ aschbacherSolvableCore 7 ↥L') ⧸
      center (↥L' ⧸ aschbacherSolvableCore 7 ↥L') :=
    (QuotientGroup.mk' (center (↥L' ⧸ aschbacherSolvableCore 7 ↥L'))).comp
      ((QuotientGroup.mk' (aschbacherSolvableCore 7 ↥L')).comp e.symm.toMonoidHom)
  refine ⟨(↥L' ⧸ aschbacherSolvableCore 7 ↥L') ⧸ center (↥L' ⧸ aschbacherSolvableCore 7 ↥L'),
    inferInstance, inferInstance, φ, ?_, ?_, hq.2.1, ?_, hB _ hQ⟩
  · exact (QuotientGroup.mk'_surjective _).comp
      ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)
  · intro x hx
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 7 ↥L') (e.symm x) ∈
        center (↥L' ⧸ aschbacherSolvableCore 7 ↥L') :=
      (QuotientGroup.eq_one_iff _).mp hx
    rw [hZ', Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : x ∈ (aschbacherSolvableCore 7 ↥L').map e.toMonoidHom :=
      ⟨e.symm x, h1, by simp [e]⟩
    rw [hθK] at h2
    exact aschbacherSolvableCore_le_center hp hKq h2
  · obtain ⟨a, b, hab⟩ := hnonab'
    exact ⟨eZ.symm a, eZ.symm b, fun h => hab (eZ.symm.injective (by simpa [map_mul] using h))⟩

end CFSG.RankThree.PartOne.BRANCH
