module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalCommutatorBound
public import CFSG.RankThree.PartOne.S9.StatementsAlpha
import CFSG.RankThree.GroupTheory.SteinbergBMResidualCommonPlaneSylowTwo
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaCentralizerTransfer
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem sectionNinePlaneCommutatorBound_of (hPSR : ProperSubgroupResidual)
    (hS2A : SylowTwoAlternatives) : SectionNinePlaneCommutatorBound := by
  intro G _ _ p hG hgood A hA hAcard c hcA hc1 B hBA hBcard hcB
  have hp : p.Prime := hG.prime
  have hp3 : 3 < p := hG.three_lt
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hAp : IsPGroup p A := IsPGroup.of_card hAcard
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := (Sec9B.isElementaryAbelian_iff_forall.mp hA).1
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hAH : A ≤ H := fun x hx => Sec9B.mem_normalizer_zpowers_of_commute (hcomm x hx c hcA)
  have hHtop : H ≠ ⊤ := Sec9B.normalizer_zpowers_ne_top hG.simple hG.nonabelian hc1
  have hoc : orderOf c = p := SteinbergBY.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  obtain ⟨b, hbB, hbc⟩ : ∃ b ∈ B, b ∉ Subgroup.zpowers c := by
    refine IsConcreteLE.not_le_iff_exists.mp fun hBc => ?_
    have h1 := Subgroup.card_le_of_le hBc
    rw [hBcard, Nat.card_zpowers, hoc] at h1
    have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h2
    omega
  have hb1 : b ≠ 1 := fun h => hbc (h ▸ one_mem _)
  have hbA : b ∈ A := hBA hbB
  have hBeq : Subgroup.zpowers c ⊔ Subgroup.zpowers b = B := by
    refine Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hcB) (Subgroup.zpowers_le.mpr hbB)) ?_
    rw [SteinbergBY.card_zpowers_sup_zpowers hp hAcard hcA hc1 hbA hbc, hBcard]
  set X := H ⊓ Subgroup.centralizer ({b} : Set G) with hX
  have hYX : H ⊓ Subgroup.centralizer (B : Set G) ≤ X :=
    inf_le_inf_left H (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
  have hcX : c ∈ X := ⟨Subgroup.le_normalizer (Subgroup.mem_zpowers c),
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hcA b hbA)⟩
  have hO : inSubgroup (pCore 2) X ≤ Subgroup.centralizer ({c} : Set G) :=
    SteinbergBY.inSubgroup_pCore_two_le_centralizer hp hp2 hoc hcX inf_le_left
  have hXN : X ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) :
      Set G) := by
    intro x hx
    have hxB : x ∈ Subgroup.normalizer (B : Set G) := by
      apply SteinbergBY.mem_normalizer_of_map_conj_eq
      rw [← hBeq, Subgroup.map_sup,
        SteinbergBY.map_conj_eq_of_mem_normalizer (show x ∈ _ from hx.1),
        SteinbergBY.map_conj_eq_of_mem_normalizer (Sec9B.mem_normalizer_zpowers_of_commute
          (Subgroup.mem_centralizer_singleton_iff.mp hx.2))]
    exact SteinbergBY.mem_normalizer_inf (Subgroup.le_normalizer hx.1)
      (Sec9B.mem_normalizer_centralizer_of_mem_normalizer hxB)
  have hDeq : inSubgroup (pCore 2) (H ⊓ Subgroup.centralizer (B : Set G)) =
      inSubgroup (pCore 2) X := by
    rw [SteinbergBY.inSubgroup_pCore_eq_inf hYX hXN]
    refine inf_eq_right.mpr fun z hz => ⟨(SteinbergBY.inSubgroup_pCore_le 2 X hz).1, ?_⟩
    have hzb : z ∈ Subgroup.centralizer ({b} : Set G) := (SteinbergBY.inSubgroup_pCore_le 2 X hz).2
    have hzc := hO hz
    have hle : B ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [← hBeq]
      exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hzc).symm))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hzb).symm))
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  rw [hDeq]
  set V := inSubgroup (pCore 2) X with hV
  have hV2 : IsPGroup 2 ↥V := SteinbergBY.isPGroup_inSubgroup_pCore 2 X
  have hAX : A ≤ X := fun x hx =>
    ⟨hAH hx, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx b hbA)⟩
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hAX.trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 X)
  have hUθ : ⁅V, A⁆ ≤ inSubgroup (aschbacherSolvableCore p) H :=
    Sec9B.commutator_two_core_le_theta hPSR hG.kProper hG.evenRank_eq.le hp hp3 hA hAcard hAH hHtop
      hbA hb1
  have hUV : ⁅V, A⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hAV
  have hU2 : IsPGroup 2 ↥(⁅V, A⁆ : Subgroup G) := hV2.to_le hUV
  have hAU : A ≤ Subgroup.normalizer ((⁅V, A⁆ : Subgroup G) : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_commutator (hAV hx) (Subgroup.le_normalizer hx)
  have hSp : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) H) := by
    have h := (solvable_prime_complement_core_characterization (H := H) hp).2.2.1
    rwa [inSubgroup, Subgroup.card_map_of_injective H.subtype_injective]
  have hAS : A ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore p) H : Subgroup G) :
      Set G) := fun x hx =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p H
      (Subgroup.le_normalizer (hAH hx))
  obtain ⟨T, hT, hUT, hAT⟩ :=
    SteinbergBM.exists_isSylowOf_two_invariant_le hp hAp hSp hAS hUθ hU2 hAU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsSylowOf 2 T (inSubgroup (aschbacherSolvableCore p) H) :=
    ABGLocalTools.isSylowOf_iff.mp hT
  rcases hS2A G p hG A hA hAcard c hcA hc1 T hT' hAT with h1 | ⟨-, hb, -⟩ | ⟨h7, q, hq, hq7, hrank⟩
  · have hVcop : ¬ p ∣ Nat.card V := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
      rw [hk]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    have hidem := RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp A V hAp
      hVcop hAV
    rw [← hidem]
    exact (Subgroup.commutator_mono hUT le_rfl).trans h1
  · exact hb b hbA hb1
  · exact absurd (hgood h7 q hq hq7) (not_le.mpr hrank)

end CFSG.RankThree.PartOne
