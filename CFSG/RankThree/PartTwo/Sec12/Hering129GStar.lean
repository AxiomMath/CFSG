module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bOmega
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Sec4.Steps434
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPlan

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129G

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.RonanStep131b

variable {G : Type} [Group G] [Finite G]

theorem not_starConditionAt_of_normal_two {A B W : Subgroup G} {x b : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hxA : x ∈ A) (hx1 : x ≠ 1) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hxB : x ∉ B)
    (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hodd : Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({x} : Set G)), A⁆ : Subgroup G)))
    (hW2 : IsPGroup 2 W) (hWx : W ≤ Subgroup.centralizer ({x} : Set G))
    (hWb : W ≤ Subgroup.centralizer ({b} : Set G))
    (hWn : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∈ Subgroup.centralizer ({b} : Set G) →
      ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (hW1 : ⁅W, A⁆ ≠ ⊥) : ¬ StarConditionAt A x := by
  intro hstar
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hAsup : B ⊔ Subgroup.zpowers x = A := sup_zpowers_eq_of_card hBA hA27 hB9 hxA hxB
  have hH1 := ronan131b_H1 hAe hBA hAsup hxA hx1 hB9 hxB hstar
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  have hAC : A ≤ C := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy x hxA)
  have hBC : B ≤ C := hBA.trans hAC
  obtain ⟨bC, hbCe⟩ : ∃ y : ↥C, (y : G) = b := ⟨⟨b, hBC hbB⟩, rfl⟩
  have hbC1 : bC ≠ 1 := by
    intro h
    apply hb1
    rw [← hbCe, h, Subgroup.coe_one]
  have hbBC : bC ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr (by rw [hbCe]; exact hbB)
  set WC : Subgroup ↥C := W.subgroupOf C with hWCdef
  set H : Subgroup ↥C := Subgroup.centralizer ({bC} : Set ↥C) with hHdef
  have hWCH : WC ≤ H := by
    intro w hw
    rw [hHdef, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp (hWb (Subgroup.mem_subgroupOf.mp hw))
    simpa [hbCe] using this
  set WH : Subgroup ↥H := WC.subgroupOf H with hWHdef
  have hWHn : WH.Normal := by
    refine ⟨fun w hw g => ?_⟩
    rw [hWHdef, Subgroup.mem_subgroupOf, hWCdef, Subgroup.mem_subgroupOf] at hw ⊢
    have hgx : (g : ↥C).1 ∈ C := (g : ↥C).2
    have hgb : ((g : ↥C) : G) ∈ Subgroup.centralizer ({b} : Set G) := by
      have h1 : (g : ↥C) * bC = bC * (g : ↥C) := Subgroup.mem_centralizer_singleton_iff.mp g.2
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa [hbCe] using h2
    exact hWn _ hgx hgb _ hw
  have hWH2 : IsPGroup 2 WH := by
    have h1 : IsPGroup 2 WC := IsPGroup.comap_subtype hW2
    exact IsPGroup.comap_subtype h1
  have hWHθ : WH ≤ aschbacherSolvableCore 3 ↥H :=
    Sec4.le_aschbacherSolvableCore_of_isPGroup Nat.prime_two (by norm_num) hWHn hWH2
  have hWCθ : WC ≤ inSubgroup (aschbacherSolvableCore 3) H := by
    intro w hw
    have hw' : (⟨w, hWCH hw⟩ : ↥H) ∈ aschbacherSolvableCore 3 ↥H :=
      hWHθ (Subgroup.mem_subgroupOf.mpr hw)
    exact ⟨_, hw', rfl⟩
  have hJ : ⁅inSubgroup (aschbacherSolvableCore 3) H, B.subgroupOf C⁆ ≤
      thetaJ 3 (B.subgroupOf C) :=
    le_iSup_of_le bC (le_iSup_of_le hbBC (le_iSup_of_le hbC1 le_rfl))
  have hWBθ : ⁅WC, B.subgroupOf C⁆ ≤ aschbacherSolvableCore 3 ↥C :=
    (Subgroup.commutator_mono hWCθ le_rfl).trans (hJ.trans (le_sup_left.trans hH1))
  have hWB : ⁅W, B⁆ ≤ inSubgroup (aschbacherSolvableCore 3) C := by
    have h1 := Subgroup.map_mono (f := C.subtype) hWBθ
    rw [Subgroup.map_commutator] at h1
    have hW' : WC.map C.subtype = W := by
      rw [hWCdef, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hWx
    have hB' : (B.subgroupOf C).map C.subtype = B := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hBC
    rwa [hW', hB'] at h1
  have hBp : IsPGroup 3 B := fun y => ⟨1, Subtype.ext (by simpa using hAe.2 y (hBA y.2))⟩
  have hWnorm : ∀ g ∈ A, g ∈ Subgroup.normalizer (W : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hgx : g ∈ C := hAC hg
    have hgb : g ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hAc g hg b (hBA hbB))
    have hginv : g⁻¹ ∈ A := A.inv_mem hg
    constructor
    · intro hw
      exact hWn g hgx hgb w hw
    · intro hw
      have := hWn g⁻¹ (C.inv_mem hgx) (Subgroup.inv_mem _ hgb) _ hw
      simpa [mul_assoc] using this
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hk] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := fun g hg => hWnorm g (hBA hg)
  have hidem : ⁅⁅W, B⁆, B⁆ = ⁅W, B⁆ :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
      B W hBp hW3 hBW
  have hWBA : ⁅W, B⁆ ≤ ⁅inSubgroup (aschbacherSolvableCore 3) C, A⁆ := by
    calc ⁅W, B⁆ = ⁅⁅W, B⁆, B⁆ := hidem.symm
      _ ≤ ⁅inSubgroup (aschbacherSolvableCore 3) C, B⁆ := Subgroup.commutator_mono hWB le_rfl
      _ ≤ ⁅inSubgroup (aschbacherSolvableCore 3) C, A⁆ := Subgroup.commutator_mono le_rfl hBA
  have hWBle : ⁅W, B⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hBW
  have hWB2 : IsPGroup 2 (⁅W, B⁆ : Subgroup G) := hW2.to_le hWBle
  have hWBodd : Odd (Nat.card (⁅W, B⁆ : Subgroup G)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hWBA)
  have hWBbot : ⁅W, B⁆ = ⊥ := by
    obtain ⟨k, hk⟩ := hWB2.exists_card_eq
    rw [hk] at hWBodd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hWBodd) (by
        rw [Nat.even_pow]
        exact ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  apply hW1
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, ← hAsup]
  refine sup_le ?_ ?_
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
      rw [Subgroup.commutator_comm]; exact hWBbot)
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (hWx hw)

end CFSG.RankThree.PartTwo.Sec12.Hering129G
