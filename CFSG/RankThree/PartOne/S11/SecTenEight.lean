module

public import CFSG.RankThree.PartOne.S11.SecTenSeven
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial

@[expose] def Sec6EightMultipliers : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (K : Subgroup H) (p : ℕ), p.Prime → 3 < p → CFSG.IsQuasisimple K →
      Catalog (K ⧸ Subgroup.center K) → p ∣ Nat.card (Subgroup.center K) →
      p = 5 ∧ Nat.card (Subgroup.center K) = 5 ∧
        ∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 5 2 n

@[expose] def SUFiveNormalizingSubgroupsContained : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (L : Subgroup H) (n : ℕ), 1 ≤ n → CFSG.IsQuasisimple L → Nat.card (Subgroup.center L) = 5 →
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 n →
      ∀ X : Subgroup H, X ≤ Subgroup.normalizer (L : Set H) → Nat.card X = 5 →
        (∃ S : Subgroup H, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S ≤ L ∧
          X ≤ Subgroup.normalizer (S : Set H)) → X ≤ L

@[expose] def Sec10EightConclusion (p : ℕ) {G : Type} [Group G] (c : G) (L : Subgroup G) :
    Prop :=
  IsSimpleGroup (L ⧸ aschbacherSolvableCore p L) ∨
    (p = 5 ∧ (Subgroup.center L).map L.subtype = Subgroup.zpowers c ∧
      Nat.card (Subgroup.center L) = 5 ∧
      (∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 n) ∧
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) → Nat.card X = 5 →
        (∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S ≤ L ∧ X ≤ Subgroup.normalizer (S : Set G)) →
        X ≤ L)

@[expose] def InSec10EightMoving : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ c ∈ A, c ≠ 1 → ∀ L ∈ sectionTenAt p (sectionTenZeroStar p A) c, Sec10EightConclusion p c L

section Helpers

theorem theta_le_center_of_quasisimple {p : ℕ} (hp : p.Prime) {L : Type*} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) : aschbacherSolvableCore p L ≤ Subgroup.center L := by
  have hnt : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hperf : Group.IsPerfect L := hq.1
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (aschbacherSolvableCore_normal p L) with htop | hle
  · exfalso
    have hsol : Group.IsSolvable (aschbacherSolvableCore p L) :=
      (solvable_prime_complement_core_characterization (H := L) hp).1
    rw [htop] at hsol
    have hsolL : Group.IsSolvable L := Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv (G := L)).toMonoidHom) (Subgroup.topEquiv (G := L)).surjective
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := L)).ne
      hperf.commutator_eq_top
  · exact hle

theorem center_le_theta_of_not_dvd {p : ℕ} (hp : p.Prime) {L : Type*} [Group L] [Finite L]
    (h : ¬ p ∣ Nat.card (Subgroup.center L)) : Subgroup.center L ≤ aschbacherSolvableCore p L :=
  (solvable_prime_complement_core_characterization (H := L) hp).2.2.2.1 _ inferInstance
    inferInstance h

theorem commute_of_mem_normalizer_zpowers_of_orderOf {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime) {c x : G} (hc : orderOf c = p) (hx : x ^ p = 1)
    (hn : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) : x * c = c * x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, x * c * x⁻¹ = c ^ j := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hn c).mp (Subgroup.mem_zpowers c))
    exact ⟨j, hj.symm⟩
  have hit : ∀ n : ℕ, x ^ n * c * (x ^ n)⁻¹ = c ^ (j ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * c * (x ^ (n + 1))⁻¹ = x * (x ^ n * c * (x ^ n)⁻¹) * x⁻¹ := by group
        _ = x * c ^ (j ^ n) * x⁻¹ := by rw [ih]
        _ = (x * c * x⁻¹) ^ (j ^ n) := conj_zpow.symm
        _ = c ^ (j ^ (n + 1)) := by rw [hj, ← zpow_mul, pow_succ, mul_comm]
  have h1 : c ^ (j ^ p - 1) = 1 := by
    have := hit p
    rw [hx] at this
    rw [zpow_sub, zpow_one, ← this]
    simp
  have h2 : (p : ℤ) ∣ j ^ p - 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := c) (i := j ^ p - 1)).mpr h1
    rwa [hc] at this
  have h3 : ((j : ZMod p)) = 1 := by
    have h4 : (((j ^ p - 1 : ℤ)) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h2
    push_cast at h4
    rw [ZMod.pow_card] at h4
    exact sub_eq_zero.mp h4
  have h5 : (p : ℤ) ∣ j - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h3, sub_self]
  have h6 : c ^ (j - 1) = 1 :=
    (orderOf_dvd_iff_zpow_eq_one (x := c) (i := j - 1)).mp (by rwa [hc])
  have h7 : x * c * x⁻¹ = c := by
    rw [hj]
    have : c ^ j = c ^ (j - 1) * c := by rw [← zpow_add_one]; simp
    rw [this, h6, one_mul]
  calc x * c = x * c * x⁻¹ * x := by group
    _ = c * x := by rw [h7]

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mem_centralizer_thetaComponentsAt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hG : CFSG.Assembly.evenRank G ≤ 3) {a : G} {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p a)
    {x : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G)) (hxp : x ^ p = 1) :
    x ∈ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsAt_iff.mp hY
  have hH : CFSG.Assembly.evenRank (Subgroup.centralizer ({a} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans hG
  have hxp' : (⟨x, hx⟩ : Subgroup.centralizer ({a} : Set G)) ^ p = 1 :=
    Subtype.ext (by simpa using hxp)
  have hord : ∃ k : ℕ, orderOf (⟨x, hx⟩ : Subgroup.centralizer ({a} : Set G)) = p ^ k := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp
      (show orderOf (⟨x, hx⟩ : Subgroup.centralizer ({a} : Set G)) ∣ p ^ 1 from by
        rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hxp')
    exact ⟨k, hk⟩
  have hmem := selected_prime_elements_normalize_theta_components.1
    (Subgroup.centralizer ({a} : Set G)) hH p hp hp3 _ hord _ hY'
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ Subgroup.centralizer ({a} : Set G)
  · have := Subgroup.mem_normalizer_iff.mp hmem ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hgY
      exact absurd (hYC hgY) hg
    · intro hxgY
      have h1 : x * g * x⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := hYC hxgY
      refine absurd ?_ hg
      have h2 := mul_mem (mul_mem (inv_mem hx) h1) hx
      simpa [mul_assoc] using h2

end Helpers

variable {G : Type} [Group G] [Finite G]

theorem inSec10EightMoving_of_inspections (hS : SchreierFor InCatalog)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (h68 : Sec6EightMultipliers) (hSU : SUFiveNormalizingSubgroupsContained) :
    InSec10EightMoving := by
  intro G _ _ p A h c hcA hc1 L hL
  obtain ⟨hL0, hLc⟩ := hL
  obtain ⟨hq, hAL, hker⟩ := moving_maximal_data_at hS h hL0 hcA hc1 hLc
  have hp := sectionTenSetup_prime h
  have hp3 := sectionTenSetup_three_lt h
  have hG3 : CFSG.twoLocalOddRank G ≤ 3 := h.2.2.2.2.1.le
  have hθ : aschbacherSolvableCore p L ≤ Subgroup.center L := theta_le_center_of_quasisimple hp hq
  by_cases hpZ : p ∣ Nat.card (Subgroup.center L)
  · right
    have hLcent : L ≤ Subgroup.centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.mp hLc).1
    have hcat : Catalog (L ⧸ Subgroup.center L) := by
      have := h.1
      exact catalog_quotient_center_of_quasisimple h.2.2.1 hbridge h.2.1 hc1 hLcent hq
    obtain ⟨hp5, hZ5, n, hn, hmodel⟩ := h68 G hG3 L p hp hp3 hq hcat hpZ
    subst hp5
    have hAe : IsElementaryAbelian 5 A := h.2.2.2.2.2.2.1
    have hcord : orderOf c = 5 := by
      have hcp : c ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) c hcA
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hcp) with h2 | h2
      · exact absurd (orderOf_eq_one_iff.mp h2) hc1
      · exact h2
    obtain ⟨-, S, hSL, hS1, hS2, hAS, -⟩ := hL0.1
    have hzc5 : Nat.card (Subgroup.zpowers c) = 5 := by rw [Nat.card_zpowers, hcord]
    have hcL : Subgroup.zpowers c ≤ L := hSU G hG3 L n hn hq hZ5 hmodel (Subgroup.zpowers c)
      ((Subgroup.zpowers_le).mpr (hAL hcA)) hzc5
      ⟨S, hS1, hS2, hSL, (Subgroup.zpowers_le).mpr hcA |>.trans hAS⟩
    have hzle : Subgroup.zpowers c ≤ (Subgroup.center L).map L.subtype := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hxL : c ^ k ∈ L := hcL (Subgroup.zpow_mem_zpowers c k)
      refine ⟨⟨c ^ k, hxL⟩, Subgroup.mem_center_iff.mpr fun l => ?_, rfl⟩
      apply Subtype.ext
      have hcl : Commute (l : G) c := Subgroup.mem_centralizer_singleton_iff.mp (hLcent l.2)
      exact (hcl.zpow_right k).eq
    have hZcard : Nat.card ((Subgroup.center L).map L.subtype) = 5 := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hZ5]
    refine ⟨rfl, ?_, hZ5, ⟨n, hn, hmodel⟩, ?_⟩
    · exact (Subgroup.eq_of_le_of_card_ge hzle (by rw [hZcard, hzc5])).symm
    · intro X hXc hX5 hXS
      have hXN : X ≤ Subgroup.normalizer (L : Set G) := by
        intro x hx
        have hxp : x ^ 5 = 1 := by
          have := pow_card_eq_one' (x := (⟨x, hx⟩ : X))
          rw [hX5] at this
          simpa using congrArg Subtype.val this
        have hxc : x * c = c * x :=
          commute_of_mem_normalizer_zpowers_of_orderOf hp hcord hxp (hXc hx)
        have hxcent : x ∈ Subgroup.centralizer ({c} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr hxc
        have hGe : CFSG.Assembly.evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq h).le
        exact mem_normalizer_of_mem_centralizer_thetaComponentsAt hp hp3 hGe hLc hxcent hxp
      exact hSU G hG3 L n hn hq hZ5 hmodel X hXN hX5 hXS
  · left
    have hcen := center_le_theta_of_not_dvd hp hpZ
    have heq : aschbacherSolvableCore p L = Subgroup.center L := le_antisymm hθ hcen
    exact (QuotientGroup.quotientMulEquivOfEq heq).isSimpleGroup_congr.mpr hq.2.1

end CFSG.RankThree.PartOne
