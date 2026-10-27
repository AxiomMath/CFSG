module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S11.SecTenEight
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pElement_normalizes_thetaComponentsAt (he : evenRank G ≤ 3) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {b x : G} (hx : x ∈ centralizer ({b} : Set G))
    (hord : ∃ k : ℕ, orderOf x = p ^ k) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p b) :
    x ∈ normalizer (Y : Set G) := by
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsAt_iff.mp hY
  have hH : evenRank (centralizer ({b} : Set G)) ≤ 3 := (Sec9A.evenRank_subgroup_le _).trans he
  have hord' : ∃ k : ℕ, orderOf (⟨x, hx⟩ : centralizer ({b} : Set G)) = p ^ k := by
    obtain ⟨k, hk⟩ := hord
    exact ⟨k, by rw [← hk, ← Subgroup.orderOf_coe]⟩
  have hmem := selected_prime_elements_normalize_theta_components.1 (centralizer ({b} : Set G)) hH
    p hp hp3 _ hord' _ hY'
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ centralizer ({b} : Set G)
  · have := Subgroup.mem_normalizer_iff.mp hmem ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hgY
      exact absurd (hYC hgY) hg
    · intro hygY
      have h1 : x * g * x⁻¹ ∈ centralizer ({b} : Set G) := hYC hygY
      refine absurd ?_ hg
      have h2 := mul_mem (mul_mem (inv_mem hx) h1) hx
      simpa [mul_assoc] using h2

omit [Finite G] in
theorem exists_orderOf_pow_of_zpow {p : ℕ} (hp : p.Prime) {x : G}
    (hord : ∃ k : ℕ, orderOf x = p ^ k) (i : ℤ) : ∃ m : ℕ, orderOf (x ^ i) = p ^ m := by
  obtain ⟨k, hk⟩ := hord
  have h1 : orderOf (x ^ i) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk, pow_orderOf_eq_one,
      one_zpow]
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp h1
  exact ⟨m, hm⟩

theorem commutator_normalizes_thetaComponentsAt (he : evenRank G ≤ 3) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {b x : G} (hx : x ∈ centralizer ({b} : Set G))
    (hord : ∃ k : ℕ, orderOf x = p ^ k) {R : Subgroup G} (hRb : R ≤ centralizer ({b} : Set G))
    (hR : R ≤ ⁅R, zpowers x⁆) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p b) :
    R ≤ normalizer (Y : Set G) := by
  refine hR.trans ?_
  rw [Subgroup.commutator_le]
  intro r hr y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hxi : x ^ i ∈ centralizer ({b} : Set G) := zpow_mem hx i
  have hxio := exists_orderOf_pow_of_zpow hp hord i
  have hrC : r ∈ centralizer ({b} : Set G) := hRb hr
  have h1 : x ^ i ∈ normalizer (Y : Set G) :=
    pElement_normalizes_thetaComponentsAt he hp hp3 hxi hxio hY
  have h2 : r * x ^ i * r⁻¹ ∈ normalizer (Y : Set G) := by
    refine pElement_normalizes_thetaComponentsAt he hp hp3
      (mul_mem (mul_mem hrC hxi) (inv_mem hrC)) ?_ hY
    obtain ⟨m, hm⟩ := hxio
    exact ⟨m, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hm]⟩
  rw [commutatorElement_def]
  exact mul_mem h2 (inv_mem h1)

omit [Finite G] in
theorem acts_trivially_of_commutator {p : ℕ} {K R : Subgroup G} {x : G}
    (hRN : R ≤ normalizer (K : Set G)) (hxN : x ∈ normalizer (K : Set G))
    (hx : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K)
    (hR : R ≤ ⁅R, zpowers x⁆) :
    ∀ r ∈ R, ∀ k ∈ K, r * k * r⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K := by
  set N := normalizer (K : Set G) with hN
  set φ := thetaQuotientConj p K with hφ
  have hker : ∀ g : N, φ g = 1 ↔
      ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K :=
    fun g => thetaQuotientConj_eq_one_iff p K g
  have hxker : φ ⟨x, hxN⟩ = 1 := (hker _).mpr hx
  have hzp : ∀ y ∈ zpowers x, ∃ hy : y ∈ N, φ ⟨y, hy⟩ = 1 := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨zpow_mem hxN i, ?_⟩
    have : (⟨x ^ i, zpow_mem hxN i⟩ : N) = (⟨x, hxN⟩ : N) ^ i := rfl
    rw [this, map_zpow, hxker, one_zpow]
  have hcomm : ⁅R, zpowers x⁆ ≤ φ.ker.map N.subtype := by
    rw [Subgroup.commutator_le]
    intro r hr y hy
    obtain ⟨hyN, hy1⟩ := hzp y hy
    refine ⟨⟨r, hRN hr⟩ * ⟨y, hyN⟩ * ⟨r, hRN hr⟩⁻¹ * ⟨y, hyN⟩⁻¹, ?_, ?_⟩
    · show _ ∈ φ.ker
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hy1]
      group
    · simp [commutatorElement_def]
  intro r hr k hk
  obtain ⟨g, hg, hgr⟩ := hcomm (hR hr)
  have hg1 : φ g = 1 := hg
  have := (hker g).mp hg1 k hk
  have hgr' : (g : G) = r := by simpa using hgr
  rwa [hgr'] at this


theorem mem_thetaComponents_of_quasisimple {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {Z : Subgroup X} (hZ : CFSG.IsQuasisimple ↥Z) (hsub : Z.IsSubnormal) :
    Z ∈ thetaComponents p X := by
  refine ⟨hZ.1, hsub, ?_⟩
  have hθ := theta_le_center_of_quasisimple hp hZ
  have := aschbacherSolvableCore_normal p ↥Z
  exact (CFSG.LocalCores.quasisimple_central_quotient hZ (aschbacherSolvableCore p ↥Z) hθ).1


omit [Finite G] in
theorem acts_trivially_zpow {p : ℕ} {K : Subgroup G} {x : G} (hxN : x ∈ normalizer (K : Set G))
    (hx : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K) (n : ℤ) :
    ∀ k ∈ K, x ^ n * k * (x ^ n)⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K := by
  have hxker : thetaQuotientConj p K ⟨x, hxN⟩ = 1 := (thetaQuotientConj_eq_one_iff p K _).mpr hx
  have h1 : thetaQuotientConj p K ⟨x ^ n, zpow_mem hxN n⟩ = 1 := by
    have : (⟨x ^ n, zpow_mem hxN n⟩ : normalizer (K : Set G)) =
        (⟨x, hxN⟩ : normalizer (K : Set G)) ^ n := rfl
    rw [this, map_zpow, hxker, one_zpow]
  exact (thetaQuotientConj_eq_one_iff p K _).mp h1

end CFSG.RankThree.PartOne
