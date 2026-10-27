module

public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.KC.UnitaryEndpointStatements
public import CFSG.RankThree.Classical.SteinbergBJUnitaryDefiningComponent
public import CFSG.RankThree.SteinbergR3EUnitaryOuterOrder

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.Automorphisms CFSG.RankThree.Classical
open CFSG.Assembly.RankThreeEven (localRank)

namespace KCUnitaryDefining

theorem planeLocalCoreInner_unitaryPSU {p f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hp3 : 3 < p) (hn : n = 3 ∨ n = 4) :
    PlaneLocalCoreInner p (unitaryPSU h n) (fun _ => True) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  intro B hB A hAInn hA hAcard _ t htA ht1
  have := hA
  have hθ : ∀ a ∈ A, a ≠ 1 →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
    intro a haA ha1
    have hap : orderOf a = p :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a haA) ha1
    exact (unitary_three_four_inner_defining_centralizer_local_cores_trivial h hp3 hn B hB
      (hAInn haA) hap).2
  have h1 := hθ t htA ht1
  have h2 : autThetaT p B A = ⊥ := by
    apply le_bot_iff.mp
    calc autThetaT p B A ≤ inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (unitaryPSU h n)))) :=
        (iInf_le _ t).trans ((iInf_le _ htA).trans (iInf_le _ ht1))
      _ = ⊥ := h1
  rw [autPlaneProduct, h1, h2, Subgroup.commutator_bot_left, bot_sup_eq]

theorem mem_inner_of_pow_eq_one {T : Type*} [Group T] {p : ℕ} (hp : p.Prime)
    (hout : ¬ p ∣ Nat.card (Outer T)) {x : MulAut T} (hx : x ^ p = 1) :
    x ∈ (MulAut.conj : T →* MulAut T).range := by
  set y : MulAut T ⧸ inner T := QuotientGroup.mk x with hy
  have h1 : orderOf y ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hy, ← QuotientGroup.mk_pow, hx]
    rfl
  have h2 : orderOf y ∣ Nat.card (Outer T) := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime hp).mp h1 with h3 | h3
  · exact (QuotientGroup.eq_one_iff (N := inner T) x).mp (orderOf_eq_one_iff.mp h3)
  · rw [h3] at h2
    exact absurd h2 hout

theorem not_dvd_outer_unitaryPSU {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp3 : 3 < p) (hpar : (n = 3 ∧ 1 ≤ f ∧ f ≤ 3) ∨ (n = 4 ∧ f = 1)) :
    ¬ p ∣ Nat.card (Outer (unitaryPSU h n)) := by
  have hn3 : 3 ≤ n := by omega
  have hq := not_three_and_pow_eq_two (n := n) h hp3
  intro hd
  have h1 := hd.trans (unitary_outer_order_divides_field_norm_one_bound h hn3 hq)
  have hf1 : 1 ≤ f := by omega
  have hf3 : f ≤ 3 := by omega
  rcases (Nat.Prime.dvd_mul h.prime).mp h1 with h2 | h2
  · have h6 : p ≤ 6 := by
      have := Nat.le_of_dvd (by omega) h2
      omega
    interval_cases p
    · exact absurd h.prime (by norm_num)
    · interval_cases f <;> omega
    · exact absurd h.prime (by norm_num)
  · have : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p (by omega : f ≠ 0))).mp h2
    exact h.prime.one_lt.ne' (Nat.dvd_one.mp this)

theorem actualPlane_le_inner {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElementaryAbelian p E) {L : Subgroup G}
    (hinn : ∀ x : MulAut (L ⧸ center L), x ^ p = 1 →
      x ∈ (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range) :
    actualPlane L E ≤ (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range := by
  have := hE
  rintro _ ⟨e, he, rfl⟩
  apply hinn
  have hpow : e ^ p = 1 := by
    apply Subtype.ext
    have h1 : ((e : normalizer (L : Set G)) : G) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian _ (Subgroup.mem_subgroupOf.mp he)
    simpa using h1
  rw [← map_pow, hpow, map_one]

end KCUnitaryDefining

theorem unitary_defining_prime_actual_component_local_core_product_centralizes :
    UnitaryDefiningPrimeActualComponentLocalCoreProductCentralizes := by
  intro X _ _ p hp hp3 N _ hN hX E hE hEcard t htE ht1 L hL n f hmod hEL hSL
  have hp2 : p ≠ 2 := by omega
  have hpar := unitary_defining_prime_actual_component_parameter_restriction hp hp3 N hN hX L hmod
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let φ : L ⧸ center L ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  have hn34 : n = 3 ∨ n = 4 := by omega
  have hplane := PlaneLocalCoreInner.of_mulEquiv hp φ
    (KCUnitaryDefining.planeLocalCoreInner_unitaryPSU hU hp3 hn34)
  have hout := KCUnitaryDefining.not_dvd_outer_unitaryPSU hU hp3 hpar
  have hinnAll : ∀ x : MulAut (L ⧸ center L), x ^ p = 1 →
      x ∈ (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range := by
    intro x hx
    have h1 := KCUnitaryDefining.mem_inner_of_pow_eq_one hp hout
      (x := MulAut.congr φ x) (by rw [← map_pow, hx, map_one])
    have h2 : MulAut.congr φ x ∈
        ((MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range).map
          (MulAut.congr φ).toMonoidHom := by
      rw [map_conj_range_mulAutCongr φ]
      exact h1
    have h3 := Subgroup.mem_map_equiv.mp h2
    rwa [MulEquiv.symm_apply_apply] at h3
  have hinner := KCUnitaryDefining.actualPlane_le_inner (L := L) hE hinnAll
  obtain ⟨h1, h2, h3⟩ := component_local_core_centralizes_of_inner_plane hp hp2 hE hEcard htE ht1
    hL hEL hSL hplane (Or.inr ⟨trivial, hinner⟩)
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t htE ht1
  exact ⟨hset, h3.trans (Subgroup.centralizer_le_normalizer _), h1, h2, h3⟩

end CFSG.RankThree.PartOne
