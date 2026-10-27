module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.SzI47J2NoA4

open CFSG.ShultStronglyClosedTI.InvolutionCounting

section Fixed

variable {G : Type*} [Group G]

@[expose, instance_reducible] def conjAction (P : Subgroup G) (S : Set G)
    (hS : ∀ k ∈ P, ∀ x ∈ S, k * x * k⁻¹ ∈ S) : MulAction P S where
  smul k x := ⟨k * x * k⁻¹, hS k k.2 x x.2⟩
  one_smul x := Subtype.ext (by show (1 : P).1 * x.1 * (1 : P).1⁻¹ = x.1; simp)
  mul_smul a b x := Subtype.ext (by
    show (a * b).1 * x.1 * (a * b).1⁻¹ = a.1 * (b.1 * x.1 * b.1⁻¹) * a.1⁻¹
    simp [mul_assoc])

theorem card_modEq_card_fixed (p : ℕ) [Fact p.Prime] (P : Subgroup G) (hP : IsPGroup p P)
    (S : Set G) [Finite S] (hS : ∀ k ∈ P, ∀ x ∈ S, k * x * k⁻¹ ∈ S) :
    Nat.card S ≡ Nat.card {x : G | x ∈ S ∧ ∀ k ∈ P, k * x = x * k} [MOD p] := by
  let _ := conjAction P S hS
  have h := hP.card_modEq_card_fixedPoints S
  have e : MulAction.fixedPoints P S ≃ {x : G | x ∈ S ∧ ∀ k ∈ P, k * x = x * k} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, fun k hk => by
        have h2 := congrArg Subtype.val (MulAction.mem_fixedPoints.mp x.2 ⟨k, hk⟩)
        exact mul_inv_eq_iff_eq_mul.mp h2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, MulAction.mem_fixedPoints.mpr fun k =>
        Subtype.ext (mul_inv_eq_iff_eq_mul.mpr (x.2.2 k k.2))⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [← Nat.card_congr e]
  exact h

end Fixed

section Involutions

variable {K : Type*} [Group K] [Finite K]

@[expose] def invSet (K : Type*) [Group K] : Set K := {u | u * u = 1 ∧ u ≠ 1}

theorem isConj_of_mem_invSet {z u : K} (hz : z * z = 1)
    (huniq : ∀ w : K, w * w = 1 → w * z = z * w → w = 1 ∨ w = z)
    (hu : u * u = 1) (hu1 : u ≠ 1) : IsConj z u := by
  by_contra hzu
  obtain ⟨d, hd0, hd⟩ := exists_orderOf_mul_eq_two_mul hz hu hzu
  have hw2 : orderOf ((z * u) ^ d) = 2 := orderOf_pow_half hd hd0
  have hww : (z * u) ^ d * (z * u) ^ d = 1 := mul_self_eq_one_of_orderOf_eq_two hw2
  have hmem : (z * u) ^ d ∈ Subgroup.zpowers (z * u) := Subgroup.npow_mem_zpowers _ d
  have hzc : Commute z ((z * u) ^ d) :=
    commute_of_mem_zpowers (conj_mul_left_eq_inv hz hu) hmem hww
  have huc : Commute u ((z * u) ^ d) :=
    commute_of_mem_zpowers (conj_mul_right_eq_inv hz hu) hmem hww
  have hw1 : (z * u) ^ d ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hwz : (z * u) ^ d = z := by
    rcases huniq _ hww hzc.symm.eq with h | h
    · exact absurd h hw1
    · exact h
  have huz : u * z = z * u := by
    have h1 := huc.eq
    rwa [hwz] at h1
  rcases huniq u hu huz with h | h
  · exact hu1 h
  · exact hzu (h ▸ IsConj.refl z)

theorem invSet_eq_conjugatesOf {z : K} (hz : z * z = 1) (hz1 : z ≠ 1)
    (huniq : ∀ w : K, w * w = 1 → w * z = z * w → w = 1 ∨ w = z) :
    invSet K = _root_.conjugatesOf z := by
  ext u
  constructor
  · rintro ⟨hu, hu1⟩
    exact isConj_of_mem_invSet hz huniq hu hu1
  · intro h
    refine ⟨mul_self_eq_one_of_isConj hz h, fun h1 => hz1 ?_⟩
    rw [h1] at h
    exact isConj_one_right.mp h.symm

theorem card_centralizer_mul_card_invSet {z : K} (hz : z * z = 1) (hz1 : z ≠ 1)
    (huniq : ∀ w : K, w * w = 1 → w * z = z * w → w = 1 ∨ w = z) :
    Nat.card (Subgroup.centralizer ({z} : Set K)) * Nat.card (invSet K) = Nat.card K := by
  rw [invSet_eq_conjugatesOf hz hz1 huniq]
  exact card_centralizer_mul_card_conjugatesOf z

theorem odd_card_invSet {z : K} (hz : z * z = 1) (hz1 : z ≠ 1)
    (huniq : ∀ w : K, w * w = 1 → w * z = z * w → w = 1 ∨ w = z) :
    Odd (Nat.card (invSet K)) := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hS : ∀ k ∈ Subgroup.zpowers z, ∀ x ∈ invSet K, k * x * k⁻¹ ∈ invSet K := by
    rintro k - x ⟨hx, hx1⟩
    refine ⟨?_, fun h => hx1 ?_⟩
    · calc k * x * k⁻¹ * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
        _ = 1 := by rw [hx]; group
    · have h2 : x = k⁻¹ * (k * x * k⁻¹) * k := by group
      rw [h2, h]
      group
  have hmod := card_modEq_card_fixed 2 (Subgroup.zpowers z) hP (invSet K) hS
  have hfix : {x : K | x ∈ invSet K ∧ ∀ k ∈ Subgroup.zpowers z, k * x = x * k} = {z} := by
    ext x
    constructor
    · rintro ⟨⟨hx, hx1⟩, hc⟩
      rcases huniq x hx (hc z (Subgroup.mem_zpowers z)).symm with h | h
      · exact absurd h hx1
      · exact h
    · rintro (rfl : x = z)
      refine ⟨⟨hz, hz1⟩, fun k hk => ?_⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      exact ((Commute.refl x).zpow_left m).eq
  rw [hfix] at hmod
  have h1 : Nat.card ({z} : Set K) = 1 := Nat.card_unique
  rw [h1] at hmod
  exact Nat.odd_iff.mpr (by simpa [Nat.ModEq] using hmod)

end Involutions

theorem false_of_commute_of_isConj {G : Type*} [Group G] [IsSimpleGroup G] {z g : G}
    (hz1 : z ≠ 1) (hg1 : g ≠ 1) (hC : Subgroup.centralizer ({z} : Set G) ≠ ⊤)
    (hcomm : ∀ u : G, IsConj z u → g * u = u * g) : False := by
  have hN : Subgroup.normalClosure ({z} : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({z} : Set G)) with
      h | h
    · exfalso
      apply hz1
      have hzN : z ∈ Subgroup.normalClosure ({z} : Set G) := Subgroup.subset_normalClosure rfl
      rw [h] at hzN
      exact hzN
    · exact h
  have hle : Subgroup.normalClosure ({z} : Set G) ≤ Subgroup.centralizer ({g} : Set G) := by
    unfold Subgroup.normalClosure
    rw [Subgroup.closure_le]
    intro u hu
    obtain ⟨a, ha, hua⟩ := Group.mem_conjugatesOfSet_iff.mp hu
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm u hua).symm
  have hgc : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : x ∈ Subgroup.normalClosure ({z} : Set G) := by
      rw [hN]
      trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h] at hgc
    exact hg1 hgc
  · apply hC
    rw [Subgroup.eq_top_iff']
    intro x
    have hx : z ∈ Subgroup.center G := by
      rw [h]
      trivial
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hx x)

end CFSG.Quasithin.SzI47J2NoA4
