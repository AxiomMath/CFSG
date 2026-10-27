module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.StandardType

variable {G : Type*} [Group G]

private def ggA : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

private def ggB : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

private lemma ggA_mem : ggA ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp only [ggA, Equiv.Perm.sign_mul]
  rw [Equiv.Perm.sign_swap (show (0 : Fin 6) ≠ 1 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 6) ≠ 2 by decide)]
  decide

private lemma ggB_mem : ggB ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp only [ggB, Equiv.Perm.sign_mul]
  rw [Equiv.Perm.sign_swap (show (3 : Fin 6) ≠ 4 by decide),
    Equiv.Perm.sign_swap (show (4 : Fin 6) ≠ 5 by decide)]
  decide

private def ggAA : alternatingGroup (Fin 6) := ⟨ggA, ggA_mem⟩

private def ggAB : alternatingGroup (Fin 6) := ⟨ggB, ggB_mem⟩

private lemma ggAA_comm : ggAA * ggAB = ggAB * ggAA := by decide

private lemma ggAA_pow_three : ggAA ^ 3 = 1 := by decide

private lemma ggAB_pow_three : ggAB ^ 3 = 1 := by decide

private lemma ggAA_ne_one : ggAA ≠ 1 := by decide

private lemma ggAB_ne_one : ggAB ≠ 1 := by decide

private lemma ggAA_ne_ggAB : ggAA ≠ ggAB := by decide

private lemma ggAA_mul_ne_one : ggAA * ggAB ≠ 1 := by decide

private theorem pow_eq_one_of_mem_sup_zpowers {G : Type*} [Group G] {p : ℕ} {a b : G}
    (hab : a * b = b * a) (ha : a ^ p = 1) (hb : b ^ p = 1) {g : G}
    (hg : g ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : g ^ p = 1 := by
  have hc : Commute a b := hab
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    have hcb : Subgroup.centralizer (Subgroup.zpowers b : Set G) =
        Subgroup.centralizer {b} := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcb, Subgroup.mem_centralizer_singleton_iff]
    exact hab
  have hg' : g ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hg'
  obtain ⟨u, hu, v, hv, rfl⟩ := hg'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hij : Commute (a ^ i) (b ^ j) := hc.zpow_zpow i j
  rw [hij.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm,
    zpow_mul, mul_comm (j : ℤ), zpow_mul, zpow_natCast, zpow_natCast, ha, hb, one_zpow, one_zpow,
    mul_one]

theorem exists_noncyclic_three_group_of_alt_six {J L : Subgroup G} (hJL : J ≤ L)
    (φ : ↥J ≃* alternatingGroup (Fin 6)) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  classical
  let uJ : ↥J := φ.symm ggAA
  let vJ : ↥J := φ.symm ggAB
  let u : G := (uJ : G)
  let v : G := (vJ : G)
  have huJ_ne_one : uJ ≠ 1 := by
    change φ.symm ggAA ≠ 1
    intro h
    have h2 : ggAA = 1 := by
      have h3 := congrArg φ h
      rwa [MulEquiv.apply_symm_apply, map_one] at h3
    exact ggAA_ne_one h2
  have hvJ_ne_one : vJ ≠ 1 := by
    change φ.symm ggAB ≠ 1
    intro h
    have h2 : ggAB = 1 := by
      have h3 := congrArg φ h
      rwa [MulEquiv.apply_symm_apply, map_one] at h3
    exact ggAB_ne_one h2
  have huJ_ne_vJ : uJ ≠ vJ := by
    change φ.symm ggAA ≠ φ.symm ggAB
    intro h
    have h2 : ggAA = ggAB := by
      have h3 := congrArg φ h
      rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
    exact ggAA_ne_ggAB h2
  have huvJ_ne_one : uJ * vJ ≠ 1 := by
    change φ.symm ggAA * φ.symm ggAB ≠ 1
    intro h
    have h2 : ggAA * ggAB = 1 := by
      have h3 := congrArg φ h
      rwa [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, map_one] at h3
    exact ggAA_mul_ne_one h2
  have huv : u * v = v * u := by
    change (uJ : G) * (vJ : G) = (vJ : G) * (uJ : G)
    have h : uJ * vJ = vJ * uJ := by
      have h := congrArg φ.symm ggAA_comm
      rw [map_mul, map_mul] at h
      exact h
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, h]
  have hu3 : u ^ 3 = 1 := by
    change (uJ : G) ^ 3 = 1
    have h : uJ ^ 3 = 1 := by
      have h := congrArg φ.symm ggAA_pow_three
      rw [map_pow, map_one] at h
      exact h
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  have hv3 : v ^ 3 = 1 := by
    change (vJ : G) ^ 3 = 1
    have h : vJ ^ 3 = 1 := by
      have h := congrArg φ.symm ggAB_pow_three
      rw [map_pow, map_one] at h
      exact h
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  have hu_ne_one : u ≠ 1 := by
    change (uJ : G) ≠ 1
    intro h
    exact huJ_ne_one (Subtype.coe_injective (by simpa using h))
  have hv_ne_one : v ≠ 1 := by
    change (vJ : G) ≠ 1
    intro h
    exact hvJ_ne_one (Subtype.coe_injective (by simpa using h))
  have hu_ne_v : u ≠ v := by
    change (uJ : G) ≠ (vJ : G)
    intro h
    exact huJ_ne_vJ (Subtype.coe_injective h)
  have huvmul_ne_one : u * v ≠ 1 := by
    change (uJ : G) * (vJ : G) ≠ 1
    intro h
    exact huvJ_ne_one
      (Subtype.coe_injective (by simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h))
  have huvmul_ne_u : u * v ≠ u := by
    intro h
    exact hv_ne_one (mul_left_cancel (by rw [h, mul_one]))
  have huvmul_ne_v : u * v ≠ v := by
    intro h
    exact hu_ne_one (mul_right_cancel (by rw [h, one_mul]))
  let S : Subgroup G := Subgroup.zpowers u ⊔ Subgroup.zpowers v
  have hu_mem_J : u ∈ J := by change (uJ : G) ∈ J; exact uJ.2
  have hv_mem_J : v ∈ J := by change (vJ : G) ∈ J; exact vJ.2
  have hSL : S ≤ L := by
    change Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ L
    exact (sup_le (Subgroup.zpowers_le.mpr hu_mem_J)
      (Subgroup.zpowers_le.mpr hv_mem_J)).trans hJL
  have hP : IsPGroup 3 S := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_eq_one_of_mem_sup_zpowers huv hu3 hv3 x.2
  have hnc : ¬ IsCyclic S := by
    intro hcyc
    haveI : IsCyclic ↥S := hcyc
    obtain ⟨gS, hgS⟩ := IsCyclic.exists_generator (α := ↥S)
    have hcard : orderOf gS = Nat.card ↥S := orderOf_eq_card_of_forall_mem_zpowers hgS
    have hg3 : (gS : G) ^ 3 = 1 :=
      pow_eq_one_of_mem_sup_zpowers huv hu3 hv3 gS.2
    have hdvd : Nat.card ↥S ∣ 3 := by
      rw [← hcard, ← Subgroup.orderOf_coe gS]
      exact orderOf_dvd_of_pow_eq_one hg3
    have hle3 : Nat.card ↥S ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hne : Nat.card ↥S ≠ 0 := by
      intro h0
      rw [h0] at hdvd
      exact (by decide : ¬ (0 ∣ 3)) hdvd
    haveI : Finite ↥S := Nat.finite_of_card_ne_zero hne
    letI : Fintype ↥S := Fintype.ofFinite ↥S
    let uS : ↥S := ⟨u, Subgroup.mem_sup_left (Subgroup.mem_zpowers u)⟩
    let vS : ↥S := ⟨v, Subgroup.mem_sup_right (Subgroup.mem_zpowers v)⟩
    have huS_ne_one : uS ≠ 1 := by
      intro h
      exact hu_ne_one (congrArg (fun x : ↥S => (x : G)) h)
    have hvS_ne_one : vS ≠ 1 := by
      intro h
      exact hv_ne_one (congrArg (fun x : ↥S => (x : G)) h)
    have huS_ne_vS : uS ≠ vS := by
      intro h
      exact hu_ne_v (congrArg (fun x : ↥S => (x : G)) h)
    have huvS_ne_one : uS * vS ≠ 1 := by
      intro h
      apply huvmul_ne_one
      have h' := congrArg (fun x : ↥S => (x : G)) h
      simpa only [Subgroup.coe_mul, Subgroup.coe_one, uS, vS] using h'
    have huvS_ne_uS : uS * vS ≠ uS := by
      intro h
      apply huvmul_ne_u
      have h' := congrArg (fun x : ↥S => (x : G)) h
      simpa only [Subgroup.coe_mul, uS, vS] using h'
    have huvS_ne_vS : uS * vS ≠ vS := by
      intro h
      apply huvmul_ne_v
      have h' := congrArg (fun x : ↥S => (x : G)) h
      simpa only [Subgroup.coe_mul, uS, vS] using h'
    have hcard4 : ({1, uS, vS, uS * vS} : Finset ↥S).card = 4 := by
      rw [Finset.card_eq_four]
      exact ⟨1, uS, vS, uS * vS, Ne.symm huS_ne_one, Ne.symm hvS_ne_one,
        Ne.symm huvS_ne_one, huS_ne_vS, Ne.symm huvS_ne_uS, Ne.symm huvS_ne_vS, rfl⟩
    have h4 : 4 ≤ Nat.card ↥S := by
      rw [Nat.card_eq_fintype_card]
      calc 4 = ({1, uS, vS, uS * vS} : Finset ↥S).card := hcard4.symm
        _ ≤ (Finset.univ : Finset ↥S).card := Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card ↥S := Finset.card_univ
    omega
  exact ⟨S, hSL, hP, hnc⟩

end CFSG.StandardType
