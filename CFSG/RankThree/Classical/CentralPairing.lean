module

public import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools

public section

namespace CFSG.RankThree.Classical

open scoped commutatorElement
open CFSG.SectionRank.OddCover

section Central

variable {G : Type*} [Group G]

theorem commutatorElement_central_mul_left {c : G} (hc : c ∈ Subgroup.center G) (x y : G) :
    ⁅c * x, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have : c * x * y * (x⁻¹ * c⁻¹) * y⁻¹ = c * (x * y * x⁻¹) * c⁻¹ * y⁻¹ := by group
  rw [this, ← Subgroup.mem_center_iff.mp hc (x * y * x⁻¹), mul_inv_cancel_right]

theorem commutatorElement_central_mul' {a b c d : G} (hc : c ∈ Subgroup.center G)
    (hd : d ∈ Subgroup.center G) : ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_central_mul_left hc, ← commutatorElement_inv,
    commutatorElement_central_mul_left hd, commutatorElement_inv]

theorem commutatorElement_conj_of_mem_center {a b : G} (h : ⁅a, b⁆ ∈ Subgroup.center G) (g : G) :
    ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = ⁅a, b⁆ := by
  have : ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [this, Subgroup.mem_center_iff.mp h g, mul_inv_cancel_right]

end Central

variable {Y X : Type*} [Group Y] [Group X] {φ : Y →* X} (hφ : Function.Surjective φ)

noncomputable def lift (x : X) : Y := Classical.choose (hφ x)

theorem map_lift (x : X) : φ (lift hφ x) = x := Classical.choose_spec (hφ x)

variable {V : Type*} [AddCommGroup V] (ρ : Multiplicative V →* X)

@[expose, reducible] def centerCommGroup (Y : Type*) [Group Y] : CommGroup (Subgroup.center Y) :=
  { (inferInstance : Group (Subgroup.center Y)) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }

noncomputable def liftPair (v w : V) : Y :=
  ⁅lift hφ (ρ (Multiplicative.ofAdd v)), lift hφ (ρ (Multiplicative.ofAdd w))⁆

theorem commute_rho (v w : V) :
    ρ (Multiplicative.ofAdd v) * ρ (Multiplicative.ofAdd w) =
      ρ (Multiplicative.ofAdd w) * ρ (Multiplicative.ofAdd v) := by
  rw [← map_mul ρ, ← map_mul ρ, mul_comm (Multiplicative.ofAdd v)]

variable (hZ : φ.ker ≤ Subgroup.center Y)
include hZ

theorem commutatorElement_eq_liftPair {a b : Y} {v w : V}
    (ha : φ a = ρ (Multiplicative.ofAdd v)) (hb : φ b = ρ (Multiplicative.ofAdd w)) :
    ⁅a, b⁆ = liftPair hφ ρ v w := by
  set a₀ := lift hφ (ρ (Multiplicative.ofAdd v))
  set b₀ := lift hφ (ρ (Multiplicative.ofAdd w))
  have hc : a * a₀⁻¹ ∈ Subgroup.center Y := hZ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha, map_lift, mul_inv_cancel])
  have hd : b * b₀⁻¹ ∈ Subgroup.center Y := hZ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb, map_lift, mul_inv_cancel])
  have := commutatorElement_central_mul' (a := a₀) (b := b₀) hc hd
  rw [inv_mul_cancel_right, inv_mul_cancel_right] at this
  exact this

theorem liftPair_mem_center (v w : V) : liftPair hφ ρ v w ∈ Subgroup.center Y := by
  refine hZ ?_
  rw [MonoidHom.mem_ker, liftPair, map_commutatorElement, map_lift, map_lift,
    commutatorElement_eq_one_iff_mul_comm]
  exact commute_rho ρ v w

theorem liftPair_add_left (v v' w : V) :
    liftPair hφ ρ (v + v') w = liftPair hφ ρ v w * liftPair hφ ρ v' w := by
  rw [← commutatorElement_eq_liftPair hφ ρ hZ (a := lift hφ (ρ (Multiplicative.ofAdd v)) *
      lift hφ (ρ (Multiplicative.ofAdd v'))) (b := lift hφ (ρ (Multiplicative.ofAdd w)))
      (by rw [map_mul, map_lift, map_lift, ← map_mul]; rfl) (map_lift _ _)]
  exact commutatorElement_mul_left_of_mem_center (liftPair_mem_center hφ ρ hZ v' w)

theorem liftPair_add_right (v w w' : V) :
    liftPair hφ ρ v (w + w') = liftPair hφ ρ v w * liftPair hφ ρ v w' := by
  rw [← commutatorElement_eq_liftPair hφ ρ hZ (a := lift hφ (ρ (Multiplicative.ofAdd v)))
      (b := lift hφ (ρ (Multiplicative.ofAdd w)) * lift hφ (ρ (Multiplicative.ofAdd w')))
      (map_lift _ _) (by rw [map_mul, map_lift, map_lift, ← map_mul]; rfl)]
  exact commutatorElement_mul_right_of_mem_center (liftPair_mem_center hφ ρ hZ v w')

omit hZ in
theorem liftPair_self (v : V) : liftPair hφ ρ v v = 1 :=
  commutatorElement_self _

theorem liftPair_zero_left (w : V) : liftPair hφ ρ 0 w = 1 := by
  have h := liftPair_add_left hφ ρ hZ (0 : V) 0 w
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem liftPair_nsmul_left (n : ℕ) (v w : V) :
    liftPair hφ ρ (n • v) w = liftPair hφ ρ v w ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, liftPair_zero_left hφ ρ hZ]
  | succ n ih => rw [succ_nsmul, liftPair_add_left hφ ρ hZ, ih, pow_succ]

theorem liftPair_zero_right (v : V) : liftPair hφ ρ v 0 = 1 := by
  have h := liftPair_add_right hφ ρ hZ v (0 : V) 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem liftPair_nsmul_right (n : ℕ) (v w : V) :
    liftPair hφ ρ v (n • w) = liftPair hφ ρ v w ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, liftPair_zero_right hφ ρ hZ]
  | succ n ih => rw [succ_nsmul, liftPair_add_right hφ ρ hZ, ih, pow_succ]

theorem liftPair_conj' (g : X) {v v' w w' : V}
    (hv : g * ρ (Multiplicative.ofAdd v) * g⁻¹ = ρ (Multiplicative.ofAdd v'))
    (hw : g * ρ (Multiplicative.ofAdd w) * g⁻¹ = ρ (Multiplicative.ofAdd w')) :
    liftPair hφ ρ v' w' = liftPair hφ ρ v w := by
  set ĝ := lift hφ g
  have h1 : φ (ĝ * lift hφ (ρ (Multiplicative.ofAdd v)) * ĝ⁻¹) = ρ (Multiplicative.ofAdd v') := by
    rw [map_mul, map_mul, map_inv, map_lift, map_lift, hv]
  have h2 : φ (ĝ * lift hφ (ρ (Multiplicative.ofAdd w)) * ĝ⁻¹) = ρ (Multiplicative.ofAdd w') := by
    rw [map_mul, map_mul, map_inv, map_lift, map_lift, hw]
  rw [← commutatorElement_eq_liftPair hφ ρ hZ h1 h2]
  exact commutatorElement_conj_of_mem_center (liftPair_mem_center hφ ρ hZ v w) ĝ

theorem liftPair_conj (g : X) (τ : V → V)
    (hτ : ∀ v, g * ρ (Multiplicative.ofAdd v) * g⁻¹ = ρ (Multiplicative.ofAdd (τ v)))
    (v w : V) : liftPair hφ ρ (τ v) (τ w) = liftPair hφ ρ v w := by
  set ĝ := lift hφ g
  have hlift : ∀ u, φ (ĝ * lift hφ (ρ (Multiplicative.ofAdd u)) * ĝ⁻¹) =
      ρ (Multiplicative.ofAdd (τ u)) := fun u => by
    rw [map_mul, map_mul, map_inv, map_lift, map_lift, hτ]
  rw [← commutatorElement_eq_liftPair hφ ρ hZ (hlift v) (hlift w)]
  exact commutatorElement_conj_of_mem_center (liftPair_mem_center hφ ρ hZ v w) ĝ

theorem liftPair_eq_one_of_weight {p : ℕ} (hp : p.Prime) {v w : V} (hpv : p • v = 0)
    {s t : ℕ} (hst : 1 ≤ s * t) (hcop : ¬ p ∣ s * t - 1)
    (hinv : liftPair hφ ρ (s • v) (t • w) = liftPair hφ ρ v w) : liftPair hφ ρ v w = 1 := by
  set z := liftPair hφ ρ v w
  have h0 : liftPair hφ ρ (s • v) (t • w) = z ^ (s * t) := by
    rw [liftPair_nsmul_left hφ ρ hZ, liftPair_nsmul_right hφ ρ hZ, ← pow_mul, mul_comm]
  have h1 : z ^ (s * t) = z := h0.symm.trans hinv
  have h2 : z ^ (s * t - 1) = 1 := by
    have : z ^ (s * t - 1) * z = 1 * z := by
      rw [← pow_succ, Nat.sub_add_cancel hst, h1, one_mul]
    exact mul_right_cancel this
  have h3 : z ^ p = 1 := by
    rw [← liftPair_nsmul_left hφ ρ hZ, hpv, liftPair_zero_left hφ ρ hZ]
  have hg : z ^ Nat.gcd (s * t - 1) p = 1 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
  rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcop).symm,
    pow_one] at hg

theorem mul_comm_of_liftPair_eq_one (h : ∀ v w, liftPair hφ ρ v w = 1) {a b : Y}
    (ha : φ a ∈ ρ.range) (hb : φ b ∈ ρ.range) : a * b = b * a := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨w, hw⟩ := hb
  have := commutatorElement_eq_liftPair hφ ρ hZ (v := v.toAdd) (w := w.toAdd) hv.symm hw.symm
  rw [h] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

@[expose] noncomputable def liftPairAdd (v w : V) : Additive (Subgroup.center Y) :=
  Additive.ofMul ⟨liftPair hφ ρ v w, liftPair_mem_center hφ ρ hZ v w⟩

theorem liftPairAdd_eq_zero_iff (v w : V) :
    liftPairAdd hφ ρ hZ v w = 0 ↔ liftPair hφ ρ v w = 1 := by
  rw [liftPairAdd]
  constructor
  · intro h
    have := congrArg (fun x : Additive (Subgroup.center Y) => ((Additive.toMul x : _) : Y)) h
    simpa using this
  · intro h
    apply Additive.toMul.injective
    exact Subtype.ext h

theorem liftPairAdd_congr {v w v' w' : V} (h : liftPair hφ ρ v w = liftPair hφ ρ v' w') :
    liftPairAdd hφ ρ hZ v w = liftPairAdd hφ ρ hZ v' w' := by
  apply Additive.toMul.injective
  exact Subtype.ext h

theorem liftPairAdd_add_left (v v' w : V) :
    liftPairAdd hφ ρ hZ (v + v') w = liftPairAdd hφ ρ hZ v w + liftPairAdd hφ ρ hZ v' w := by
  apply Additive.toMul.injective
  exact Subtype.ext (liftPair_add_left hφ ρ hZ v v' w)

theorem liftPairAdd_add_right (v w w' : V) :
    liftPairAdd hφ ρ hZ v (w + w') = liftPairAdd hφ ρ hZ v w + liftPairAdd hφ ρ hZ v w' := by
  apply Additive.toMul.injective
  exact Subtype.ext (liftPair_add_right hφ ρ hZ v w w')

theorem liftPairAdd_self (v : V) : liftPairAdd hφ ρ hZ v v = 0 :=
  (liftPairAdd_eq_zero_iff hφ ρ hZ v v).mpr (liftPair_self hφ ρ v)

theorem liftPair_sum_left {ι : Type*} (s : Finset ι) (a : ι → V) (w : V)
    (h : ∀ i ∈ s, liftPair hφ ρ (a i) w = 1) : liftPair hφ ρ (∑ i ∈ s, a i) w = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, liftPair_zero_left hφ ρ hZ]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, liftPair_add_left hφ ρ hZ, h i (Finset.mem_insert_self i s),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj), one_mul]

theorem liftPair_sum_right {κ : Type*} (t : Finset κ) (v : V) (b : κ → V)
    (h : ∀ j ∈ t, liftPair hφ ρ v (b j) = 1) : liftPair hφ ρ v (∑ j ∈ t, b j) = 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, liftPair_zero_right hφ ρ hZ]
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, liftPair_add_right hφ ρ hZ, h j (Finset.mem_insert_self j t),
      ih fun k hk => h k (Finset.mem_insert_of_mem hk), one_mul]

theorem liftPair_eq_one_of_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (a : ι → V)
    (b : κ → V) (h : ∀ i ∈ s, ∀ j ∈ t, liftPair hφ ρ (a i) (b j) = 1) :
    liftPair hφ ρ (∑ i ∈ s, a i) (∑ j ∈ t, b j) = 1 :=
  liftPair_sum_left hφ ρ hZ s a _ fun i hi =>
    liftPair_sum_right hφ ρ hZ t _ b fun j hj => h i hi j hj

end CFSG.RankThree.Classical
