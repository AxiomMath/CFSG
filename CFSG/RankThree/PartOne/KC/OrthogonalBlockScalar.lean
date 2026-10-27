module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Order

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem OddOrderIsometry.orderOf_root (hx : OddOrderIsometry Q p x) (hp : p.Prime) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    ∃ hlam0 : AdjoinRoot.root h ≠ 0, orderOf (Units.mk0 (AdjoinRoot.root h) hlam0) = p := by
  have hmon := (mem_primaryFactors.mp hh).2.1
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0' => by
    rw [h0', zero_pow hp.ne_zero] at hlamp
    exact zero_ne_one hlamp
  exact ⟨hlam0, orderOf_root_unit hp hlam0 hlam1 hlamp⟩

theorem OddOrderIsometry.p_lt_card_adjoinRoot (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) : p < Nat.card (AdjoinRoot h) := by
  obtain ⟨hlam0, hord⟩ := hx.orderOf_root hp hh hne1
  have h1 : p ∣ Nat.card (AdjoinRoot h) - 1 := by
    rw [← Nat.card_units, ← hord]
    exact orderOf_dvd_natCard _
  have h2 : 1 < Nat.card (AdjoinRoot h) := Finite.one_lt_card
  have := Nat.le_of_dvd (by omega) h1
  omega

omit [Finite K] in
theorem OddOrderIsometry.dvd_card_pow_add_one (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    {d : ℕ} (hroot : AdjoinRoot.root h ^ Nat.card K ^ d = (AdjoinRoot.root h)⁻¹) :
    p ∣ Nat.card K ^ d + 1 := by
  obtain ⟨hlam0, hord⟩ := hx.orderOf_root hp hh hne1
  rw [← hord]
  refine orderOf_dvd_of_pow_eq_one (Units.ext ?_)
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, pow_succ, hroot, inv_mul_cancel₀ hlam0,
    Units.val_one]

end Order

section Scalar

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.exists_scalar_factor (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hscal : ∀ c : (AdjoinRoot h)ˣ, c ^ p = 1 → scalarGL x h c ∈ (blockGL Q x h).range)
    (hpm : ¬ p ∣ primaryMultiplicity x.toLinearMap h) {t : ↥(supportedBlock Q x h)}
    (ht : t ^ p = 1) :
    ∃ s : ↥(supportedBlock Q x h), (∀ g, s * g = g * s) ∧ s ^ p = 1 ∧
      blockDet Q x h s = blockDet Q x h t := by
  set m := primaryMultiplicity x.toLinearMap h with hm
  have hδp : blockDet Q x h t ^ p = 1 := by
    rw [← map_pow, ht, map_one]
  have hδ0 : blockDet Q x h t ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp.ne_zero] at hδp
    exact zero_ne_one hδp
  let δ : (AdjoinRoot h)ˣ := Units.mk0 _ hδ0
  have hδu : δ ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hδp)
  have hcop : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm).symm
  obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hc : (δ ^ b) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hδu, one_pow]
  have hcm : (δ ^ b) ^ m = δ := by
    rw [← pow_mul, mul_comm b m]
    have h1 : m * b = p * (m * b / p) + 1 := by
      have := Nat.div_add_mod (m * b) p
      omega
    rw [h1, pow_add, pow_mul, hδu, one_pow, one_mul, pow_one]
  obtain ⟨s, hs⟩ := hscal (δ ^ b) hc
  have hinj := hx.blockGL_injective hh
  refine ⟨s, fun g => ?_, ?_, ?_⟩
  · apply hinj
    rw [map_mul, map_mul, hs]
    exact ((Subgroup.mem_center_iff.mp (scalarGL_mem_center h (δ ^ b))) (blockGL Q x h g)).symm
  · apply hinj
    rw [map_pow, hs, ← scalarGL_pow, hc, scalarGL_one, map_one]
  · rw [blockDet_apply, hs, det_scalarGL, ← hm, ← Units.val_pow_eq_pow_val, hcm]
    rfl

theorem OddOrderIsometry.scalarGL_mem_range_paired (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h)
    (c : (AdjoinRoot h)ˣ) : scalarGL x h c ∈ (blockGL Q x h).range :=
  hx.blockGL_surjective_paired hh hne _

end Scalar

section ScalarSelfDual

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.scalarGL_mem_range_selfDual (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h) {d : ℕ}
    (hroot : AdjoinRoot.root h ^ Nat.card K ^ d = (AdjoinRoot.root h)⁻¹)
    (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h)
    (hH : ∀ u w c, Algebra.trace K (AdjoinRoot h) (H u w * c) =
      QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    (hleft : ∀ (c : AdjoinRoot h) u w, H (c • u) w = frobPow K (AdjoinRoot h) d c * H u w)
    (hright : ∀ (c : AdjoinRoot h) u w, H u (c • w) = c * H u w)
    (c : (AdjoinRoot h)ˣ) (hc : c ^ p = 1) : scalarGL x h c ∈ (blockGL Q x h).range := by
  rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH]
  intro u w
  have hdvd := hx.dvd_card_pow_add_one hp hh hne1 hroot
  have hcc : frobPow K (AdjoinRoot h) d (c : AdjoinRoot h) * c = 1 := by
    rw [frobPow_apply, ← pow_succ]
    have h1 : (c : AdjoinRoot h) ^ (Nat.card K ^ d + 1) = 1 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hc, Units.val_one, one_pow]
    exact h1
  show H ((c : AdjoinRoot h) • u) ((c : AdjoinRoot h) • w) = H u w
  rw [hleft, hright, ← mul_assoc, hcc, one_mul]

end ScalarSelfDual

end CFSG.RankThree.PartOne.KCOrthogonal
