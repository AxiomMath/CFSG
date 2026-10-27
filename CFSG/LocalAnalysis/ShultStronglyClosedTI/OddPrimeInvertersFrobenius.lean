module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OddPrimeInverters

open Polynomial

section Algebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

theorem aeval_units_conj (u : Aˣ) (y : A) (f : K[X]) :
    aeval ((u : A) * y * ↑u⁻¹) f = u * aeval y f * ↑u⁻¹ := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg, mul_add, add_mul]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow, ← mul_assoc, ← mul_assoc,
      Algebra.commutes a (u : A)]
    simp only [mul_assoc]

theorem aeval_geom_mul (p k : ℕ) (z : A) :
    aeval z (∑ i ∈ Finset.range p, (X ^ p ^ k : K[X]) ^ i) * (z ^ p ^ k - 1) =
      z ^ p ^ (k + 1) - 1 := by
  rw [map_sum]
  simp only [map_pow, aeval_X]
  rw [geom_sum_mul, ← pow_mul, ← pow_succ]

variable [Fintype K]

theorem exists_lt_pow_eq_pow_card_pow {y : A} (hy : IsIntegral K y) {d : ℕ}
    (hdeg : (minpoly K y).natDegree ≤ d) {p k : ℕ} [Fact p.Prime] (hpK : (p : K) ≠ 0)
    (hk : ¬ y ^ p ^ k = 1) (hk' : y ^ p ^ (k + 1) = 1)
    (hord : d ≤ orderOf ((Fintype.card K : ℕ) : ZMod (p ^ (k + 1))))
    {j : ℕ} (hj : aeval (y ^ j) (minpoly K y) = 0) :
    ∃ i < d, y ^ j = y ^ Fintype.card K ^ i := by
  classical
  set μ := minpoly K y with hμ
  set q := Fintype.card K with hq
  let L := AlgebraicClosure K
  set h : K[X] := ∑ i ∈ Finset.range p, (X ^ p ^ k : K[X]) ^ i with hh
  have hnc : ¬ IsCoprime μ h := by
    rintro ⟨a, b, hab⟩
    have h1 : aeval y b * aeval y h = 1 := by
      simpa [hμ, minpoly.aeval] using congrArg (aeval y) hab
    apply hk
    have h2 : y ^ p ^ k - 1 = 0 := by
      calc y ^ p ^ k - 1 = aeval y b * aeval y h * (y ^ p ^ k - 1) := by rw [h1, one_mul]
        _ = aeval y b * (y ^ p ^ (k + 1) - 1) := by rw [mul_assoc, hh, aeval_geom_mul]
        _ = 0 := by rw [hk', sub_self, mul_zero]
    exact sub_eq_zero.mp h2
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed K L] at hnc
  push Not at hnc
  obtain ⟨ζ, hζμ, hζh⟩ := hnc
  have hζn : ζ ^ p ^ (k + 1) = 1 := by
    have h1 := aeval_geom_mul (K := K) p k ζ
    rw [← hh, hζh, zero_mul] at h1
    exact (sub_eq_zero.mp h1.symm)
  have hζk : ¬ ζ ^ p ^ k = 1 := by
    intro h1
    rw [hh, map_sum] at hζh
    simp only [map_pow, aeval_X, h1, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] at hζh
    apply hpK
    exact (algebraMap K L).injective (by rw [map_natCast, map_zero]; exact hζh)
  have hζord : orderOf ζ = p ^ (k + 1) := orderOf_eq_prime_pow hζk hζn
  have hyord : orderOf y = p ^ (k + 1) := orderOf_eq_prime_pow hk hk'
  have hpos : 0 < p ^ (k + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hζfin : IsOfFinOrder ζ := orderOf_pos_iff.mp (hζord ▸ hpos)
  have hyfin : IsOfFinOrder y := orderOf_pos_iff.mp (hyord ▸ hpos)
  have hfrob : ∀ i : ℕ, aeval (ζ ^ q ^ i) μ = 0 := by
    intro i
    induction i with
    | zero => simpa using hζμ
    | succ i ih =>
      rw [pow_succ, pow_mul, ← expand_aeval, hq, FiniteField.Polynomial.expand_card, map_pow,
        ih, zero_pow Fintype.card_ne_zero]
  have hζj : aeval (ζ ^ j) μ = 0 := by
    obtain ⟨c, hc⟩ := minpoly.dvd K y (p := μ.comp (X ^ j))
      (by rw [aeval_comp, map_pow, aeval_X, hj])
    have h1 := congrArg (aeval ζ) hc
    rwa [aeval_comp, map_pow, aeval_X, map_mul, ← hμ, hζμ, zero_mul] at h1
  have hinj : Set.InjOn (fun i => ζ ^ q ^ i) (Finset.range d : Set ℕ) := by
    intro i hi i' hi' hii'
    have h1 : q ^ i ≡ q ^ i' [MOD p ^ (k + 1)] := by
      rw [← hζord]
      exact hζfin.pow_eq_pow_iff_modEq.mp hii'
    have h2 : (q : ZMod (p ^ (k + 1))) ^ i = (q : ZMod (p ^ (k + 1))) ^ i' := by
      rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
      exact h1
    exact pow_injOn_Iio_orderOf (lt_of_lt_of_le (Finset.mem_range.mp hi) hord)
      (lt_of_lt_of_le (Finset.mem_range.mp hi') hord) h2
  set f : L[X] := μ.map (algebraMap K L) with hf
  have hf0 : f ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hy)
  have hmem : ∀ z : L, aeval z μ = 0 → z ∈ f.roots := fun z hz => by
    rw [mem_roots hf0, IsRoot.def, hf, eval_map_algebraMap]
    exact hz
  set Z : Finset L := (Finset.range d).image (fun i => ζ ^ q ^ i) with hZ
  have hZcard : Z.card = d := by rw [hZ, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hζjZ : ζ ^ j ∈ Z := by
    by_contra hnot
    have hsub : (insert (ζ ^ j) Z).val ⊆ f.roots := by
      intro z hz
      rw [Finset.mem_val, Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact hmem _ hζj
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
        exact hmem _ (hfrob i)
    have hle := card_le_degree_of_subset_roots hsub
    rw [Finset.card_insert_of_notMem hnot, hZcard, hf, natDegree_map] at hle
    omega
  obtain ⟨i, hi, hiζ⟩ := Finset.mem_image.mp hζjZ
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  rw [hyfin.pow_eq_pow_iff_modEq, hyord, ← hζord]
  exact (hζfin.pow_eq_pow_iff_modEq.mp hiζ).symm

end Algebra

section Linear

variable {K : Type*} [Field K] [Fintype K]

theorem exists_lt_conj_eq_pow_card_pow {d : ℕ} {G : Type*} [Group G] (ρ : G →* GL (Fin d) K)
    (hρ : Function.Injective ρ) {p k : ℕ} [Fact p.Prime] (hpK : (p : K) ≠ 0) {y g : G}
    (hy : orderOf y = p ^ (k + 1))
    (hord : d ≤ orderOf ((Fintype.card K : ℕ) : ZMod (p ^ (k + 1))))
    {j : ℕ} (hj : g * y * g⁻¹ = y ^ j) :
    ∃ i < d, g * y * g⁻¹ = y ^ Fintype.card K ^ i := by
  set Y : Matrix (Fin d) (Fin d) K := (ρ y : Matrix (Fin d) (Fin d) K) with hYdef
  have hval : ∀ n : ℕ, ((ρ (y ^ n) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Y ^ n :=
    fun n => by rw [map_pow, Units.val_pow_eq_pow_val]
  have hdeg : (minpoly K Y).natDegree ≤ d := by
    have h1 := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly Y)
      (Matrix.charpoly_monic Y).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h1
  have hconj : ((ρ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * Y *
      (((ρ g)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Y ^ j := by
    rw [← hval, ← hj, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  have hj' : aeval (Y ^ j) (minpoly K Y) = 0 := by
    rw [← hconj, aeval_units_conj, minpoly.aeval, mul_zero, zero_mul]
  have hk : ¬ Y ^ p ^ k = 1 := by
    intro h1
    have h2 : y ^ p ^ k = 1 := hρ (Units.ext (by rw [hval, h1, map_one, Units.val_one]))
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hy] at h3
    exact absurd (Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos k) h3)
      (not_le.mpr (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.lt_succ_self k)))
  have hk' : Y ^ p ^ (k + 1) = 1 := by
    rw [← hval, ← hy, pow_orderOf_eq_one, map_one, Units.val_one]
  obtain ⟨i, hi, hYi⟩ := exists_lt_pow_eq_pow_card_pow (Algebra.IsIntegral.isIntegral Y) hdeg
    hpK hk hk' hord hj'
  refine ⟨i, hi, ?_⟩
  rw [hj]
  exact hρ (Units.ext (by rw [hval, hval, hYi]))

theorem orderOf_natCast_zmod_of_dvd {q n e : ℕ} (hn : 3 ≤ n) (hdvd : n ∣ q ^ 2 ^ e + 1) :
    orderOf (q : ZMod n) = 2 ^ (e + 1) := by
  have h1 : (q : ZMod n) ^ 2 ^ e = -1 := by
    have h0 : ((q ^ 2 ^ e + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hne : (-1 : ZMod n) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod n) = 0 := by
      rw [Nat.cast_ofNat, ← one_add_one_eq_two]
      nth_rewrite 1 [← h]
      exact neg_add_cancel 1
    exact absurd (Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff _ _).mp h2)) (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime_pow (by rw [h1]; exact hne) ?_
  rw [pow_succ, pow_mul, h1, neg_one_sq]

theorem exists_lt_conj_eq_pow_card_pow_of_dvd [CharP K 2] {d e : ℕ} (hd : d = 2 ^ (e + 1))
    {G : Type*} [Group G] [Finite G] (ρ : G →* GL (Fin d) K) (hρ : Function.Injective ρ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y g : G} (hy : IsPGroup p (Subgroup.zpowers y))
    (hdvd : orderOf y ∣ Fintype.card K ^ 2 ^ e + 1) (hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y) :
    ∃ i < d, g * y * g⁻¹ = y ^ Fintype.card K ^ i := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hy
  rw [Nat.card_zpowers] at hn
  rcases n with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hn
    subst hn
    exact ⟨0, by rw [hd]; positivity, by rw [mul_one, mul_inv_cancel, one_pow]⟩
  · have hfin : IsOfFinOrder y := orderOf_pos_iff.mp (hn ▸ pow_pos hp.pos _)
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr hgy)
    have hpK : (p : K) ≠ 0 := fun h => hp2
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp ((CharP.cast_eq_zero_iff K 2 p).mp h)).symm
    have h3 : 3 ≤ p ^ (k + 1) :=
      le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (Nat.succ_ne_zero k) p)
    have hord := orderOf_natCast_zmod_of_dvd h3 (hn ▸ hdvd)
    exact exists_lt_conj_eq_pow_card_pow ρ hρ hpK hn (by rw [hord, hd]) hj.symm

end Linear

end CFSG.ShultStronglyClosedTI.OddPrimeInverters
