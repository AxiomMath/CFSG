module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.StandardType

namespace TableBUF

variable {K : Type} [Field K]

theorem ringEquiv_apply_eq_of_pow_eq_one {p : ℕ} (hp : p.Prime) {φ : K ≃+* K} (hφ : φ ^ p = 1)
    {ζ : K} (hζ : ζ ^ p = 1) : φ ζ = ζ := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases h1 : ζ = 1
  · rw [h1, map_one]
  have hord : orderOf ζ = p := orderOf_eq_prime hζ h1
  have hprim : IsPrimitiveRoot ζ p := hord ▸ IsPrimitiveRoot.orderOf ζ
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one (ξ := φ ζ) (by rw [← map_pow, hζ, map_one])
  have hk : ∀ k : ℕ, (φ ^ k) ζ = ζ ^ i ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, pow_one]; rfl
    | succ k ih =>
      rw [pow_succ', RingAut.mul_apply, ih, map_pow, ← hi, ← pow_mul, pow_succ', mul_comm]
  have h2 : ζ ^ i ^ p = ζ ^ i := by
    have h3 : ((i ^ p : ℕ) : ZMod p) = ((i : ℕ) : ZMod p) := by
      push_cast
      exact ZMod.pow_card _
    have h4 : i ^ p % p = i % p := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h3
    rw [← pow_mod_orderOf ζ (i ^ p), ← pow_mod_orderOf ζ i, hord, h4]
  have h4 := hk p
  rw [hφ, h2] at h4
  rw [← hi]
  exact h4.symm

@[expose] def partNorm (φ : K ≃+* K) (δ : K) (k : ℕ) : K :=
  ∏ i ∈ Finset.range k, (φ ^ i) δ

theorem partNorm_succ' (φ : K ≃+* K) (δ : K) (k : ℕ) :
    partNorm φ δ (k + 1) = δ * φ (partNorm φ δ k) := by
  rw [partNorm, Finset.prod_range_succ', pow_zero, RingAut.one_apply, mul_comm, partNorm,
    map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pow_succ', RingAut.mul_apply]

theorem exists_hilbert90 {p : ℕ} (hp : p.Prime) {φ : K ≃+* K} (hφ : φ ^ p = 1) (hφ1 : φ ≠ 1)
    {δ : K} (hδ : δ ≠ 0) (hN : partNorm φ δ p = 1) :
    ∃ b : K, b ≠ 0 ∧ φ b = δ⁻¹ * b := by
  classical
  have := Fact.mk hp
  have hord : orderOf φ = p := orderOf_eq_prime hφ hφ1
  set χ : Fin p → (K →* K) := fun k => ((φ ^ (k : ℕ) : K ≃+* K) : K →* K) with hχ
  have hχinj : Function.Injective χ := by
    intro k l hkl
    have h1 : φ ^ (k : ℕ) = φ ^ (l : ℕ) := by
      ext x
      exact DFunLike.congr_fun hkl x
    exact Fin.ext (pow_injOn_Iio_orderOf (x := φ) (by rw [hord]; exact k.2)
      (by rw [hord]; exact l.2) h1)
  have hli := (linearIndependent_monoidHom K K).comp χ hχinj
  set S : K → K := fun x => ∑ k ∈ Finset.range p, partNorm φ δ k * (φ ^ k) x with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 := Fintype.linearIndependent_iff.mp hli (fun k => partNorm φ δ k) (by
      funext x
      rw [Finset.sum_apply]
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hcon x, hS]
      exact (Finset.sum_range (fun k => partNorm φ δ k * (φ ^ k) x)).symm)
      ⟨0, hp.pos⟩
    simp [partNorm] at h1
  obtain ⟨x, hx⟩ := hS0
  refine ⟨S x, hx, ?_⟩
  have key : δ * φ (S x) = S x := by
    set g : ℕ → K := fun j => partNorm φ δ j * (φ ^ j) x with hg
    have e1 : δ * φ (S x) = ∑ k ∈ Finset.range p, g (k + 1) := by
      rw [hS, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hg]
      rw [map_mul, ← mul_assoc, ← partNorm_succ', pow_succ', RingAut.mul_apply]
    have e2 := Finset.sum_range_succ' g p
    have e3 := Finset.sum_range_succ g p
    have hgp : g p = x := by
      rw [hg]
      simp only
      rw [hN, hφ, one_mul, RingAut.one_apply]
    have hg0 : g 0 = x := by simp [hg, partNorm]
    have e4 : ∑ k ∈ Finset.range p, g (k + 1) + g 0 = ∑ k ∈ Finset.range p, g k + g p := by
      rw [← e2, e3]
    rw [hgp, hg0] at e4
    rw [e1]
    exact add_right_cancel e4
  calc φ (S x) = δ⁻¹ * (δ * φ (S x)) := by rw [← mul_assoc, inv_mul_cancel₀ hδ, one_mul]
    _ = δ⁻¹ * S x := by rw [key]

theorem partNorm_pow (φ : K ≃+* K) (γ : K) (j k : ℕ) :
    partNorm φ (γ ^ j) k = partNorm φ γ k ^ j := by
  rw [partNorm, partNorm, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => map_pow _ _ _

theorem exists_hilbert90_unitary [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : Even q)
    (hq1 : 1 ≤ q) {p : ℕ} (hp : p.Prime) {φ : K ≃+* K} (hφ : φ ^ p = 1) (hφ1 : φ ≠ 1) {γ : K}
    (hγ : γ ^ (q + 1) = 1) (hN : partNorm φ γ p = 1) :
    ∃ c : K, c ^ (q + 1) = 1 ∧ φ c = γ * c := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨m, hm⟩ := hq
  set δ := γ ^ (m + 1) with hδ
  have hδ2 : δ ^ 2 = γ := by
    rw [hδ, ← pow_mul, show (m + 1) * 2 = (q + 1) + 1 by omega, pow_succ, hγ, one_mul]
  have hδq : δ ^ (q + 1) = 1 := by
    rw [hδ, ← pow_mul, mul_comm, pow_mul, hγ, one_pow]
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hδq
    exact zero_ne_one hδq
  have hNδ : partNorm φ δ p = 1 := by
    rw [hδ, partNorm_pow, hN, one_pow]
  obtain ⟨b, hb0, hb⟩ := exists_hilbert90 hp hφ hφ1 hδ0 hNδ
  refine ⟨b ^ (q - 1), ?_, ?_⟩
  · have hcard : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
    have h1 := FiniteField.pow_card_sub_one_eq_one b hb0
    rw [hcard] at h1
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    rw [← pow_mul, show (q - 1) * (q + 1) = q ^ 2 - 1 by zify [hq1, hq2]; ring]
    exact h1
  · rw [map_pow, hb, mul_pow]
    congr 1
    have h1 : δ ^ (q - 1) * δ ^ 2 = 1 := by
      rw [← pow_add, show q - 1 + 2 = q + 1 by omega, hδq]
    rw [inv_pow, ← hδ2]
    exact inv_eq_of_mul_eq_one_right h1

end TableBUF

end CFSG.StandardType
