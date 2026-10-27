module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryField
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldMat

public section

namespace CFSG.StandardType

namespace LIDUF

open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Foote.ModuleExclusions

variable {K : Type} [Field K] [Finite K] {n : ℕ}

@[expose] noncomputable def barEquiv (h : UnitaryFieldData 2 n K) : K ≃+* K where
  toFun := h.bar
  invFun := h.bar
  left_inv := h.bar_bar
  right_inv := h.bar_bar
  map_mul' := map_mul h.bar
  map_add' := map_add h.bar

theorem orderOf_barEquiv (h : UnitaryFieldData 2 n K) : orderOf (barEquiv h) = 2 := by
  have h2 : barEquiv h ^ 2 = 1 := by
    ext x
    simp [pow_two, RingAut.mul_apply, barEquiv, h.bar_bar]
  have h1 : barEquiv h ≠ 1 := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    intro he
    exact hc (by simpa [barEquiv] using DFunLike.congr_fun he c)
  exact orderOf_eq_prime h2 h1

theorem exists_unitary_normalizer (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) {p : ℕ}
    {φ : K ≃+* K} (hφ : orderOf φ = p) {τ : K} (hτ : τ ^ (2 ^ n + 1) = 1) (hφτ : φ τ = τ) :
    ∃ ρ : K, ρ ^ (2 ^ n + 1) = 1 ∧ ∏ i ∈ Finset.range p, (φ ^ i) ρ = τ := by
  have := Fintype.ofFinite K
  have hq : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  set m : ℕ := 2 ^ (n - 1) with hm
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hτ
    exact zero_ne_one hτ
  set δ := τ ^ (m + 1) with hδ
  have hδ2 : δ ^ 2 = τ := by
    rw [hδ, ← pow_mul, show (m + 1) * 2 = (2 ^ n + 1) + 1 by omega, pow_succ, hτ, one_mul]
  have hδ0 : δ ≠ 0 := pow_ne_zero _ hτ0
  have hδq : δ ^ (2 ^ n + 1) = 1 := by
    rw [hδ, ← pow_mul, mul_comm, pow_mul, hτ, one_pow]
  set γ := δ⁻¹ with hγ
  have hγ0 : γ ≠ 0 := inv_ne_zero hδ0
  have hγq : γ ^ (2 ^ n + 1) = 1 := by rw [hγ, inv_pow, hδq, inv_one]
  have hφδ : φ δ = δ := by rw [hδ, map_pow, hφτ]
  have hφγ : φ γ = γ := by rw [hγ, map_inv₀, hφδ]
  obtain ⟨ρ₀, hρ₀0, hρ₀⟩ := exists_prod_pow_eq φ γ hφγ hγ0
  rw [hφ] at hρ₀
  refine ⟨ρ₀ ^ (2 ^ n - 1), ?_, ?_⟩
  · have hcard : Fintype.card K = (2 ^ n) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
    have h1 := FiniteField.pow_card_sub_one_eq_one ρ₀ hρ₀0
    rw [hcard] at h1
    have hq2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hq1
    rw [← pow_mul, show (2 ^ n - 1) * (2 ^ n + 1) = (2 ^ n) ^ 2 - 1 by zify [hq1, hq2]; ring]
    exact h1
  · simp only [map_pow]
    rw [Finset.prod_pow, hρ₀]
    have h1 : γ ^ (2 ^ n - 1) * γ ^ 2 = 1 := by
      rw [← pow_add, show 2 ^ n - 1 + 2 = 2 ^ n + 1 by omega, hγq]
    rw [← hδ2]
    have h3 : γ ^ (2 ^ n - 1) = (γ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h3, hγ, inv_pow, inv_inv]

theorem exists_fixed_normOne (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) {φ : K ≃+* K} (hφ : orderOf φ = p)
    (hφb : ∀ x, φ (h.bar x) = h.bar (φ x)) {z : K} (hz0 : z ≠ 0) (hzb : h.bar z = z)
    (hzφ : φ z = z) : ∃ s : K, s ≠ 0 ∧ φ s = s ∧ s * h.bar s = z := by
  have := Fintype.ofFinite K
  have hφp : φ ^ p = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hφ1 : φ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hφ
    exact hp.one_lt.ne hφ
  obtain ⟨l, hl0, hl⟩ := exists_prod_pow_eq (barEquiv h) z hzb hz0
  rw [orderOf_barEquiv h] at hl
  have hl' : l * h.bar l = z := by
    simpa [Finset.prod_range_succ, barEquiv] using hl
  have hφl0 : φ l ≠ 0 := fun h0 => hl0 ((map_eq_zero_iff φ φ.injective).1 h0)
  set u : K := φ l / l with hu
  have hu0 : u ≠ 0 := div_ne_zero hφl0 hl0
  have hbaru : h.bar u = h.bar (φ l) / h.bar l := map_div₀ h.bar _ _
  have hbl0 : h.bar l ≠ 0 := fun h0 => hl0 ((map_eq_zero_iff h.bar h.bar.injective).1 h0)
  have hnu : u * h.bar u = 1 := by
    rw [hbaru, hu, ← hφb]
    have h1 : φ (l * h.bar l) = φ z := by rw [hl']
    rw [map_mul, hzφ] at h1
    field_simp
    exact h1.trans hl'.symm
  have huq : u ^ (2 ^ n + 1) = 1 := by
    rw [pow_succ, ← h.bar_apply u, mul_comm, hnu]
  have hγq : (u⁻¹) ^ (2 ^ n + 1) = 1 := by rw [inv_pow, huq, inv_one]
  have hN : TableBUF.partNorm φ u⁻¹ p = 1 := by
    have hpow : ∀ i : ℕ, (φ ^ i) u⁻¹ = (φ ^ i) l / (φ ^ (i + 1)) l := by
      intro i
      rw [hu, map_inv₀, map_div₀, inv_div, pow_succ, RingAut.mul_apply]
    have hP : ∏ i ∈ Finset.range p, (φ ^ i) u⁻¹ =
        (∏ i ∈ Finset.range p, (φ ^ i) l) / ∏ i ∈ Finset.range p, (φ ^ (i + 1)) l := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun i _ => hpow i
    have h1 := Finset.prod_range_succ (fun i => (φ ^ i) l) p
    have h2 := Finset.prod_range_succ' (fun i => (φ ^ i) l) p
    rw [h1] at h2
    simp only [hφp, pow_zero, RingAut.one_apply] at h2
    have hne : ∏ i ∈ Finset.range p, (φ ^ (i + 1)) l ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => fun h0 => hl0 (by
        have := (map_eq_zero_iff (φ ^ (i + 1)) (φ ^ (i + 1)).injective).1 h0
        exact this)
    have hne' : ∏ i ∈ Finset.range p, (φ ^ i) l ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => fun h0 => hl0 (by
        have := (map_eq_zero_iff (φ ^ i) (φ ^ i).injective).1 h0
        exact this)
    unfold TableBUF.partNorm
    rw [hP, div_eq_one_iff_eq hne]
    exact mul_right_cancel₀ hl0 h2
  obtain ⟨t, htq, hφt⟩ := TableBUF.exists_hilbert90_unitary (q := 2 ^ n) hK
    ((Nat.even_pow' (by omega)).mpr even_two) Nat.one_le_two_pow hp hφp hφ1 hγq hN
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at htq
    exact zero_ne_one htq
  refine ⟨l * t, mul_ne_zero hl0 ht0, ?_, ?_⟩
  · rw [map_mul, hφt]
    have : φ l = u * l := by rw [hu]; field_simp
    rw [this]
    field_simp
  · rw [map_mul]
    have : t * h.bar t = 1 := by
      rw [← htq, pow_succ, ← h.bar_apply t, mul_comm]
    calc l * t * (h.bar l * h.bar t) = (l * h.bar l) * (t * h.bar t) := by ring
      _ = z := by rw [hl', this, mul_one]

end LIDUF

end CFSG.StandardType

end
