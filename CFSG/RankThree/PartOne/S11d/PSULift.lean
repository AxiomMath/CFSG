module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical

variable {F n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

abbrev SUn (h : UnitaryFieldData 2 F K) (n : ℕ) : Type := ↥(gramSU h (idGram K n))

abbrev ZSU (h : UnitaryFieldData 2 F K) (n : ℕ) : Subgroup (SUn h n) :=
  normOneScalars h (gramSU h (idGram K n)) n

abbrev PSUn (h : UnitaryFieldData 2 F K) (n : ℕ) : Type := SUn h n ⧸ ZSU h n

theorem not_dvd_card_ZSU (hn : 1 ≤ n) (hp : p.Prime)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1) :
    ¬ p ∣ Nat.card (ZSU h n) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite K := h.finite
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨c, hcN, hcn, hzc⟩ := z.2
  have hzp : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hcp : c ^ p = 1 := by
    have := congrArg (fun w : ↥(ZSU h n) => ((w : SUn h n) : GL (Fin n) K)) hzp
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [hzc, ← map_pow] at this
    exact (scalar_eq_one_iff hn).mp this
  have hc1 := hZp c hcN hcn hcp
  have : z = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hzc, hc1]
    simp
  rw [this, orderOf_one] at hz
  exact hp.one_lt.ne hz

theorem odd_card_ZSU (hn : 1 ≤ n) : Odd (Nat.card (ZSU h n)) := by
  have hfin : Finite K := h.finite
  rw [card_normOneScalars_one h hn]
  have hodd : Odd (2 ^ F + 1) := by
    have : Even (2 ^ F) := (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩)
    exact this.add_one
  exact Odd.of_dvd_nat hodd (Nat.gcd_dvd_right _ _)

theorem exists_lift_pow (hn : 1 ≤ n)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    {x : PSUn h n} (hxp : x ^ p = 1) :
    ∃ g : SUn h n, g ^ p = 1 ∧ (g : PSUn h n) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ^ p ∈ ZSU h n :=
    (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact hxp)
  obtain ⟨c₀, hc₀N, hc₀n, hc₀⟩ := hg
  obtain ⟨c₁, hc₁N, hc₁n, hc₁p⟩ := exists_pow_eq_of_noTorsion hZp
    (c₀ := c₀⁻¹) (by rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hc₀N, inv_one])
    (by rw [inv_pow, hc₀n, inv_one])
  let z : SUn h n := ⟨GeneralLinearGroup.scalar (Fin n) c₁, scalar_mem_gramSU hn hc₁N hc₁n⟩
  have hz : z ∈ ZSU h n := ⟨c₁, hc₁N, hc₁n, rfl⟩
  have hzc : Commute g z := Subgroup.mem_center_iff.mp (normOneScalars_le_center h _ n hz) g
  have hgp' : ((g : GL (Fin n) K)) ^ p = GeneralLinearGroup.scalar (Fin n) c₀ := by
    rw [← Subgroup.coe_pow]
    exact hc₀
  have hxp' : (g * z) ^ p = 1 := by
    rw [hzc.mul_pow]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hgp']
    change GeneralLinearGroup.scalar (Fin n) c₀ * (GeneralLinearGroup.scalar (Fin n) c₁) ^ p = 1
    rw [← map_pow, hc₁p, ← map_mul, mul_inv_cancel, map_one]
  refine ⟨g * z, hxp', ?_⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]

theorem lift_sigma_fixed (hn : 1 ≤ n)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1) {σ : K ≃+* K}
    {A : SUn h n} (hAp : A ^ p = 1)
    (hσx : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ
      (A : PSUn h n) = A) : glAut σ (A : GL (Fin n) K) = A := by
  have h1 : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ (A : PSUn h n) =
      ((primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := n)) σ A : SUn h n) :
        PSUn h n) := primeFormFieldAut_mk h _ σ A
  rw [h1] at hσx
  have hAp' : (primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := n)) σ A) ^ p = 1 := by
    rw [← map_pow, hAp, map_one]
  have := eq_of_mk_eq_of_pow_eq_one_of_noTorsion hZp hn hAp' hAp hσx
  exact congrArg (fun g : SUn h n => (g : GL (Fin n) K)) this

theorem commute_of_mk_commute (hn : 1 ≤ n)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    {A g : SUn h n} (hAp : A ^ p = 1) (hcomm : (g : PSUn h n) * A = A * g) : g * A = A * g := by
  have h1 : g * A * g⁻¹ = A := by
    refine eq_of_mk_eq_of_pow_eq_one_of_noTorsion hZp hn ?_ hAp ?_
    · rw [conj_pow, hAp]
      simp
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcomm]
      exact mul_inv_cancel_right _ _
  calc g * A = g * A * g⁻¹ * g := by simp
    _ = A * g := by rw [h1]

theorem exists_lift_two_pow (hn : 1 ≤ n) {y : PSUn h n} {k : ℕ} (hy : y ^ (2 ^ k) = 1) :
    ∃ g : SUn h n, g ^ (2 ^ k) = 1 ∧ (g : PSUn h n) = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hN := odd_card_ZSU h hn
  set N := Nat.card (ZSU h n) with hNdef
  have hcop : Nat.Coprime (2 ^ k) N :=
    Nat.Coprime.pow_left k ((Nat.coprime_two_left).mpr hN)
  obtain ⟨m, hm1, hm2⟩ := Nat.chineseRemainder hcop 1 0
  have hg2 : g ^ (2 ^ k) ∈ ZSU h n := (QuotientGroup.eq_one_iff _).mp (by
    rw [QuotientGroup.mk_pow]; exact hy)
  refine ⟨g ^ m, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    have hNm : N ∣ m := (Nat.modEq_zero_iff_dvd.mp hm2)
    obtain ⟨t, ht⟩ := hNm
    have hz : (⟨g ^ (2 ^ k), hg2⟩ : ↥(ZSU h n)) ^ N = 1 := pow_card_eq_one'
    have hz' : (g ^ (2 ^ k)) ^ N = 1 := congrArg Subtype.val hz
    rw [ht, pow_mul, hz', one_pow]
  · rw [QuotientGroup.mk_pow]
    have h1 : (g : PSUn h n) ^ m = (g : PSUn h n) ^ (m % 2 ^ k) := pow_eq_pow_mod m hy
    have h2 : (g : PSUn h n) ^ (1 % 2 ^ k) = (g : PSUn h n) := by
      rw [← pow_eq_pow_mod 1 hy, pow_one]
    rw [h1, ← h2]
    congr 1

end CFSG.RankThree.PartOne
