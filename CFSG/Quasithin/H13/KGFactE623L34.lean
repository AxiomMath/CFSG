module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel

public section

namespace CFSG.Quasithin.H13.KGE623

open CFSG.ComponentClassification CFSG.Assembly.LowTwoRank

theorem eq_one_of_psl34 {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 3 2 2) {a b : S} (ha : a ^ 3 = 1) (hb : b ^ 2 = 1)
    (hb1 : b ≠ 1) (hab : a * b = b * a) : a = 1 := by
  obtain ⟨e⟩ := PSL3Four.exact_model.2.2.2.1 S h
  set y : Equiv.Perm (Fin 42) := ((e b : PSL3Four.S) : Equiv.Perm (Fin 42)) with hy
  set t : Equiv.Perm (Fin 42) := ((e a : PSL3Four.S) : Equiv.Perm (Fin 42)) with ht
  have hyS : y ∈ PSL3Four.S := (e b).2
  have htS : t ∈ PSL3Four.S := (e a).2
  have hy2 : y ^ 2 = 1 := by
    have h1 : e b ^ 2 = 1 := by rw [← map_pow, hb, map_one]
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hy1 : y ≠ 1 := by
    intro h1
    apply hb1
    apply e.injective
    rw [map_one]
    exact Subtype.ext h1
  have ht3 : t ^ 3 = 1 := by
    have h1 : e a ^ 3 = 1 := by rw [← map_pow, ha, map_one]
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hty : t * y = y * t := by
    have h1 : e a * e b = e b * e a := by rw [← map_mul, ← map_mul, hab]
    exact congrArg Subtype.val h1
  let yR : PSL3Four.R := ⟨y, PSL3Four.S_le_R hyS⟩
  have hyR : orderOf yR = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => hy1 (congrArg Subtype.val h1)
    simpa using hy2
  have hconj : IsConj yR PSL3Four.r₁R := by
    rcases (PSL3Four.orderOf_eq_two_iff yR).1 hyR with h1 | h1 | h1 | h1
    · exact h1
    · exact absurd hyS (PSL3Four.not_mem_S_of_isConj h1 PSL3Four.not_mem_S_r₂)
    · exact absurd hyS (PSL3Four.not_mem_S_of_isConj h1 PSL3Four.not_mem_S_r₃)
    · exact absurd hyS (PSL3Four.not_mem_S_of_isConj h1 PSL3Four.not_mem_S_r₄)
  obtain ⟨c, hc, hyc⟩ := PSL3Four.eq_conj_of_isConj hconj
  have hr : PSL3Four.r₁ = c⁻¹ * y * c := by
    have hyc' : y = c * PSL3Four.r₁ * c⁻¹ := hyc
    rw [hyc']
    group
  have ht'S : c⁻¹ * t * c ∈ PSL3Four.S := by
    have h1 := PSL3Four.conj_mem_S (inv_mem hc) htS
    rwa [inv_inv] at h1
  have ht'C : c⁻¹ * t * c ∈ PSL3Four.C₁ := by
    show c⁻¹ * t * c ∈ Subgroup.centralizer {PSL3Four.r₁} ⊓ PSL3Four.S
    refine Subgroup.mem_inf.mpr ⟨?_, ht'S⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hr]
    calc c⁻¹ * t * c * (c⁻¹ * y * c) = c⁻¹ * (t * y) * c := by group
      _ = c⁻¹ * (y * t) * c := by rw [hty]
      _ = c⁻¹ * y * c * (c⁻¹ * t * c) := by group
  set g : PSL3Four.C₁ := ⟨c⁻¹ * t * c, ht'C⟩ with hg
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    show (c⁻¹ * t * c) ^ 3 = 1
    calc (c⁻¹ * t * c) ^ 3 = c⁻¹ * t ^ 3 * c := by rw [pow_three, pow_three]; group
      _ = 1 := by rw [ht3]; group
  have hdvd := orderOf_dvd_natCard g
  rw [PSL3Four.card_C₁] at hdvd
  have hgcd : orderOf g ∣ Nat.gcd 64 3 := Nat.dvd_gcd hdvd (orderOf_dvd_of_pow_eq_one hg3)
  have h64 : Nat.gcd 64 3 = 1 := by norm_num
  rw [h64, Nat.dvd_one, orderOf_eq_one_iff] at hgcd
  have hg1 : g = 1 := hgcd
  have ht1 : t = 1 := by
    have h1 : c⁻¹ * t * c = 1 := congrArg Subtype.val hg1
    calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  apply e.injective
  rw [map_one]
  exact Subtype.ext ht1

end CFSG.Quasithin.H13.KGE623
