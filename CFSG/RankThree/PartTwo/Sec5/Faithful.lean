module

import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_orderOf_coprime {M : Type*} [Group M] {φ : M} {k : ℕ}
    (hφ : ∃ n, φ ^ (3 ^ n) = 1) (hdvd : orderOf φ ∣ k) (hk : ¬ 3 ∣ k) : φ = 1 := by
  obtain ⟨n, hn⟩ := hφ
  have h1 : orderOf φ ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (3 ^ n) k :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hk)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 hdvd)

theorem exists_faithful_exponent_three {Q B : Subgroup G} (hQ : IsPGroup 3 Q) (hBQ : B ≤ Q)
    (hQB : Q ≤ Subgroup.centralizer (B : Set G)) (hB3 : ∀ b ∈ B, b ^ 3 = 1) :
    ∃ D : Subgroup G, B ≤ D ∧ D ≤ Q ∧ (∀ x ∈ D, x ^ 3 = 1) ∧
      (∀ g ∈ Subgroup.normalizer (Q : Set G), g ∈ Subgroup.centralizer (B : Set G) →
        g ∈ Subgroup.normalizer (D : Set G)) ∧
      ∀ K : Subgroup G, ¬ 3 ∣ Nat.card K → K ≤ Subgroup.normalizer (Q : Set G) →
        K ≤ Subgroup.centralizer (D : Set G) → K ≤ Subgroup.centralizer (Q : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases eq_or_ne Q ⊥ with hQbot | hQbot
  · refine ⟨⊥, by rw [← hQbot]; exact hBQ, by rw [hQbot], fun x hx => by
      rw [Subgroup.mem_bot.mp hx, one_pow], fun g _ _ => ?_, fun K _ _ _ => ?_⟩
    · rw [Subgroup.normalizer_eq_top ⊥]
      exact Subgroup.mem_top g
    · rw [hQbot]
      intro k _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      rw [hh, one_mul, mul_one]
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQbot
  obtain ⟨D₀, hchar, -, -, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := 3) (by norm_num) hQ
  set D₁ := D₀.map Q.subtype with hD₁
  have hD₁Q : D₁ ≤ Q := Subgroup.map_subtype_le D₀
  have hD₁B : D₁ ≤ Subgroup.normalizer (B : Set G) :=
    (hD₁Q.trans hQB).trans (Subgroup.centralizer_le_normalizer (B : Set G))
  refine ⟨D₁ ⊔ B, le_sup_right, sup_le hD₁Q hBQ, ?_, ?_, ?_⟩
  ·
    intro x hx
    have hx' : x ∈ (D₁ : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D₁ B hD₁B]
      exact hx
    obtain ⟨d, hd, b, hb, rfl⟩ := hx'
    have hcomm : Commute d b :=
      (Subgroup.mem_centralizer_iff.mp ((hD₁Q.trans hQB) hd) b hb).symm
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.mp hd
    rw [hcomm.mul_pow, hB3 b hb, mul_one]
    change ((d₀ ^ 3 : Q) : G) = 1
    rw [hexp d₀ hd₀, Subgroup.coe_one]
  ·
    intro g hgQ hgB
    have hgD₁ : g ∈ Subgroup.normalizer (D₁ : Set G) := by
      set φ := Q.normalizerMonoidHom ⟨g, hgQ⟩
      have hφ : D₀.map φ.toMonoidHom = D₀ := Subgroup.characteristic_iff_map_eq.mp hchar φ
      have hφs : D₀.map φ.symm.toMonoidHom = D₀ := Subgroup.characteristic_iff_map_eq.mp hchar _
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨d, hd, rfl⟩
        have hmem : φ d ∈ D₀ := hφ ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hd
        exact ⟨φ d, hmem, rfl⟩
      · intro hh
        obtain ⟨e, he, hee⟩ := Subgroup.mem_map.mp hh
        have hhQ : h ∈ Q := by
          have h1 : g * h * g⁻¹ ∈ Q := hee ▸ e.2
          have h2 := (Subgroup.mem_normalizer_iff.mp hgQ h).mpr h1
          exact h2
        have hmem : φ.symm e ∈ D₀ := hφs ▸ Subgroup.mem_map_of_mem φ.symm.toMonoidHom he
        refine ⟨φ.symm e, hmem, ?_⟩
        have hφe : φ ⟨h, hhQ⟩ = e := Subtype.ext hee.symm
        rw [← hφe, MulEquiv.symm_apply_apply]
        rfl
    exact Subgroup.inf_normalizer_le_normalizer_sup D₁ B
      (Subgroup.mem_inf.mpr ⟨hgD₁, Subgroup.centralizer_le_normalizer (B : Set G) hgB⟩)
  ·
    intro K hK hKQ hKD k hk
    set φ := Q.normalizerMonoidHom ⟨k, hKQ hk⟩
    have hφfix : φ ∈ fixingSubgroup (MulAut Q) (D₀ : Set Q) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      change k * (d : G) * k⁻¹ = d
      have hdD : (d : G) ∈ D₁ ⊔ B :=
        (le_sup_left : D₁ ≤ D₁ ⊔ B) (Subgroup.mem_map_of_mem Q.subtype hd)
      rw [← Subgroup.mem_centralizer_iff.mp (hKD hk) _ hdD, mul_inv_cancel_right]
    have hφ1 : (⟨φ, hφfix⟩ : fixingSubgroup (MulAut Q) (D₀ : Set Q)) = 1 := by
      refine eq_one_of_orderOf_coprime (k := Nat.card K) (hfix _) ?_ hK
      have h1 := orderOf_map_dvd (fixingSubgroup (MulAut Q) (D₀ : Set Q)).subtype
        ⟨φ, hφfix⟩
      have h2 : orderOf φ ∣ orderOf (⟨k, hKQ hk⟩ : Subgroup.normalizer (Q : Set G)) :=
        orderOf_map_dvd _ _
      have h3 : orderOf (⟨k, hKQ hk⟩ : Subgroup.normalizer (Q : Set G)) = orderOf k :=
        Subgroup.orderOf_mk k _
      have h4 : orderOf (⟨φ, hφfix⟩ : fixingSubgroup (MulAut Q) (D₀ : Set Q)) = orderOf φ :=
        Subgroup.orderOf_mk φ _
      rw [h4]
      exact h2.trans (h3 ▸ Subgroup.orderOf_dvd_natCard K hk)
    have hφ1' : φ = 1 := congrArg Subtype.val hφ1
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := DFunLike.congr_fun hφ1' ⟨q, hq⟩
    have h5 : k * q * k⁻¹ = q := congrArg Subtype.val this
    calc q * k = k * q * k⁻¹ * k := by rw [h5]
      _ = k * q := by group

end CFSG.RankThree.PartTwo.Sec5
