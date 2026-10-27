module

public import CFSG.Quasithin.Background.P3GL24A5Dec
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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open Equiv

theorem gl24_card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem gl24_eq_alt_of_card_sixty (H : Subgroup (Perm (Fin 5))) (h : Nat.card H = 60) :
    H = alternatingGroup (Fin 5) := by
  have hcardS : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hidx : H.index = 2 := by
    have := H.card_mul_index
    rw [h, hcardS] at this
    omega
  have : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hN : (H.subgroupOf (alternatingGroup (Fin 5))).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf (alternatingGroup (Fin 5)))
    with hbot | htop
  · exfalso
    have hinj : Function.Injective (Perm.sign.comp H.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxA : (x : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
        rw [Perm.mem_alternatingGroup]
        simpa using hx
      have : (⟨x, hxA⟩ : alternatingGroup (Fin 5)) ∈ H.subgroupOf (alternatingGroup (Fin 5)) :=
        x.2
      rw [hbot, Subgroup.mem_bot] at this
      have h1 : (x : Perm (Fin 5)) = 1 := by simpa using congrArg Subtype.val this
      exact Subtype.ext h1
    have := Nat.card_le_card_of_injective _ hinj
    rw [h] at this
    simp at this
  · have hle : alternatingGroup (Fin 5) ≤ H := by
      intro x hx
      have : (⟨x, hx⟩ : alternatingGroup (Fin 5)) ∈ H.subgroupOf (alternatingGroup (Fin 5)) := by
        rw [htop]; trivial
      exact this
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h, gl24_card_alt5])).symm

theorem gl24_eq_alt_of_orders (P : Subgroup (Perm (Fin 5))) (hPA : P ≤ alternatingGroup (Fin 5))
    (x y z : Perm (Fin 5)) (hx : x ∈ P) (hy : y ∈ P) (hz : z ∈ P)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1) : P = alternatingGroup (Fin 5) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdiv : ∀ (w : Perm (Fin 5)) (hw : w ∈ P) (p : ℕ) [Fact p.Prime], w ^ p = 1 → w ≠ 1 →
      p ∣ Nat.card P := by
    intro w hw p _ hwp hw1
    have h := orderOf_dvd_natCard (⟨w, hw⟩ : P)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hwp hw1] at h
  have h2 := hdiv x hx 2 hx2 hx1
  have h3 := hdiv y hy 3 hy3 hy1
  have h5 := hdiv z hz 5 hz5 hz1
  have hd : Nat.card P ∣ 60 := by
    rw [← gl24_card_alt5]
    exact Subgroup.card_dvd_of_le hPA
  have hle : Nat.card P ≤ 60 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hcases : Nat.card P = 30 ∨ Nat.card P = 60 := by omega
  rcases hcases with hn | hn
  · exfalso
    have hQ : Nat.card (P.subgroupOf (alternatingGroup (Fin 5))) = 30 := by
      rw [← hn]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv
    have hidx : (P.subgroupOf (alternatingGroup (Fin 5))).index = 2 := by
      have := (P.subgroupOf (alternatingGroup (Fin 5))).card_mul_index
      rw [hQ, gl24_card_alt5] at this
      omega
    have : (P.subgroupOf (alternatingGroup (Fin 5))).Normal := Subgroup.normal_of_index_eq_two hidx
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf (alternatingGroup (Fin 5)))
      with h | h
    · rw [h] at hQ
      simp at hQ
    · rw [h, Subgroup.card_top, gl24_card_alt5] at hQ
      omega
  · exact Subgroup.eq_of_le_of_card_ge hPA (by rw [gl24_card_alt5]; omega)

theorem gl24_perm_three_of_normalizes (P : Subgroup (Perm (Fin 5)))
    (hPA : P ≤ alternatingGroup (Fin 5)) (a u : Perm (Fin 5)) (haP : a ∈ P) (huP : u ∈ P)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hN : ∀ g ∈ P, g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹) : Nonempty (↥P ≃* Perm (Fin 3)) := by
  have hsign : ∀ p ∈ P, Perm.sign p = 1 := fun p hp => Perm.mem_alternatingGroup.1 (hPA hp)
  have hsupp : ∀ g ∈ P, ∀ x, x ∈ a.support ↔ g x ∈ a.support := by
    intro g hg x
    have hb := hN g⁻¹ (P.inv_mem hg)
    rw [inv_inv] at hb
    have key : ((g⁻¹ * a * g) x = x ↔ a (g x) = g x) := by
      simp only [Perm.mul_apply]
      rw [Perm.inv_eq_iff_eq]
    rw [Perm.mem_support, Perm.mem_support, ← not_iff_not, not_not, not_not, ← key]
    rcases hb with hb | hb
    · rw [hb]
    · rw [hb, Perm.inv_eq_iff_eq, eq_comm]
  let φ : P →* Perm {x // x ∈ a.support} :=
    { toFun := fun g => (g : Perm (Fin 5)).subtypePerm (fun x => (hsupp g g.2 x).symm)
      map_one' := by
        ext x
        simp
      map_mul' := fun g h => by
        ext x
        rfl }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine gl24_fix_three a ha3 ha1 g (hsign g g.2) ?_
    intro x hx
    have := congrArg
      (fun f : Perm {x // x ∈ a.support} => (f ⟨x, Perm.mem_support.2 hx⟩ : Fin 5)) hg
    simpa [φ] using this
  have hcard : Nat.card (Perm {x // x ∈ a.support}) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe,
      gl24_card_support_three a ha3 ha1]
    decide
  have hP6 : ∀ (w : Perm (Fin 5)) (hw : w ∈ P) (p : ℕ) [Fact p.Prime], w ^ p = 1 → w ≠ 1 →
      p ∣ Nat.card φ.range := by
    intro w hw p _ hwp hw1
    have hφw : φ ⟨w, hw⟩ ^ p = 1 := by
      rw [← map_pow]
      have : (⟨w, hw⟩ : P) ^ p = 1 := Subtype.ext (by simpa using hwp)
      rw [this, map_one]
    have hφne : φ ⟨w, hw⟩ ≠ 1 := by
      intro h
      have := hinj (h.trans (map_one φ).symm)
      exact hw1 (congrArg Subtype.val this)
    have hord : orderOf (⟨φ ⟨w, hw⟩, MonoidHom.mem_range.2 ⟨⟨w, hw⟩, rfl⟩⟩ : φ.range) = p := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hφw hφne
    rw [← hord]
    exact orderOf_dvd_natCard _
  have h2 := hP6 u huP 2 (by rw [sq]; exact hu2) hu1
  have h3 := hP6 a haP 3 ha3 ha1
  have hdv : Nat.card φ.range ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  have hR : Nat.card φ.range = 6 := by
    have : 6 ∣ Nat.card φ.range := by omega
    exact Nat.dvd_antisymm hdv this
  have hsurj : Function.Surjective φ := by
    have : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (hR.trans hcard.symm)
    exact MonoidHom.range_eq_top.1 this
  have e3 : {x // x ∈ a.support} ≃ Fin 3 := Fintype.equivFinOfCardEq
    (by rw [Fintype.card_coe, gl24_card_support_three a ha3 ha1])
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).trans e3.permCongrHom⟩

theorem gl24_s3_of_no_five (P : Subgroup (Perm (Fin 5))) (hPA : P ≤ alternatingGroup (Fin 5))
    (h5 : ∀ c ∈ P, c ^ 5 = 1 → c = 1) (u₁ u₂ : Perm (Fin 5)) (hu₁ : u₁ ∈ P) (hu₂ : u₂ ∈ P)
    (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1) (hnc : u₁ * u₂ ≠ u₂ * u₁) :
    Nonempty (↥P ≃* Perm (Fin 3)) ∧ ∃ a ∈ P, a ^ 3 = 1 ∧ a ≠ 1 := by
  have hsign : ∀ p ∈ P, Perm.sign p = 1 := fun p hp => Perm.mem_alternatingGroup.1 (hPA hp)
  have hi1 : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right h1
  have hi2 : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right h2
  have haP : u₁ * u₂ ∈ P := P.mul_mem hu₁ hu₂
  have hu1ne : u₁ ≠ 1 := by
    intro h
    apply hnc
    rw [h, one_mul, mul_one]
  have ha_ne : u₁ * u₂ ≠ 1 := by
    intro h
    apply hnc
    have : u₂ = u₁ := by
      calc u₂ = u₁⁻¹ * (u₁ * u₂) := by group
        _ = u₁ := by rw [h, mul_one, hi1]
    rw [this]
  have ha3 : (u₁ * u₂) ^ 3 = 1 := by
    rcases gl24_ord_alt5 (u₁ * u₂) (hsign _ haP) with h | h | h
    · exfalso
      apply hnc
      have : u₁ * u₂ * (u₁ * u₂) = 1 := by rw [← sq]; exact h
      calc u₁ * u₂ = (u₁ * u₂ * (u₁ * u₂)) * (u₂⁻¹ * u₁⁻¹) := by group
        _ = u₂ * u₁ := by rw [this, one_mul, hi1, hi2]
    · exact h
    · exact absurd (h5 _ haP h) ha_ne
  have hua : u₁ * (u₁ * u₂) * u₁⁻¹ = (u₁ * u₂)⁻¹ := by
    rw [mul_inv_rev, hi1, hi2, ← mul_assoc, h1, one_mul]
  have hN : ∀ g ∈ P, g * (u₁ * u₂) * g⁻¹ = u₁ * u₂ ∨ g * (u₁ * u₂) * g⁻¹ = (u₁ * u₂)⁻¹ := by
    intro g hg
    rcases gl24_five_of_not_normalizing (u₁ * u₂) (hsign _ haP) ha3 ha_ne u₁ (hsign _ hu₁) h1 hua
      g (hsign g hg) with h | h | h | h | h
    · exact h
    · exact absurd (h5 g hg h.1) h.2
    · exact absurd (h5 _ (P.mul_mem hg hu₁) h.1) h.2
    · exact absurd (h5 _ (P.mul_mem hg haP) h.1) h.2
    · exact absurd (h5 _ (P.mul_mem (P.mul_mem hg hu₁) haP) h.1) h.2
  exact ⟨gl24_perm_three_of_normalizes P hPA (u₁ * u₂) u₁ haP hu₁ ha3 ha_ne h1 hu1ne hN,
    u₁ * u₂, haP, ha3, ha_ne⟩

theorem gl24_claim_s (P : Subgroup (Perm (Fin 5))) (hPA : P ≤ alternatingGroup (Fin 5))
    (s : Perm (Fin 5)) (hs2 : s * s = 1) (hsodd : Perm.sign s = -1)
    (hsP : ∀ p ∈ P, s * p * s⁻¹ ∈ P)
    (u₁ u₂ : Perm (Fin 5)) (hu₁ : u₁ ∈ P) (hu₂ : u₂ ∈ P) (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1)
    (hnc : u₁ * u₂ ≠ u₂ * u₁) :
    (P = alternatingGroup (Fin 5) ∨ Nonempty (↥P ≃* Perm (Fin 3))) ∧
      ∃ a ∈ P, a ^ 3 = 1 ∧ a ≠ 1 := by
  have hsign : ∀ p ∈ P, Perm.sign p = 1 := fun p hp => Perm.mem_alternatingGroup.1 (hPA hp)
  have hu1ne : u₁ ≠ 1 := by
    intro h
    apply hnc
    rw [h, one_mul, mul_one]
  by_cases h5 : ∃ c ∈ P, c ^ 5 = 1 ∧ c ≠ 1
  · obtain ⟨c, hcP, hc5, hc1⟩ := h5
    have hc' := hsP c hcP
    obtain ⟨b, hbP, hb3, hb1⟩ : ∃ b ∈ P, b ^ 3 = 1 ∧ b ≠ 1 := by
      rcases gl24_three_of_five c (hsign c hcP) hc5 hc1 s hs2 hsodd with ⟨h3, hne⟩ | ⟨h3, hne⟩
      · exact ⟨_, P.mul_mem hcP hc', h3, hne⟩
      · exact ⟨_, P.mul_mem hcP (P.pow_mem hc' 3), h3, hne⟩
    exact ⟨Or.inl (gl24_eq_alt_of_orders P hPA u₁ b c hu₁ hbP hcP (by rw [sq]; exact h1) hu1ne
      hb3 hb1 hc5 hc1), b, hbP, hb3, hb1⟩
  · push Not at h5
    have h := gl24_s3_of_no_five P hPA h5 u₁ u₂ hu₁ hu₂ h1 h2 hnc
    exact ⟨Or.inr h.1, h.2⟩

end G118

end G11

end CFSG.Quasithin
