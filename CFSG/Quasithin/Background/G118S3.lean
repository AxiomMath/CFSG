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
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IndexNormal
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

section Order6

variable {G : Type*} [Group G]

theorem zpowers_normal_of_central {y : G} (hy : ∀ g : G, g * y = y * g) :
    (Subgroup.zpowers y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have : g * y ^ k * g⁻¹ = y ^ k := by
    have h1 : g * y * g⁻¹ = y := by rw [hy g]; group
    calc g * y ^ k * g⁻¹ = (g * y * g⁻¹) ^ k := by rw [conj_zpow]
      _ = y ^ k := by rw [h1]
  rw [this]
  exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩

theorem g118_exists_inverting [Finite G] (hG : Nat.card G = 6) {y : G} (hy2 : y * y = 1)
    (hy1 : y ≠ 1) (hno : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) :
    ∃ c : G, c ^ 3 = 1 ∧ c ≠ 1 ∧ y * c * y⁻¹ = c⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hG]; norm_num : 3 ∣ Nat.card G)
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  set Z : Subgroup G := Subgroup.zpowers c with hZ
  have hZcard : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, hc]
  have hZidx : Z.index = 2 := by
    have := Subgroup.card_mul_index Z
    rw [hZcard, hG] at this
    omega
  have : Z.Normal := Subgroup.normal_of_index_eq_two hZidx
  have hyZ : y ∉ Z := by
    intro h
    have h2 : orderOf y ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard Z h
      rwa [hZcard] at this
    have hy2' : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    rw [hy2'] at h2
    omega
  have hconj : y * c * y⁻¹ ∈ Z :=
    Subgroup.Normal.conj_mem inferInstance c (Subgroup.mem_zpowers c) y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hconj
  have hc3' : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
  have hmod : c ^ k = c ^ (k % 3) := zpow_eq_zpow_emod k hc3'
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hmod
    rw [hmod] at hk
    apply hc1
    have : y * c * y⁻¹ = 1 := hk.symm
    have h' : c = y⁻¹ * (y * c * y⁻¹) * y := by group
    rw [h', this]
    group
  ·
    exfalso
    rw [h1, zpow_one] at hmod
    rw [hmod] at hk
    have hyc : y * c = c * y := by
      have : y * c * y⁻¹ = c := hk.symm
      calc y * c = (y * c * y⁻¹) * y := by group
        _ = c * y := by rw [this]
    obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hZidx
    have hyZ' : y * a ∈ Z := by
      rcases ha y with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hyZ
    have hcentral : ∀ g : G, g * y = y * g := by
      intro g
      by_cases hg : g ∈ Z
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        have : ∀ j : ℤ, c ^ j * y = y * c ^ j := by
          intro j
          have hcomm : Commute c y := hyc.symm
          exact (hcomm.zpow_left j).eq
        exact this j
      · have hga : g * a ∈ Z := by
          rcases ha g with ⟨h, -⟩ | ⟨h, -⟩
          · exact h
          · exact absurd h hg
        have hz : g * y⁻¹ ∈ Z := by
          have := Z.mul_mem hga (Z.inv_mem hyZ')
          simpa [mul_assoc] using this
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hz
        have hgz : g = c ^ j * y := by
          calc g = (g * y⁻¹) * y := by group
            _ = c ^ j * y := by rw [← hj]
        have hcomm : Commute c y := hyc.symm
        have hcj : c ^ j * y = y * c ^ j := (hcomm.zpow_left j).eq
        rw [hgz]
        calc c ^ j * y * y = y * c ^ j * y := by rw [hcj]
          _ = y * (c ^ j * y) := by rw [mul_assoc]
    have hnormal := zpowers_normal_of_central hcentral
    have h2grp : IsPGroup 2 (Subgroup.zpowers y) := by
      have hcard2 : Nat.card (Subgroup.zpowers y) = 2 ^ 1 := by
        rw [Nat.card_zpowers, pow_one]
        exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
      exact IsPGroup.of_card hcard2
    have := hno _ hnormal h2grp
    exact hy1 (Subgroup.zpowers_eq_bot.1 this)
  · refine ⟨c, hc3, hc1, ?_⟩
    rw [h2] at hmod
    rw [hmod] at hk
    have hcinv : c ^ (2 : ℤ) = c⁻¹ := by
      have : c ^ (3 : ℤ) = 1 := hc3'
      calc c ^ (2 : ℤ) = c ^ (3 : ℤ) * c⁻¹ := by group
        _ = c⁻¹ := by rw [this, one_mul]
    rw [hcinv] at hk
    exact hk.symm

theorem eq_one_or_eq_of_mem_zpowers' {y : G} (hy2 : y * y = 1) {z : G}
    (hz : z ∈ Subgroup.zpowers y) : z = 1 ∨ z = y := by
  have hy1 : y⁻¹ = y := by
    rw [inv_eq_iff_mul_eq_one]
    exact hy2
  rw [Subgroup.zpowers_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    right
    exact hx
  | one => left; rfl
  | mul x y' _ _ hx hy' =>
    rcases hx with rfl | rfl <;> rcases hy' with rfl | rfl
    · left; simp
    · right; simp
    · right; simp
    · left; exact hy2
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · left; simp
    · right; exact hy1

theorem g118_mulEquiv_perm_three [Finite G] (hG : Nat.card G = 6) {c y : G} (hy2 : y * y = 1)
    (hy1 : y ≠ 1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hyc : y * c * y⁻¹ = c⁻¹) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  set Y : Subgroup G := Subgroup.zpowers y with hY
  have hYcard : Nat.card Y = 2 := by
    rw [hY, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hidx : Y.index = 3 := by
    have := Subgroup.card_mul_index Y
    rw [hYcard, hG] at this
    omega
  have hYnn : ¬ Y.Normal := by
    intro hN
    have h1 : c * y * c⁻¹ ∈ Y := hN.conj_mem y (Subgroup.mem_zpowers y) c
    rcases eq_one_or_eq_of_mem_zpowers' hy2 h1 with h0 | hh
    · apply hy1
      have : y = c⁻¹ * (c * y * c⁻¹) * c := by group
      rw [this, h0]
      group
    · have hcy : c * y = y * c := by
        calc c * y = (c * y * c⁻¹) * c := by group
          _ = y * c := by rw [hh]
      have hyc' : y * c * y⁻¹ = c := by
        calc y * c * y⁻¹ = (c * y) * y⁻¹ := by rw [hcy]
          _ = c := by group
      have : c = c⁻¹ := hyc'.symm.trans hyc
      apply hc1
      have h2 : c * c = 1 := by
        calc c * c = c * c⁻¹ := by rw [← this]
          _ = 1 := by group
      have h3 : c = c ^ 3 * (c * c)⁻¹ := by group
      rw [h3, hc3, h2]
      group
  let ρ : G →* Equiv.Perm (G ⧸ Y) := MulAction.toPermHom G (G ⧸ Y)
  have hker : ρ.ker = Y.normalCore := (Subgroup.normalCore_eq_ker Y).symm
  have hcoreNormal : Y.normalCore.Normal := Subgroup.normalCore_normal Y
  have hcoreLe : Y.normalCore ≤ Y := Subgroup.normalCore_le Y
  have hcoreCard : Nat.card Y.normalCore ∣ 2 := by
    rw [← hYcard]
    exact Subgroup.card_dvd_of_le hcoreLe
  have hcore : Y.normalCore = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hcoreCard with h1 | h2
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      apply hYnn
      have : Y.normalCore = Y :=
        Subgroup.eq_of_le_of_card_ge hcoreLe (by rw [h2, hYcard])
      rw [← this]
      exact hcoreNormal
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 (by rw [hker, hcore])
  have hq : Nat.card (G ⧸ Y) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hbij : Function.Bijective ρ :=
    (Nat.bijective_iff_injective_and_card ρ).2 ⟨hinj, by rw [Nat.card_perm, hq, hG]; rfl⟩
  exact ⟨(MulEquiv.ofBijective ρ hbij).trans (Finite.equivFinOfCardEq hq).permCongrHom⟩

end Order6

theorem g118_perm_three_aut_inner (φ : MulAut (Equiv.Perm (Fin 3))) :
    ∃ g : Equiv.Perm (Fin 3), ∀ x, φ x = g * x * g⁻¹ := by
  set s₀ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hs₀
  set s₁ : Equiv.Perm (Fin 3) := Equiv.swap 1 2 with hs₁
  have key : ∀ a b : Equiv.Perm (Fin 3), (a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b) →
      ∃ g : Equiv.Perm (Fin 3), g * s₀ * g⁻¹ = a ∧ g * s₁ * g⁻¹ = b := by
    decide
  have h00 : s₀ * s₀ = 1 := by decide
  have h11 : s₁ * s₁ = 1 := by decide
  have hne0 : s₀ ≠ 1 := by decide
  have hne1 : s₁ ≠ 1 := by decide
  have hne01 : s₀ ≠ s₁ := by decide
  have ha : φ s₀ * φ s₀ = 1 := by rw [← map_mul, h00, map_one]
  have hb : φ s₁ * φ s₁ = 1 := by rw [← map_mul, h11, map_one]
  have ha1 : φ s₀ ≠ 1 := fun h => hne0 (φ.injective (h.trans (map_one φ).symm))
  have hb1 : φ s₁ ≠ 1 := fun h => hne1 (φ.injective (h.trans (map_one φ).symm))
  have hab : φ s₀ ≠ φ s₁ := fun h => hne01 (φ.injective h)
  obtain ⟨g, hg0, hg1⟩ := key _ _ ⟨ha, ha1, hb, hb1, hab⟩
  refine ⟨g, fun x => ?_⟩
  have hx : x = 1 ∨ x = s₀ ∨ x = s₁ ∨ x = s₀ * s₁ ∨ x = s₁ * s₀ ∨ x = s₀ * s₁ * s₀ := by
    revert x
    decide
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact hg0.symm
  · exact hg1.symm
  · rw [map_mul, ← hg0, ← hg1]
    group
  · rw [map_mul, ← hg0, ← hg1]
    group
  · rw [map_mul, map_mul, ← hg0, ← hg1]
    group


end G118

end G11

end CFSG.Quasithin
