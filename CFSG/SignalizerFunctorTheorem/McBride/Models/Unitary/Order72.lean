module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Simproc.Factors
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame

structure Order72 (G : Type*) [Group G] : Prop where
  card : Nat.card G = 72
  not_three_dvd : ∀ x t : G, orderOf t = 2 → x * t = t * x → ¬ 3 ∣ orderOf x

namespace Order72

variable {G : Type*} [Group G] [Finite G]

theorem card_sylow_three (h : Order72 G) (P : Sylow 3 G) : Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, h.card]
  have : Nat.factorization 72 3 = 2 := by norm_num [Nat.factorization]
  rw [this]
  norm_num

omit [Finite G] in
theorem isMulCommutative_of_card_nine (P : Subgroup G) (hP : Nat.card P = 9) :
    IsMulCommutative P :=
  IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP]; norm_num)

theorem card_inf_eq_three (h : Order72 G) {P P' : Subgroup G} (hP : Nat.card P = 9)
    (hP' : Nat.card P' = 9) (hne : P ≠ P') : Nat.card ↥(P ⊓ P') = 3 := by
  have hindex : (P ⊓ P').index ≤ P.index * P'.index := Subgroup.index_inf_le
  have hPi : P.index = 8 := by
    have := P.card_mul_index
    rw [hP, h.card] at this
    omega
  have hPi' : P'.index = 8 := by
    have := P'.card_mul_index
    rw [hP', h.card] at this
    omega
  rw [hPi, hPi'] at hindex
  have hmul := (P ⊓ P').card_mul_index
  rw [h.card] at hmul
  have hdvd : Nat.card ↥(P ⊓ P') ∣ 9 := hP ▸ Subgroup.card_dvd_of_le inf_le_left
  have hpos : 0 < Nat.card ↥(P ⊓ P') := Nat.card_pos
  have hge : 2 ≤ Nat.card ↥(P ⊓ P') := by
    by_contra hlt
    have h1 : Nat.card ↥(P ⊓ P') = 1 := by omega
    rw [h1] at hmul
    omega
  have hcases : Nat.card ↥(P ⊓ P') = 3 ∨ Nat.card ↥(P ⊓ P') = 9 := by
    have : Nat.card ↥(P ⊓ P') ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h9 : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [h9] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  rcases hcases with h3 | h9
  · exact h3
  · exfalso
    have h1 : P ⊓ P' = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hP])
    have h2 : P ⊓ P' = P' := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h9, hP'])
    exact hne (h1.symm.trans h2)

theorem subsingleton_sylow_three (h : Order72 G) : Subsingleton (Sylow 3 G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨fun P₁ P₂ => ?_⟩
  by_contra hne
  have hne' : (P₁ : Subgroup G) ≠ P₂ := fun he => hne (Sylow.ext he)
  have h1 := h.card_sylow_three P₁
  have h2 := h.card_sylow_three P₂
  have hinf := h.card_inf_eq_three h1 h2 hne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥((P₁ : Subgroup G) ⊓ P₂)) 3
    (by rw [hinf])
  have hx3 : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hxP₁ : (x : G) ∈ (P₁ : Subgroup G) := x.2.1
  have hxP₂ : (x : G) ∈ (P₂ : Subgroup G) := x.2.2
  have hc₁ := isMulCommutative_of_card_nine (P₁ : Subgroup G) h1
  have hc₂ := isMulCommutative_of_card_nine (P₂ : Subgroup G) h2
  set Z : Subgroup G := Subgroup.centralizer ({(x : G)} : Set G) with hZ
  have hle₁ : (P₁ : Subgroup G) ≤ Z := by
    intro g hg
    rw [hZ, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hc₁.is_comm.comm ⟨g, hg⟩ ⟨(x : G), hxP₁⟩)
  have hle₂ : (P₂ : Subgroup G) ≤ Z := by
    intro g hg
    rw [hZ, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hc₂.is_comm.comm ⟨g, hg⟩ ⟨(x : G), hxP₂⟩)
  have h9Z : 9 ∣ Nat.card Z := h1 ▸ Subgroup.card_dvd_of_le hle₁
  have hZdvd : Nat.card Z ∣ 72 := h.card ▸ Subgroup.card_subgroup_dvd_card Z
  have hZne : Nat.card Z ≠ 9 := by
    intro h9
    have e₁ : (P₁ : Subgroup G) = Z := Subgroup.eq_of_le_of_card_ge hle₁ (by rw [h9, h1])
    have e₂ : (P₂ : Subgroup G) = Z := Subgroup.eq_of_le_of_card_ge hle₂ (by rw [h9, h2])
    exact hne' (e₁.trans e₂.symm)
  have h2Z : 2 ∣ Nat.card Z := by
    have hmem : Nat.card Z ∈ Nat.divisors 72 := Nat.mem_divisors.mpr ⟨hZdvd, by norm_num⟩
    have h72 : Nat.divisors 72 = {1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72} := by decide
    rw [h72] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h2Z
  have hu2 : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have hcomm : (x : G) * u = u * x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp u.2
    exact this.symm
  exact h.not_three_dvd (x : G) u hu2 hcomm (by rw [hx3])


omit [Finite G] in
theorem orderOf_dvd_nine_of_odd (h : Order72 G) {x : G} (hx : ¬ 2 ∣ orderOf x) :
    orderOf x = 1 ∨ orderOf x = 3 ∨ orderOf x = 9 := by
  have hdvd72 : orderOf x ∣ 72 := h.card ▸ orderOf_dvd_natCard x
  have hmem : orderOf x ∈ Nat.divisors 72 := Nat.mem_divisors.mpr ⟨hdvd72, by norm_num⟩
  have h72 : Nat.divisors 72 = {1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72} := by decide
  rw [h72] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem mem_of_not_two_dvd (h : Order72 G) (P : Sylow 3 G) {x : G} (hx : ¬ 2 ∣ orderOf x) :
    x ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.subsingleton_sylow_three
  have hzp : IsPGroup 3 (Subgroup.zpowers x) := by
    rcases h.orderOf_dvd_nine_of_odd hx with h1 | h3 | h9
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3]; norm_num)
    · exact IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, h9]; norm_num)
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  rw [Subsingleton.elim P Q]
  exact hQ (Subgroup.mem_zpowers x)

theorem two_dvd_orderOf_of_not_mem (h : Order72 G) (P : Sylow 3 G) {x : G} (hx : x ∉ P) :
    2 ∣ orderOf x := by
  by_contra h2
  exact hx (h.mem_of_not_two_dvd P h2)

theorem eq_one_of_commute_involution (h : Order72 G) (P : Sylow 3 G) {x u : G} (hx : x ∈ P)
    (hu : orderOf u = 2) (hc : x * u = u * x) : x = 1 := by
  by_contra hx1
  have hdvd : orderOf x ∣ 9 := by
    have := Subgroup.orderOf_dvd_natCard (P : Subgroup G) hx
    rwa [h.card_sylow_three P] at this
  have h3 : 3 ∣ orderOf x := by
    obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show orderOf x ∣ 3 ^ 2 by simpa using hdvd)
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.mp (by simpa using hord))
    rw [hord]
    exact dvd_pow_self 3 hi0
  exact h.not_three_dvd x u hu hc h3

omit [Finite G] in
theorem inv_eq_self_of_orderOf_eq_two {u : G} (hu : orderOf u = 2) : u⁻¹ = u := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  exact inv_eq_of_mul_eq_one_right hu2

theorem conj_eq_inv_of_involution (h : Order72 G) (P : Sylow 3 G) {u : G} (hu : orderOf u = 2)
    {x : G} (hx : x ∈ P) : u * x * u⁻¹ = x⁻¹ := by
  have := h.subsingleton_sylow_three
  have hn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hc := isMulCommutative_of_card_nine (P : Subgroup G) (h.card_sylow_three P)
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  have hui2 : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
  have hyP : u * x * u⁻¹ ∈ (P : Subgroup G) := hn.conj_mem x hx u
  have hzP : x * (u * x * u⁻¹) ∈ (P : Subgroup G) := Subgroup.mul_mem _ hx hyP
  have hcomm : x * (u * x * u⁻¹) = (u * x * u⁻¹) * x :=
    congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨_, hyP⟩)
  have hyy : u * (u * x * u⁻¹) * u⁻¹ = x := by
    calc u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) := by group
      _ = x := by rw [hu2, hui2]; group
  have hzc : u * (x * (u * x * u⁻¹)) * u⁻¹ = x * (u * x * u⁻¹) := by
    calc u * (x * (u * x * u⁻¹)) * u⁻¹
        = (u * x * u⁻¹) * (u * (u * x * u⁻¹) * u⁻¹) := by group
      _ = (u * x * u⁻¹) * x := by rw [hyy]
      _ = x * (u * x * u⁻¹) := hcomm.symm
  have hz : (x * (u * x * u⁻¹)) * u = u * (x * (u * x * u⁻¹)) :=
    (mul_inv_eq_iff_eq_mul.mp hzc).symm
  have h1 := h.eq_one_of_commute_involution P hzP hu hz
  exact eq_inv_of_mul_eq_one_right h1


theorem mem_of_commute (h : Order72 G) (P : Sylow 3 G) {g x : G} (hx : x ∈ P) (hx1 : x ≠ 1)
    (hg : g * x = x * g) : g ∈ P := by
  by_contra hgP
  have h2 := h.two_dvd_orderOf_of_not_mem P hgP
  have hk : orderOf (g ^ (orderOf g / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' h2
  have hc : x * g ^ (orderOf g / 2) = g ^ (orderOf g / 2) * x :=
    (Commute.pow_left (show Commute g x from hg) _).symm.eq
  exact hx1 (h.eq_one_of_commute_involution P hx hk hc)

theorem pow_three_eq_one (h : Order72 G) (P : Sylow 3 G) {x : G} (hx : x ∈ P) : x ^ 3 = 1 := by
  by_contra hx3
  have := h.subsingleton_sylow_three
  have hn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hPcard := h.card_sylow_three P
  have hx1 : x ≠ 1 := fun h1 => hx3 (by rw [h1, one_pow])
  have hdvd : orderOf x ∣ 9 := by
    have := Subgroup.orderOf_dvd_natCard (P : Subgroup G) hx
    rwa [hPcard] at this
  have hord : orderOf x = 9 := by
    obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show orderOf x ∣ 3 ^ 2 by simpa using hdvd)
    interval_cases i
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hord)) hx1
    · have h3 : orderOf x = 3 := by simpa using hord
      exact absurd (h3 ▸ pow_orderOf_eq_one x) hx3
    · simpa using hord
  have : IsCyclic (P : Subgroup G) := isCyclic_of_orderOf_eq_card (⟨x, hx⟩ : (P : Subgroup G))
    (by rw [Subgroup.orderOf_mk, hord, hPcard])
  let φ : G →* MulAut (P : Subgroup G) := MulAut.conjNormal
  have hker : φ.ker ≤ (P : Subgroup G) := by
    intro g hg
    have hφ : φ g = 1 := hg
    have hgx : g * x * g⁻¹ = x := by
      have := congrArg (fun a : MulAut ↥(P : Subgroup G) => (a ⟨x, hx⟩ : G)) hφ
      simpa [φ, MulAut.conjNormal_apply] using this
    exact h.mem_of_commute P hx hx1 (mul_inv_eq_iff_eq_mul.mp hgx)
  have hcardAut : Nat.card (MulAut (P : Subgroup G)) = 6 := by
    rw [IsCyclic.card_mulAut, hPcard]
    decide
  have hdvd6 : φ.ker.index ∣ 6 := by
    have := Subgroup.card_dvd_of_injective (QuotientGroup.kerLift φ)
      (QuotientGroup.kerLift_injective φ)
    rwa [hcardAut] at this
  have hle : Nat.card φ.ker ≤ 9 := hPcard ▸ Subgroup.card_le_of_le hker
  have hmul := φ.ker.card_mul_index
  rw [h.card] at hmul
  have hidx : φ.ker.index ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  have := Nat.mul_le_mul hle hidx
  omega


theorem exists_conj_eq (h : Order72 G) (P : Sylow 3 G) {x y : G} (hx : x ∈ P) (hx1 : x ≠ 1)
    (hy : y ∈ P) (hy1 : y ≠ 1) : ∃ c : G, c * x * c⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.subsingleton_sylow_three
  have hn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hPcard := h.card_sylow_three P
  obtain ⟨T⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hT : Nat.card T = 8 := by
    rw [Sylow.card_eq_multiplicity, h.card]
    have : Nat.factorization 72 2 = 3 := by norm_num [Nat.factorization]
    rw [this]
    norm_num
  have hTP : ∀ t ∈ (T : Subgroup G), t ∈ (P : Subgroup G) → t = 1 := by
    intro t htT htP
    have h8 : orderOf t ∣ 8 := hT ▸ Subgroup.orderOf_dvd_natCard _ htT
    have h9 : orderOf t ∣ 9 := hPcard ▸ Subgroup.orderOf_dvd_natCard _ htP
    have h1 : orderOf t = 1 := Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h8 h9)
    exact orderOf_eq_one_iff.mp h1
  let F : T → {z : (P : Subgroup G) // z ≠ 1} := fun t =>
    ⟨⟨(t : G) * x * (t : G)⁻¹, hn.conj_mem x hx t⟩, fun h1 => hx1 (by
      have := congrArg (fun a : (P : Subgroup G) => (a : G)) h1
      simpa using this)⟩
  have hinj : Function.Injective F := by
    intro t t' htt
    have hc : (t : G) * x * (t : G)⁻¹ = (t' : G) * x * (t' : G)⁻¹ :=
      congrArg (fun a : {z : (P : Subgroup G) // z ≠ 1} => ((a.1 : (P : Subgroup G)) : G)) htt
    have hcomm : ((t' : G)⁻¹ * t) * x = x * ((t' : G)⁻¹ * t) := by
      have : (t' : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) * t' = x := by
        rw [hc]; group
      calc ((t' : G)⁻¹ * t) * x = (t' : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) * t * 1 := by
            group
        _ = ((t' : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) * t') * ((t' : G)⁻¹ * t) := by
            group
        _ = x * ((t' : G)⁻¹ * t) := by rw [this]
    have hP' : (t' : G)⁻¹ * t ∈ (P : Subgroup G) := h.mem_of_commute P hx hx1 hcomm
    have hT' : (t' : G)⁻¹ * t ∈ (T : Subgroup G) := T.mul_mem (T.inv_mem t'.2) t.2
    have := hTP _ hT' hP'
    exact Subtype.ext (inv_mul_eq_one.mp this).symm
  have hcardP : Nat.card {z : (P : Subgroup G) // z ≠ 1} + 1 = 9 := by
    have := Fintype.ofFinite (P : Subgroup G)
    classical
    have h1 : Nat.card {z : (P : Subgroup G) // z ≠ 1} + 1 = Nat.card (P : Subgroup G) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      simp only [Fintype.card_subtype_eq]
      have : 0 < Fintype.card (P : Subgroup G) := Fintype.card_pos
      omega
    rw [h1, hPcard]
  have hc : Nat.card {z : (P : Subgroup G) // z ≠ 1} ≤ Nat.card T := by
    rw [hT]; omega
  have hbij := hinj.bijective_of_nat_card_le hc
  obtain ⟨t, ht⟩ := hbij.2 ⟨⟨y, hy⟩, fun h1 => hy1 (by simpa using congrArg Subtype.val h1)⟩
  refine ⟨t, ?_⟩
  exact congrArg (fun a : {z : (P : Subgroup G) // z ≠ 1} => ((a.1 : (P : Subgroup G)) : G)) ht

theorem eq_of_commute_involutions (h : Order72 G) {u v : G} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u * v = v * u) : u = v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have hPcard := h.card_sylow_three P
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup G)) 3
    (by rw [hPcard]; norm_num)
  have hxP : (x : G) ∈ P := x.2
  have hx1 : (x : G) ≠ 1 := by
    intro h1
    have : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
    rw [h1, orderOf_one] at this
    omega
  have hxinvP : (x : G)⁻¹ ∈ P := P.inv_mem hxP
  have h1 := h.conj_eq_inv_of_involution P hv hxP
  have h2 := h.conj_eq_inv_of_involution P hu hxinvP
  rw [inv_inv] at h2
  have hcomm : (u * v) * (x : G) = (x : G) * (u * v) := by
    have : u * v * (x : G) * (u * v)⁻¹ = x := by
      calc u * v * (x : G) * (u * v)⁻¹ = u * (v * (x : G) * v⁻¹) * u⁻¹ := by group
        _ = x := by rw [h1, h2]
    exact (mul_inv_eq_iff_eq_mul.mp this)
  have huvP : u * v ∈ P := h.mem_of_commute P hxP hx1 hcomm
  have hsq : (u * v) ^ 2 = 1 := by
    rw [pow_two]
    have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
    have hv2 : v * v = 1 := by rw [← pow_two, ← hv]; exact pow_orderOf_eq_one v
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, one_mul]
  have hd2 : orderOf (u * v) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hd9 : orderOf (u * v) ∣ 9 := hPcard ▸ Subgroup.orderOf_dvd_natCard _ huvP
  have h1' : orderOf (u * v) = 1 := Nat.dvd_one.mp (by simpa using Nat.dvd_gcd hd2 hd9)
  have huv1 : u * v = 1 := orderOf_eq_one_iff.mp h1'
  rw [mul_eq_one_iff_eq_inv.mp huv1, inv_eq_self_of_orderOf_eq_two hv]


theorem exists_central_quotient (h : Order72 G) (P : Sylow 3 G) :
    ∃ z : G, z ∉ P ∧ ∀ x : G, ⁅z, x⁆ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.subsingleton_sylow_three
  have hn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hPcard := h.card_sylow_three P
  have hQcard : Nat.card (G ⧸ (P : Subgroup G)) = 8 := by
    have := (P : Subgroup G).card_mul_index
    rw [hPcard, h.card] at this
    rw [← Subgroup.index_eq_card]
    omega
  have hQp : IsPGroup 2 (G ⧸ (P : Subgroup G)) :=
    IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num)
  have : Nontrivial (G ⧸ (P : Subgroup G)) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have := hQp.center_nontrivial
  obtain ⟨⟨zq, hzq⟩, hne⟩ := exists_ne (1 : ↥(Subgroup.center (G ⧸ (P : Subgroup G))))
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zq
  refine ⟨z, fun hz => ?_, fun x => ?_⟩
  · apply hne
    exact Subtype.ext ((QuotientGroup.eq_one_iff z).mpr hz)
  · have hcomm := Subgroup.mem_center_iff.mp hzq (x : G ⧸ (P : Subgroup G))
    have h1 : QuotientGroup.mk' (P : Subgroup G) ⁅z, x⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
    exact (QuotientGroup.eq_one_iff _).mp h1

theorem le_of_normal (h : Order72 G) (P : Sylow 3 G) {N : Subgroup G} (hN : N.Normal)
    (hN1 : N ≠ ⊥) : (P : Subgroup G) ≤ N := by
  have := h.subsingleton_sylow_three
  have hn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hPcard := h.card_sylow_three P
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup G)) 3
    (by rw [hPcard]; norm_num)
  have hx₀P : (x₀ : G) ∈ P := x₀.2
  have hx₀1 : (x₀ : G) ≠ 1 := by
    intro h1
    have : orderOf (x₀ : G) = 3 := by rw [Subgroup.orderOf_coe, hx₀]
    rw [h1, orderOf_one] at this
    omega
  by_cases hcase : ∃ x ∈ N, x ∈ (P : Subgroup G) ∧ x ≠ 1
  · obtain ⟨x, hxN, hxP, hx1⟩ := hcase
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact N.one_mem
    · obtain ⟨c, hc⟩ := h.exists_conj_eq P hxP hx1 hy hy1
      rw [← hc]
      exact hN.conj_mem x hxN c
  · exfalso
    push Not at hcase
    obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
    have hnP : (n : G) ∉ P := fun hnP => hn1 (Subtype.ext (hcase n n.2 hnP))
    have h2 := h.two_dvd_orderOf_of_not_mem P hnP
    have hk : orderOf ((n : G) ^ (orderOf (n : G) / 2)) = 2 :=
      orderOf_pow_orderOf_div (orderOf_pos (n : G)).ne' h2
    have huN : (n : G) ^ (orderOf (n : G) / 2) ∈ N := N.pow_mem n.2 _
    set u := (n : G) ^ (orderOf (n : G) / 2) with hu
    have hcN : u * (x₀ : G) * u⁻¹ * (x₀ : G)⁻¹ ∈ N := by
      have : u * ((x₀ : G) * u⁻¹ * (x₀ : G)⁻¹) ∈ N :=
        N.mul_mem huN (hN.conj_mem u⁻¹ (N.inv_mem huN) x₀)
      simpa [mul_assoc] using this
    have hcP : u * (x₀ : G) * u⁻¹ * (x₀ : G)⁻¹ ∈ (P : Subgroup G) :=
      Subgroup.mul_mem _ (hn.conj_mem _ hx₀P u) (P.inv_mem hx₀P)
    have h1 := hcase _ hcN hcP
    have hcomm : (x₀ : G) * u = u * x₀ := by
      have h3 : u * (x₀ : G) * u⁻¹ = x₀ := by
        have := congrArg (· * (x₀ : G)) h1
        simpa using this
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    exact hx₀1 (h.eq_one_of_commute_involution P hx₀P hk hcomm)


theorem fittingSubgroup_eq (h : Order72 G) (P : Sylow 3 G) :
    CFSG.fittingSubgroup G = (P : Subgroup G) := by
  have := h.subsingleton_sylow_three
  have hn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hPle : (P : Subgroup G) ≤ CFSG.fittingSubgroup G :=
    le_sSup ⟨hn, P.isPGroup'.isNilpotent⟩
  refine le_antisymm (fun x hx => ?_) hPle
  by_contra hxP
  have h2 := h.two_dvd_orderOf_of_not_mem P hxP
  have hy2 : orderOf (x ^ (orderOf x / 2)) = 2 := orderOf_pow_orderOf_div (orderOf_pos x).ne' h2
  have hyF : x ^ (orderOf x / 2) ∈ CFSG.fittingSubgroup G := Subgroup.pow_mem _ hx _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup G)) 3
    (by rw [h.card_sylow_three P]; norm_num)
  have hz3 : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hzF : (z : G) ∈ CFSG.fittingSubgroup G := hPle z.2
  have hnil : Group.IsNilpotent ↥(CFSG.fittingSubgroup G) := inferInstance
  have hy2' : orderOf (⟨x ^ (orderOf x / 2), hyF⟩ : CFSG.fittingSubgroup G) = 2 := by
    rw [Subgroup.orderOf_mk, hy2]
  have hz3' : orderOf (⟨(z : G), hzF⟩ : CFSG.fittingSubgroup G) = 3 := by
    rw [Subgroup.orderOf_mk, hz3]
  have hc : Commute (⟨x ^ (orderOf x / 2), hyF⟩ : CFSG.fittingSubgroup G) ⟨(z : G), hzF⟩ :=
    Group.IsNilpotent.commute_of_orderOf_coprime (by rw [hy2', hz3']; norm_num)
  have hcomm : (z : G) * x ^ (orderOf x / 2) = x ^ (orderOf x / 2) * z :=
    (congrArg Subtype.val hc.eq).symm
  exact h.not_three_dvd (z : G) _ hy2 hcomm (by rw [hz3])


theorem exists_sq_ne_one (h : Order72 G) {T : Subgroup G} (hT : Nat.card T = 8) :
    ∃ x ∈ T, x ^ 2 ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hTne : T ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hT
    omega
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
  have hx1' : (x : G) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hxo : orderOf (x : G) = 2 := orderOf_eq_prime (hcon x x.2) hx1'
  have hnle : ¬ T ≤ Subgroup.zpowers (x : G) := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hxo, hT] at this
    omega
  obtain ⟨y, hyT, hyz⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hy1 : y ≠ 1 := fun h1 => hyz (h1 ▸ Subgroup.one_mem _)
  have hyo : orderOf y = 2 := orderOf_eq_prime (hcon y hyT) hy1
  have hxinv : (x : G)⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxo
  have hyinv : y⁻¹ = y := inv_eq_self_of_orderOf_eq_two hyo
  have hxy : (x : G) * y * ((x : G) * y) = 1 := by
    rw [← pow_two]
    exact hcon _ (T.mul_mem x.2 hyT)
  have hcomm : (x : G) * y = y * x := by
    have := inv_eq_of_mul_eq_one_right hxy
    rw [mul_inv_rev, hxinv, hyinv] at this
    exact this.symm
  exact hyz (h.eq_of_commute_involutions hxo hyo hcomm ▸ Subgroup.mem_zpowers _)

end Order72

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame
