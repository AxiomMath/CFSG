module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.RankThreeEvenClassification.ClassTwoPairing
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.FixedRank36

open scoped commutatorElement
open CFSG

section Extraspecial

variable {S : Type*} [Group S]

theorem exists_center_generator [Finite S] (hS : IsExtraspecialPGroup 2 S) :
    ∃ z : S, Subgroup.center S = Subgroup.zpowers z ∧ z ≠ 1 ∧ z * z = 1 := by
  obtain ⟨z, hzc, hz1⟩ : ∃ z ∈ Subgroup.center S, z ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Subgroup.center S = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    have h2 := hS.2.2.2
    rw [h1, Subgroup.card_bot] at h2
    omega
  have hle : Subgroup.zpowers z ≤ Subgroup.center S := Subgroup.zpowers_le.2 hzc
  have hdvd : orderOf z ∣ 2 := by
    rw [← Nat.card_zpowers, ← hS.2.2.2]
    exact Subgroup.card_dvd_of_le hle
  have hord : orderOf z = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  refine ⟨z, ?_, hz1, ?_⟩
  · symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, hord, hS.2.2.2]
  · rw [← pow_two, ← hord, pow_orderOf_eq_one]

theorem eq_one_or_eq_of_mem_center {z : S} (hz : Subgroup.center S = Subgroup.zpowers z)
    (hz1 : z ≠ 1) (hzz : z * z = 1) {c : S} (hc : c ∈ Subgroup.center S) : c = 1 ∨ c = z := by
  rw [hz] at hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  rw [← zpow_mod_orderOf, hord] at hk
  have hk2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk2 with h0 | h1
  · left
    rw [← hk, h0, zpow_zero]
  · right
    rw [← hk, h1, zpow_one]

theorem commutator_mem_center (hS : IsExtraspecialPGroup 2 S) (x y : S) :
    ⁅x, y⁆ ∈ Subgroup.center S := by
  rw [← hS.2.1, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem sq_mem_center [Finite S] (hS : IsExtraspecialPGroup 2 S) (x : S) :
    x ^ 2 ∈ Subgroup.center S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 S) := ⟨hS.1⟩
  rw [← hS.2.2.1]
  exact pth_power_mem_frattini_of_isPGroup (p := 2) x

theorem exists_noncentral_involution [Finite S] (hS : IsExtraspecialPGroup 2 S)
    (hS32 : Nat.card S = 32) : ∃ s : S, s ∉ Subgroup.center S ∧ orderOf s = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hz1, hzz⟩ := exists_center_generator hS
  have hcl : commutator S ≤ Subgroup.center S := hS.2.1.le
  obtain ⟨x, hx⟩ : ∃ x : S, x ∉ Subgroup.center S := by
    by_contra h
    push Not at h
    have h1 : Subgroup.center S = ⊤ := eq_top_iff.2 fun x _ => h x
    have h2 := hS.2.2.2
    rw [h1, Subgroup.card_top, hS32] at h2
    omega
  set f := CFSG.RankThreeEvenClassification.Helpers.classTwoCommutatorHomRight hcl x with hf
  have hker : f.ker = Subgroup.centralizer {x} := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : ⁅x, y⁆ = 1 := congrArg Subtype.val h
      rw [commutatorElement_eq_one_iff_mul_comm] at h'
      exact h'.symm
    · intro h
      apply Subtype.ext
      show ⁅x, y⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h.symm
  have hC : 16 ≤ Nat.card (Subgroup.centralizer {x}) := by
    have h1 := Subgroup.card_ker_mul_card_range f
    have h2 : Nat.card f.range ≤ 2 := by
      rw [← hS.2.2.2]
      exact Subgroup.card_le_card_group _
    rw [hker, hS32] at h1
    by_contra hb
    push Not at hb
    have h3 : Nat.card (Subgroup.centralizer {x}) * Nat.card f.range ≤ 15 * 2 :=
      Nat.mul_le_mul (by omega) h2
    omega
  obtain ⟨y, hyC, hyZ, hyxZ⟩ : ∃ y ∈ Subgroup.centralizer ({x} : Set S), y ∉ Subgroup.center S ∧
      x⁻¹ * y ∉ Subgroup.center S := by
    by_contra h
    push Not at h
    have hsub : (Subgroup.centralizer ({x} : Set S) : Set S) ⊆
        (Subgroup.center S : Set S) ∪ (fun c => x * c) '' (Subgroup.center S : Set S) := by
      intro y hy
      by_cases hyZ : y ∈ Subgroup.center S
      · exact Or.inl hyZ
      · exact Or.inr ⟨x⁻¹ * y, h y hy hyZ, by simp⟩
    have hB : ((Subgroup.center S : Set S) ∪
        (fun c => x * c) '' (Subgroup.center S : Set S)).ncard ≤ 4 := by
      refine (Set.ncard_union_le _ _).trans ?_
      have h1 : (Subgroup.center S : Set S).ncard = 2 := by
        rw [← Nat.card_coe_set_eq]
        exact hS.2.2.2
      have h2 : ((fun c => x * c) '' (Subgroup.center S : Set S)).ncard ≤ 2 :=
        (Set.ncard_image_le (Set.toFinite _)).trans h1.le
      omega
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h4 : (Subgroup.centralizer ({x} : Set S) : Set S).ncard =
        Nat.card (Subgroup.centralizer {x}) := (Nat.card_coe_set_eq _).symm
    omega
  have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
  have hx1 : x ≠ 1 := fun h => hx (h ▸ Subgroup.one_mem _)
  have hy1 : y ≠ 1 := fun h => hyZ (h ▸ Subgroup.one_mem _)
  have hsq := fun (w : S) => eq_one_or_eq_of_mem_center hz hz1 hzz (sq_mem_center hS w)
  rcases hsq x with hx2 | hx2
  · exact ⟨x, hx, orderOf_eq_prime hx2 hx1⟩
  rcases hsq y with hy2 | hy2
  · exact ⟨y, hyZ, orderOf_eq_prime hy2 hy1⟩
  have hxyZ : x * y ∉ Subgroup.center S := by
    intro hxy
    apply hyxZ
    have hx2c : x ^ 2 ∈ Subgroup.center S := sq_mem_center hS x
    have h1 : x⁻¹ * y = (x ^ 2)⁻¹ * (x * y) := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx2c) hxy
  have hxy1 : x * y ≠ 1 := fun h => hxyZ (h ▸ Subgroup.one_mem _)
  refine ⟨x * y, hxyZ, orderOf_eq_prime ?_ hxy1⟩
  have hc : Commute x y := hyx.symm
  rw [hc.mul_pow, hx2, hy2, hzz]

end Extraspecial

section Fixed

theorem card_modEq_one_of_fixed {G : Type*} [Group G] [Finite G] {A : Type*} [Group A]
    (hA : IsPGroup 5 A) (ψ : A →* MulAut G) (a₀ : A) (hfix : ∀ x : G, ψ a₀ x = x → x = 1)
    (U : Subgroup G) (hU : ∀ a : A, ∀ x ∈ U, ψ a x ∈ U) : Nat.card U ≡ 1 [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let : MulAction A U :=
    { smul := fun a x => ⟨ψ a x, hU a x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ψ 1 (x : G) = x
        rw [map_one]
        rfl)
      mul_smul := fun a b x => Subtype.ext (by
        show ψ (a * b) (x : G) = ψ a (ψ b x)
        rw [map_mul]
        rfl) }
  have hmod := hA.card_modEq_card_fixedPoints U
  have hfp : Nat.card (MulAction.fixedPoints A U) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have hone : ∀ x : U, (∀ a : A, a • x = x) → x = 1 := by
      intro x hx
      apply Subtype.ext
      apply hfix
      exact congrArg Subtype.val (hx a₀)
    refine ⟨⟨fun x y => ?_⟩, ⟨⟨1, fun a => ?_⟩⟩⟩
    · exact Subtype.ext ((hone x.1 x.2).trans (hone y.1 y.2).symm)
    · apply Subtype.ext
      show ψ a (1 : G) = 1
      rw [map_one]
  rwa [hfp] at hmod

end Fixed

section Abelianization

variable {S : Type*} [Group S]

theorem of_eq_one_iff (hS : IsExtraspecialPGroup 2 S) (s : S) :
    Abelianization.of s = 1 ↔ s ∈ Subgroup.center S := by
  rw [← hS.2.1]
  exact QuotientGroup.eq_one_iff s

theorem of_eq_of_iff (hS : IsExtraspecialPGroup 2 S) (s t : S) :
    Abelianization.of s = Abelianization.of t ↔ s⁻¹ * t ∈ Subgroup.center S := by
  rw [← hS.2.1]
  exact QuotientGroup.eq

theorem card_abelianization [Finite S] (hS : IsExtraspecialPGroup 2 S) (hS32 : Nat.card S = 32) :
    Nat.card (Abelianization S) = 16 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator S)
  have hc : Nat.card (commutator S) = 2 := by
    rw [hS.2.1]
    exact hS.2.2.2
  rw [hc, hS32] at h
  have h16 : Nat.card (S ⧸ commutator S) = 16 := by omega
  exact h16

theorem abelianization_sq [Finite S] (hS : IsExtraspecialPGroup 2 S) (x : Abelianization S) :
    x ^ 2 = 1 := by
  refine QuotientGroup.induction_on x ?_
  intro s
  show Abelianization.of s ^ 2 = 1
  rw [← map_pow]
  exact (of_eq_one_iff hS _).2 (sq_mem_center hS s)

@[expose] noncomputable def abAut {A : Type*} [Group A] (φ : A →* MulAut S) :
    A →* MulAut (Abelianization S) where
  toFun a := (φ a).abelianizationCongr
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro s
    show Abelianization.of (φ 1 s) = Abelianization.of s
    rw [map_one]
    rfl
  map_mul' a b := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro s
    show Abelianization.of (φ (a * b) s) = Abelianization.of (φ a (φ b s))
    rw [map_mul]
    rfl

theorem abAut_of {A : Type*} [Group A] (φ : A →* MulAut S) (a : A) (s : S) :
    abAut φ a (Abelianization.of s) = Abelianization.of (φ a s) := rfl

theorem center_fixed [Finite S] {A : Type*} [Group A] (φ : A →* MulAut S)
    (hS : IsExtraspecialPGroup 2 S) {z : S} (hz : Subgroup.center S = Subgroup.zpowers z)
    (a : A) : φ a z = z := by
  obtain ⟨z', hz', hz1, hzz⟩ := exists_center_generator hS
  have hzc : z ∈ Subgroup.center S := hz ▸ Subgroup.mem_zpowers z
  have hz1' : z ≠ 1 := by
    intro h
    rw [h, Subgroup.zpowers_one_eq_bot] at hz
    have h2 := hS.2.2.2
    rw [hz, Subgroup.card_bot] at h2
    omega
  have hzz' : z * z = 1 := by
    rcases eq_one_or_eq_of_mem_center hz' hz1 hzz hzc with h | h
    · exact absurd h hz1'
    · rw [h]
      exact hzz
  have hcen : φ a z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.1 hzc ((φ a)⁻¹ g)
    have h2 : g = φ a ((φ a)⁻¹ g) := by simp
    calc g * φ a z = φ a ((φ a)⁻¹ g) * φ a z := by rw [← h2]
      _ = φ a ((φ a)⁻¹ g * z) := (map_mul _ _ _).symm
      _ = φ a (z * (φ a)⁻¹ g) := by rw [h1]
      _ = φ a z * φ a ((φ a)⁻¹ g) := map_mul _ _ _
      _ = φ a z * g := by rw [← h2]
  rcases eq_one_or_eq_of_mem_center hz hz1' hzz' hcen with h | h
  · exact absurd ((map_eq_one_iff (φ a) (φ a).injective).1 h) hz1'
  · exact h

theorem fixed_abelianization [Finite S] {A : Type*} [Group A] (φ : A →* MulAut S)
    (hS : IsExtraspecialPGroup 2 S) (a₀ : A)
    (hfpf : ∀ s : S, s ∉ Subgroup.center S → (φ a₀ s)⁻¹ * s ∉ Subgroup.center S)
    (x : Abelianization S) (hx : abAut φ a₀ x = x) : x = 1 := by
  refine QuotientGroup.induction_on x (fun s hs => ?_) hx
  by_contra hne
  have hs' : s ∉ Subgroup.center S := fun h => hne ((of_eq_one_iff hS s).2 h)
  apply hfpf s hs'
  have h1 : Abelianization.of (φ a₀ s) = Abelianization.of s := hs
  exact (of_eq_of_iff hS _ _).1 h1

theorem abAut_irreducible [Finite S] {A : Type*} [Group A] (φ : A →* MulAut S)
    (hS : IsExtraspecialPGroup 2 S) (hS32 : Nat.card S = 32) (hA : IsPGroup 5 A) (a₀ : A)
    (hfpf : ∀ s : S, s ∉ Subgroup.center S → (φ a₀ s)⁻¹ * s ∉ Subgroup.center S) :
    ∀ U : Subgroup (Abelianization S), (∀ a : A, ∀ x ∈ U, abAut φ a x ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hmod := card_modEq_one_of_fixed hA (abAut φ) a₀ (fixed_abelianization φ hS a₀ hfpf) U hU
  have hdvd : Nat.card U ∣ 2 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card U
    rwa [card_abelianization hS hS32] at this
  obtain ⟨k, hk, hkU⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk' : k = 0 ∨ k = 4 := by
    rw [hkU] at hmod
    unfold Nat.ModEq at hmod
    interval_cases k <;> simp_all
  rcases hk' with rfl | rfl
  · left
    rw [← Subgroup.card_eq_one, hkU]
    rfl
  · right
    apply Subgroup.eq_top_of_card_eq
    rw [hkU, card_abelianization hS hS32]
    norm_num

theorem abAut_range_card [Finite S] {A : Type*} [Group A] [Finite A] (φ : A →* MulAut S)
    (hS : IsExtraspecialPGroup 2 S) (hS32 : Nat.card S = 32) (hA : IsPGroup 5 A)
    (hAc : ∀ a b : A, a * b = b * a) (a₀ : A)
    (hfpf : ∀ s : S, s ∉ Subgroup.center S → (φ a₀ s)⁻¹ * s ∉ Subgroup.center S) :
    Nat.card (abAut φ).range = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hirr := abAut_irreducible φ hS hS32 hA a₀ hfpf
  have hΓ : IsPGroup 5 (abAut φ).range :=
    hA.of_surjective (abAut φ).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨k, hk⟩ := hΓ.exists_card_eq
  have hcard16 := card_abelianization hS hS32
  obtain ⟨x, hx1⟩ : ∃ x : Abelianization S, x ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card (Abelianization S) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  have hfree : ∀ γ ∈ (abAut φ).range, γ ≠ 1 → ∀ y : Abelianization S, γ y = y → y = 1 := by
    rintro _ ⟨b, rfl⟩ hb y hy
    let U : Subgroup (Abelianization S) :=
      { carrier := {w | abAut φ b w = w}
        mul_mem' := fun {u v} hu hv => by
          show abAut φ b (u * v) = u * v
          rw [map_mul]
          exact congrArg₂ _ hu hv
        one_mem' := map_one _
        inv_mem' := fun {u} hu => by
          show abAut φ b u⁻¹ = u⁻¹
          rw [map_inv]
          exact congrArg _ hu }
    have hUinv : ∀ a : A, ∀ w ∈ U, abAut φ a w ∈ U := by
      intro a w hw
      show abAut φ b (abAut φ a w) = abAut φ a w
      have h1 : (abAut φ b) ((abAut φ a) w) = (abAut φ a) ((abAut φ b) w) := by
        rw [← MulAut.mul_apply, ← map_mul, hAc b a, map_mul, MulAut.mul_apply]
      rw [h1, show abAut φ b w = w from hw]
    rcases hirr U hUinv with h | h
    · have hyU : y ∈ U := hy
      rw [h] at hyU
      exact hyU
    · exfalso
      apply hb
      ext w
      have hwU : w ∈ U := h ▸ Subgroup.mem_top w
      exact hwU
  have hle : Nat.card (abAut φ).range ≤ 16 := by
    rw [← hcard16]
    refine Nat.card_le_card_of_injective (fun γ : (abAut φ).range => (γ : MulAut _) x) ?_
    intro γ γ' hγ
    by_contra hne
    have hne' : γ'⁻¹ * γ ≠ 1 := fun h => hne (inv_mul_eq_one.1 h).symm
    have hδ : ((γ'⁻¹ * γ : ↥(abAut φ).range) : MulAut (Abelianization S)) =
        (γ' : MulAut (Abelianization S))⁻¹ * (γ : MulAut (Abelianization S)) := rfl
    have hδ1 : ((γ'⁻¹ * γ : ↥(abAut φ).range) : MulAut (Abelianization S)) ≠ 1 :=
      fun h => hne' (Subtype.ext h)
    have h1 : ((γ'⁻¹ * γ : ↥(abAut φ).range) : MulAut (Abelianization S)) x = x := by
      rw [hδ, MulAut.mul_apply, show (γ : MulAut (Abelianization S)) x =
        (γ' : MulAut (Abelianization S)) x from hγ.symm.symm, ← MulAut.mul_apply, inv_mul_cancel]
      rfl
    exact hx1 (hfree _ (γ'⁻¹ * γ).2 hδ1 x h1)
  have hnt : Nat.card (abAut φ).range ≠ 1 := by
    intro h1
    have h2 : (abAut φ).range = ⊥ := Subgroup.card_eq_one.1 h1
    have h3 : abAut φ a₀ = 1 := by
      have : abAut φ a₀ ∈ (abAut φ).range := ⟨a₀, rfl⟩
      rw [h2] at this
      exact this
    have h4 : abAut φ a₀ x = x := by rw [h3]; rfl
    exact hx1 (fixed_abelianization φ hS a₀ hfpf x h4)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hnt (by rw [hk]; rfl)
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    have : 5 ^ 2 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  have hk1' : k = 1 := by omega
  rw [hk, hk1']
  rfl

end Abelianization

end CFSG.RankThree.PartOne.FixedRank36
