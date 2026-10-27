module

public import CFSG.GroupTheory.PrimeField.SteinbergBNNoncyclicFixedVector
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
public import Mathlib.GroupTheory.Nilpotent
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
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22q_exists_central_mod {p : ℕ} [Fact p.Prime] {R V₀ V : Subgroup G} (hR : IsPGroup p R)
    (hV₀V : V₀ ≤ V) (hVR : V ≤ R) (hRV : ∀ r ∈ R, ∀ v ∈ V, r * v * r⁻¹ ∈ V)
    (hRV₀ : ∀ r ∈ R, ∀ v ∈ V₀, r * v * r⁻¹ ∈ V₀) (hne : V ≠ V₀) :
    ∃ v ∈ V, v ∉ V₀ ∧ ∀ r ∈ R, r * v * r⁻¹ * v⁻¹ ∈ V₀ := by
  have hV₀R : V₀ ≤ R := hV₀V.trans hVR
  have hn₀ : (V₀.subgroupOf R).Normal := ⟨fun x hx r => by
    have := hRV₀ r r.2 x hx
    simpa [Subgroup.mem_subgroupOf] using this⟩
  have hnV : (V.subgroupOf R).Normal := ⟨fun x hx r => by
    have := hRV r r.2 x hx
    simpa [Subgroup.mem_subgroupOf] using this⟩
  haveI := hn₀
  haveI := hnV
  let π : ↥R →* ↥R ⧸ V₀.subgroupOf R := QuotientGroup.mk' (V₀.subgroupOf R)
  haveI : Group.IsNilpotent (↥R ⧸ V₀.subgroupOf R) := (hR.to_quotient (V₀.subgroupOf R)).isNilpotent
  let H : Subgroup (↥R ⧸ V₀.subgroupOf R) := (V.subgroupOf R).map π
  haveI : H.Normal := Subgroup.Normal.map hnV π (QuotientGroup.mk'_surjective _)
  have hH : H ≠ ⊥ := by
    intro hbot
    apply hne
    refine le_antisymm (fun v hv => ?_) hV₀V
    have hv' : (⟨v, hVR hv⟩ : R) ∈ V.subgroupOf R := hv
    have h1 : π ⟨v, hVR hv⟩ ∈ H := ⟨_, hv', rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := V₀.subgroupOf R) _).1 h1)
  obtain ⟨⟨z, hzmem⟩, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hH)
  obtain ⟨hzH, hzC⟩ := hzmem
  obtain ⟨r, hrV, rfl⟩ := hzH
  refine ⟨(r : G), hrV, fun hr0 => hz1 (Subtype.ext ?_), fun s hs => ?_⟩
  · exact (QuotientGroup.eq_one_iff (N := V₀.subgroupOf R) r).2 (Subgroup.mem_subgroupOf.2 hr0)
  · have hc := Subgroup.mem_center_iff.1 hzC (π ⟨s, hs⟩)
    have h1 : π (⟨s, hs⟩ * r * ⟨s, hs⟩⁻¹ * r⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := V₀.subgroupOf R) _).1 h1)

theorem uc22p22q_fixed_in_coset_odd {V₀ V : Subgroup G} {g v : G} {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVexp : ∀ w ∈ V, w ^ 2 = 1)
    (hgV : ∀ w ∈ V, g * w * g⁻¹ ∈ V) (hgV₀ : ∀ w ∈ V₀, g * w * g⁻¹ ∈ V₀) (hv : v ∈ V)
    (hgv : g * v * g⁻¹ * v⁻¹ ∈ V₀) :
    ∃ w ∈ V, g * w * g⁻¹ = w ∧ w * v⁻¹ ∈ V₀ := by
  letI : CommGroup ↥V := { (inferInstance : Group ↥V) with
    mul_comm := fun a b => Subtype.ext (hVab a a.2 b b.2) }
  let φ : Monoid.End ↥V :=
    { toFun := fun x => ⟨g * x * g⁻¹, hgV x x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp [mul_assoc] }
  have hφ : ∀ x : ↥V, ((φ x : ↥V) : G) = g * x * g⁻¹ := fun x => rfl
  have hφpow : ∀ (i : ℕ) (x : ↥V), (((φ ^ i) x : ↥V) : G) = g ^ i * x * (g ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ']
      change ((φ ((φ ^ i) x) : ↥V) : G) = _
      rw [hφ, ih x]
      group
  have hφm : ∀ x : ↥V, (φ ^ m) x = x := fun x => Subtype.ext (by rw [hφpow, hgm]; simp)
  let v₁ : ↥V := ⟨v, hv⟩
  have hmod : ∀ i : ℕ, (g ^ i * v * (g ^ i)⁻¹) * v⁻¹ ∈ V₀ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have h1 := hgV₀ _ ih
      have e : (g ^ (i + 1) * v * (g ^ (i + 1))⁻¹) * v⁻¹ =
          (g * ((g ^ i * v * (g ^ i)⁻¹) * v⁻¹) * g⁻¹) * (g * v * g⁻¹ * v⁻¹) := by group
      rw [e]
      exact V₀.mul_mem h1 hgv
  let f : ℕ → ↥V := fun i => (φ ^ i) v₁
  let N : ↥V := ∏ i ∈ Finset.range m, f i
  have hfix : φ N = N := by
    have h1 : φ N = ∏ i ∈ Finset.range m, f (i + 1) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [f]
      rw [pow_succ']
      rfl
    have h2 : (∏ i ∈ Finset.range m, f (i + 1)) * f 0 = (∏ i ∈ Finset.range m, f i) * f m := by
      rw [← Finset.prod_range_succ', Finset.prod_range_succ]
    have h3 : f m = f 0 := by
      simp only [f]
      rw [hφm]
      simp
    rw [h3] at h2
    rw [h1]
    exact mul_right_cancel h2
  have hN : N * v₁⁻¹ ∈ V₀.subgroupOf V := by
    have h1 : ∏ i ∈ Finset.range m, (f i * v₁⁻¹) ∈ V₀.subgroupOf V := by
      refine Subgroup.prod_mem _ fun i _ => ?_
      show (((f i * v₁⁻¹ : ↥V)) : G) ∈ V₀
      have e : (((f i * v₁⁻¹ : ↥V)) : G) = (g ^ i * v * (g ^ i)⁻¹) * v⁻¹ := by
        simp only [f]
        rw [Subgroup.coe_mul, hφpow, Subgroup.coe_inv]
      rw [e]
      exact hmod i
    have h2 : ∏ i ∈ Finset.range m, (f i * v₁⁻¹) = N * v₁⁻¹ ^ m := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have h3 : v₁ ^ 2 = 1 := Subtype.ext (hVexp v hv)
    have h4 : v₁ ^ m = v₁ := by
      obtain ⟨k, rfl⟩ := hm
      rw [pow_succ, pow_mul, h3, one_pow, one_mul]
    have h5 : (v₁⁻¹) ^ m = v₁⁻¹ := by
      rw [inv_pow, h4]
    rw [h2, h5] at h1
    exact h1
  exact ⟨(N : G), N.2, by rw [← hφ N, hfix], hN⟩

theorem uc22p22q_exists_fixed_involution {V : Subgroup G} {t : G} (ht : t ^ 2 = 1) (hV : IsPGroup 2 V)
    (hV1 : V ≠ ⊥) (htV : ∀ w ∈ V, t * w * t⁻¹ ∈ V) :
    ∃ w ∈ V, w ≠ 1 ∧ t * w * t⁻¹ = w := by
  classical
  haveI : Fintype ↥V := Fintype.ofFinite _
  have ht' : t * t = 1 := by rw [← sq]; exact ht
  have key : ∀ y : G, t * (t * y * t⁻¹) * t⁻¹ = y := fun y => by
    calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
      _ = y := by rw [ht']; simp
  let σ : Equiv.Perm ↥V :=
    { toFun := fun x => ⟨t * x * t⁻¹, htV x x.2⟩
      invFun := fun x => ⟨t * x * t⁻¹, htV x x.2⟩
      left_inv := fun x => Subtype.ext (key x)
      right_inv := fun x => Subtype.ext (key x) }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext x
    simp only [pow_one]
    rw [sq]
    exact key x
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) hσ
  have hcardV : Fintype.card ↥V % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hV
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hV1 (Subgroup.card_eq_one.1 (by simpa using hk))
    rw [hk]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simp [pow_succ]
  have hcard2 : 2 ≤ (σ.supportᶜ).card := by
    have h1 : (σ.supportᶜ).card % 2 = 0 := by
      have := hmod
      unfold Nat.ModEq at this
      omega
    have h2 : 0 < (σ.supportᶜ).card := by
      refine Finset.card_pos.2 ⟨1, ?_⟩
      simp [Equiv.Perm.mem_support, σ]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcard2
  have hfix : ∀ z ∈ σ.supportᶜ, (t * (z : G) * t⁻¹) = z := by
    intro z hz
    have : σ z = z := by simpa [Equiv.Perm.mem_support] using hz
    exact congrArg Subtype.val this
  by_cases hx1 : x = 1
  · refine ⟨y, y.2, fun h => hxy ?_, hfix y hy⟩
    rw [hx1]
    exact Subtype.ext h.symm
  · exact ⟨x, x.2, fun h => hx1 (Subtype.ext h), hfix x hx⟩

theorem uc22p22q_isCyclic_of_fpf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {V E : Subgroup G}
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVexp : ∀ w ∈ V, w ^ 2 = 1) (hV1 : V ≠ ⊥)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEexp : ∀ e ∈ E, e ^ p = 1)
    (hEV : ∀ e ∈ E, ∀ w ∈ V, e * w * e⁻¹ ∈ V)
    (hfpf : ∀ e ∈ E, e ≠ 1 → ∀ w ∈ V, e * w * e⁻¹ = w → w = 1) : IsCyclic ↥E := by
  by_contra hcyc
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup ↥V := { (inferInstance : Group ↥V) with
    mul_comm := fun a b => Subtype.ext (hVab a a.2 b b.2) }
  letI : CommGroup ↥E := { (inferInstance : Group ↥E) with
    mul_comm := fun a b => Subtype.ext (hEcomm a a.2 b b.2) }
  have h2 : ∀ x : Additive ↥V, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    simp only [toMul_nsmul, toMul_zero]
    exact Subtype.ext (hVexp x.toMul x.toMul.2)
  letI : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule h2
  haveI : Nontrivial (Additive ↥V) := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hV1)
    exact ⟨⟨Additive.ofMul ⟨w, hw⟩, 0, fun h => hw1 (by simpa using congrArg Additive.toMul h)⟩⟩
  let ρ : Representation (ZMod 2) ↥E (Additive ↥V) :=
    { toFun := fun e => AddMonoidHom.toZModLinearMap 2
        { toFun := fun x => Additive.ofMul ⟨e * (x.toMul : G) * e⁻¹, hEV e e.2 x.toMul x.toMul.2⟩
          map_zero' := by
            apply Additive.toMul.injective
            apply Subtype.ext
            simp
          map_add' := fun x y => by
            apply Additive.toMul.injective
            apply Subtype.ext
            simp [mul_assoc] }
      map_one' := by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        apply Subtype.ext
        simp [mul_assoc] }
  have hEp : IsPGroup p ↥E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hEexp g g.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).1 hEp
  have hcop : Nat.Coprime (Nat.card ↥E) 2 := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  obtain ⟨a, ha1, w, hw0, hρ⟩ :=
    CFSG.GroupTheory.PrimeField.noncyclic_abelian_actor_fixed_vector (p := 2) hcyc hcop ρ
  apply hw0
  have hw : ((a : G)) * (w.toMul : G) * (a : G)⁻¹ = (w.toMul : G) :=
    congrArg (fun y : Additive ↥V => ((y.toMul : ↥V) : G)) hρ
  have := hfpf (a : G) a.2 (fun h => ha1 (Subtype.ext h)) (w.toMul : G) w.toMul.2 hw
  apply Additive.toMul.injective
  exact Subtype.ext this

theorem uc22p22q_fix_of_card_lt {p : ℕ} (hp : p.Prime) {W : Subgroup G} {x : G} (hx : x ^ p = 1)
    (hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W) (hW : Nat.card W < p) : ∀ w ∈ W, x * w * x⁻¹ = w := by
  classical
  haveI : Fintype ↥W := Fintype.ofFinite _
  haveI : Fact p.Prime := ⟨hp⟩
  let σ : Equiv.Perm ↥W := Equiv.ofBijective (fun w : ↥W => (⟨x * w * x⁻¹, hxW w w.2⟩ : ↥W))
    (Finite.injective_iff_bijective.1 (fun a b h => Subtype.ext (by
      have := congrArg Subtype.val h
      simpa using this)))
  have hσ : ∀ (k : ℕ) (w : ↥W), (((σ ^ k) w : ↥W) : G) = x ^ k * w * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ', Equiv.Perm.mul_apply]
      change x * (((σ ^ k) w : ↥W) : G) * x⁻¹ = _
      rw [ih w]
      group
  have hσp : σ ^ p ^ 1 = 1 := by
    ext w
    rw [pow_one, hσ p w, hx]
    simp
  have hmod := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) hσp
  unfold Nat.ModEq at hmod
  have hcardW : Fintype.card ↥W < p := by rwa [← Nat.card_eq_fintype_card]
  have hle : (σ.supportᶜ).card ≤ Fintype.card ↥W := Finset.card_le_univ _
  have heq : (σ.supportᶜ).card = Fintype.card ↥W := by
    rw [Nat.mod_eq_of_lt (hle.trans_lt hcardW), Nat.mod_eq_of_lt hcardW] at hmod
    exact hmod
  have huniv : σ.supportᶜ = Finset.univ := Finset.eq_univ_of_card _ heq
  intro w hw
  have : σ ⟨w, hw⟩ = ⟨w, hw⟩ := by
    have hmem : (⟨w, hw⟩ : ↥W) ∈ σ.supportᶜ := by rw [huniv]; exact Finset.mem_univ _
    simpa [Equiv.Perm.mem_support] using hmem
  exact congrArg Subtype.val this

end CFSG.LocalAnalysis.UniquenessCase.UC22
