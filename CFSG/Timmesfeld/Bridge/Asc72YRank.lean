module

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

namespace CFSG.Timmesfeld.Bridge.Asc72

namespace YRank

variable {G : Type*} [Group G]

@[expose] def rSub (L : Set G) (z : G) (hz : z * z = 1) (hL : ∀ d ∈ L, d * d = 1)
    (hLz : ∀ d ∈ L, Commute d z) (hmul : ∀ d ∈ L, ∀ e ∈ L, d ≠ e → d * e * z ∈ L) :
    Subgroup G where
  carrier := {x | x = 1 ∨ x * z ∈ L}
  mul_mem' := by
    intro x y hx hy
    rcases hx with rfl | hx
    · rwa [one_mul]
    rcases hy with rfl | hy
    · rw [mul_one]
      exact Or.inr hx
    have hxz : x = x * z * z := by rw [mul_assoc, hz, mul_one]
    have hyz : y = y * z * z := by rw [mul_assoc, hz, mul_one]
    by_cases hde : x * z = y * z
    · left
      have hxy : x = y := mul_right_cancel hde
      rw [← hxy, hxz, show x * z * z * (x * z * z) = x * z * (z * (x * z)) * z by group,
        ← (hLz _ hx).eq, show x * z * (x * z * z) * z = (x * z) * (x * z) * (z * z) by group,
        hL _ hx, hz, one_mul]
    · right
      have h := hmul _ hx _ hy hde
      have e1 : x * y * z = x * z * (y * z) * z := by
        calc x * y * z = (x * z * z) * (y * z * z) * z := by rw [← hxz, ← hyz]
          _ = (x * z) * (z * (y * z)) * (z * z) := by group
          _ = (x * z) * (y * z * z) * (z * z) := by rw [← (hLz _ hy).eq]
          _ = x * z * (y * z) * z := by rw [hz, mul_one]; group
      rw [e1]
      exact h
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro x hx
    rcases hx with rfl | hx
    · left
      exact inv_one
    · right
      have hxx : x * x = 1 := by
        calc x * x = x * z * (z * x) := by rw [mul_assoc x z, ← mul_assoc z, hz, one_mul]
          _ = x * z * (x * z) := by
            have h := (hLz _ hx).eq
            rw [show z * x = z * (x * z) * z by rw [mul_assoc, mul_assoc, hz, mul_one], ← h,
              show x * z * z * z = x * (z * z) * z by group, hz, mul_one]
          _ = 1 := hL _ hx
      rw [inv_eq_of_mul_eq_one_right hxx]
      exact hx

variable {L : Set G} {z : G} {hz : z * z = 1} {hL : ∀ d ∈ L, d * d = 1}
  {hLz : ∀ d ∈ L, Commute d z} {hmul : ∀ d ∈ L, ∀ e ∈ L, d ≠ e → d * e * z ∈ L}

theorem commute_of_mem_rSub (hLL : ∀ d ∈ L, ∀ e ∈ L, Commute d e) {x y : G}
    (hx : x ∈ rSub L z hz hL hLz hmul) (hy : y ∈ rSub L z hz hL hLz hmul) : Commute x y := by
  rcases hx with rfl | hx
  · exact Commute.one_left y
  rcases hy with rfl | hy
  · exact Commute.one_right x
  have hxz : x = x * z * z := by rw [mul_assoc, hz, mul_one]
  have hyz : y = y * z * z := by rw [mul_assoc, hz, mul_one]
  rw [hxz, hyz]
  have h1 : Commute (x * z) (y * z) := hLL _ hx _ hy
  have h2 : Commute (x * z) z := hLz _ hx
  have h3 : Commute (y * z) z := hLz _ hy
  exact (h1.mul_right h2.symm.symm).mul_left ((h3.symm.mul_right (Commute.refl z)))

theorem mul_self_of_mem_rSub {x : G} (hx : x ∈ rSub L z hz hL hLz hmul) : x * x = 1 := by
  have hx' := (rSub L z hz hL hLz hmul).inv_mem hx
  rcases hx with rfl | hx
  · exact one_mul 1
  · have h := (hLz _ hx).eq
    calc x * x = x * z * (z * x) := by rw [mul_assoc x z, ← mul_assoc z, hz, one_mul]
      _ = x * z * (x * z) := by
        rw [show z * x = z * (x * z) * z by rw [mul_assoc, mul_assoc, hz, mul_one], ← h,
          show x * z * z * z = x * (z * z) * z by group, hz, mul_one]
      _ = 1 := hL _ hx

theorem ncard_add_one_le [Finite G] (hzL : z ∉ L) :
    L.ncard + 1 ≤ ((rSub L z hz hL hLz hmul : Subgroup G) : Set G).ncard := by
  have hinj : Function.Injective (fun d : G => d * z) := fun d e h => mul_right_cancel h
  have h1 : (1 : G) ∉ (fun d : G => d * z) '' L := by
    rintro ⟨d, hd, hdz⟩
    have : d = z := by
      calc d = d * z * z := by rw [mul_assoc, hz, mul_one]
        _ = z := by rw [show d * z = 1 from hdz, one_mul]
    exact hzL (this ▸ hd)
  have hsub : insert (1 : G) ((fun d : G => d * z) '' L) ⊆
      ((rSub L z hz hL hLz hmul : Subgroup G) : Set G) := by
    rintro x (rfl | ⟨d, hd, rfl⟩)
    · exact Or.inl rfl
    · right
      show d * z * z ∈ L
      rwa [mul_assoc, hz, mul_one]
  calc L.ncard + 1 = (insert (1 : G) ((fun d : G => d * z) '' L)).ncard := by
        rw [Set.ncard_insert_of_notMem h1 (Set.toFinite _), Set.ncard_image_of_injective _ hinj]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem exists_two_commute [Finite G] (L : Set G) {z a : G} (hz : z * z = 1)
    (hL : ∀ d ∈ L, d * d = 1) (hLz : ∀ d ∈ L, Commute d z) (hLL : ∀ d ∈ L, ∀ e ∈ L, Commute d e)
    (hmul : ∀ d ∈ L, ∀ e ∈ L, d ≠ e → d * e * z ∈ L) (hzL : z ∉ L) (ha : a * a = 1)
    (haz : Commute a z) (haL : ∀ d ∈ L, a * d * a⁻¹ ∈ L) (h4 : 4 ≤ L.ncard) :
    ∃ d ∈ L, ∃ e ∈ L, d ≠ e ∧ Commute a d ∧ Commute a e := by
  set R := rSub L z hz hL hLz hmul with hRdef
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have haR : ∀ x ∈ R, a * x * a⁻¹ ∈ R := by
    intro x hx
    rcases hx with rfl | hx
    · left
      group
    · right
      have h := haL _ hx
      rwa [show a * (x * z) * a⁻¹ = a * x * a⁻¹ * (a * z * a⁻¹) by group, haz.eq,
        mul_inv_cancel_right] at h
  have hRc : ∀ x ∈ R, ∀ y ∈ R, Commute x y := fun x hx y hy => commute_of_mem_rSub hLL hx hy
  let φ : R →* R :=
    { toFun := fun x => x * ⟨a * x * a⁻¹, haR x x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hc := hRc _ y.2 _ (haR x x.2)
        calc (x : G) * y * (a * (x * y) * a⁻¹)
            = x * (y * (a * x * a⁻¹)) * (a * y * a⁻¹) := by group
          _ = x * ((a * x * a⁻¹) * y) * (a * y * a⁻¹) := by rw [hc.eq]
          _ = x * (a * x * a⁻¹) * (y * (a * y * a⁻¹)) := by group }
  have hφ : ∀ x : R, ((φ x : R) : G) = x * (a * x * a⁻¹) := fun x => rfl
  have hker : ∀ x : R, x ∈ φ.ker → Commute a (x : G) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (x : G) * (a * x * a⁻¹) = 1 := by
      have := congrArg Subtype.val hx
      rwa [hφ] at this
    have hxx : (x : G) * x = 1 := mul_self_of_mem_rSub x.2
    have h2 : a * x * a⁻¹ = x := by
      calc a * x * a⁻¹ = (x : G) * x * (a * x * a⁻¹) := by rw [hxx, one_mul]
        _ = x := by rw [mul_assoc, h1, mul_one]
    show a * x = x * a
    calc a * (x : G) = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h2]
  have hrange : φ.range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hφ, hφ, OneMemClass.coe_one]
    have hc := hRc _ x.2 _ (haR x x.2)
    have hxx : (x : G) * x = 1 := mul_self_of_mem_rSub x.2
    have hyy : (a * x * a⁻¹) * (a * x * a⁻¹) = 1 := by
      rw [show a * x * a⁻¹ * (a * x * a⁻¹) = a * ((x : G) * x) * a⁻¹ by group, hxx, mul_one,
        mul_inv_cancel]
    have e1 : a * ((x : G) * (a * x * a⁻¹)) * a⁻¹ = (a * x * a⁻¹) * x := by
      calc a * ((x : G) * (a * x * a⁻¹)) * a⁻¹ = a * x * a⁻¹ * (a * a * x * (a⁻¹ * a⁻¹)) := by
            group
        _ = (a * x * a⁻¹) * x := by rw [ha, hainv, ha, one_mul, mul_one]
    rw [e1, ← hc.eq]
    calc (x : G) * (a * x * a⁻¹) * (x * (a * x * a⁻¹))
        = x * (a * x * a⁻¹) * ((a * x * a⁻¹) * x) := by rw [hc.eq]
      _ = x * ((a * x * a⁻¹) * (a * x * a⁻¹)) * x := by group
      _ = 1 := by rw [hyy, mul_one, hxx]
  have hcardR : Nat.card R = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hle1 : Nat.card φ.range ≤ Nat.card φ.ker := Subgroup.card_le_of_le hrange
  have hle2 : L.ncard + 1 ≤ Nat.card R := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact ncard_add_one_le hzL
  have h3 : 3 ≤ Nat.card φ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card R ≤ 2 * 2 := by
      rw [hcardR]
      exact Nat.mul_le_mul (hle1.trans (by omega)) (by omega)
    omega
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq] at h3
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp (by omega : 2 < ((φ.ker : Subgroup R) : Set R).ncard)
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁1, hr₂1, hr12⟩ : ∃ r₁ r₂ : R, r₁ ∈ φ.ker ∧ r₂ ∈ φ.ker ∧ r₁ ≠ 1 ∧
      r₂ ≠ 1 ∧ r₁ ≠ r₂ := by
    by_cases hx₁ : x₁ = 1
    · subst hx₁
      exact ⟨x₂, x₃, h₂, h₃, Ne.symm h12, Ne.symm h13, h23⟩
    by_cases hx₂ : x₂ = 1
    · subst hx₂
      exact ⟨x₁, x₃, h₁, h₃, hx₁, Ne.symm h23, h13⟩
    · exact ⟨x₁, x₂, h₁, h₂, hx₁, hx₂, h12⟩
  have hmemL : ∀ r : R, r ≠ 1 → (r : G) * z ∈ L := by
    intro r hr
    rcases r.2 with h | h
    · exact absurd (Subtype.ext h) hr
    · exact h
  refine ⟨r₁ * z, hmemL r₁ hr₁1, r₂ * z, hmemL r₂ hr₂1, fun h => hr12 (Subtype.ext
    (mul_right_cancel h)), (hker r₁ hr₁).mul_right haz, (hker r₂ hr₂).mul_right haz⟩

end YRank

end CFSG.Timmesfeld.Bridge.Asc72
