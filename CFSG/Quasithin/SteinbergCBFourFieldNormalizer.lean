module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SteinbergCB

open Module Subgroup

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [Module (ZMod 2) V]

@[expose] def restrictTwoHom : (V ≃ₗ[k] V) →* (V ≃ₗ[ZMod 2] V) where
  toFun g := { g.toAddEquiv with map_smul' := fun c x => ZMod.map_smul g.toAddEquiv c x }
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem restrictTwoHom_injective : Function.Injective (restrictTwoHom (k := k) (V := V)) :=
  fun g h hgh => LinearEquiv.ext fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hgh
    exact this

variable (k V) in
@[expose] def specialLinearTwo : Subgroup (V ≃ₗ[ZMod 2] V) :=
  ((restrictTwoHom (k := k) (V := V)).comp SpecialLinearGroup.toLinearEquiv).range

theorem smul_comm_of_mem_specialLinearTwo {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ specialLinearTwo k V)
    (a : k) (w : V) : s (a • w) = a • s w := by
  obtain ⟨u, rfl⟩ := hs
  exact (u : V ≃ₗ[k] V).map_smul a w

@[expose] def scalarTwo (a : k) : V →ₗ[ZMod 2] V :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun v => a • v, map_zero' := smul_zero a, map_add' := smul_add a }

theorem scalarTwo_apply (a : k) (v : V) : scalarTwo a v = a • v :=
  rfl

theorem exists_smul_of_commute_specialLinear [FiniteDimensional k V] (hV : finrank k V = 2)
    {A : V →ₗ[ZMod 2] V}
    (hA : ∀ g : V ≃ₗ[k] V, LinearEquiv.det g = 1 → ∀ v, A (g v) = g (A v)) :
    ∃ a : k, ∀ v, A v = a • v := by
  let b := Module.finBasisOfFinrankEq k V hV
  have key : ∀ i j : Fin 2, i ≠ j → ∀ t : k,
      A (t • b j) = (b.coord i (A (b i)) * t) • b j := by
    intro i j hij t
    have h0 : b.coord i (t • b j) = 0 := by
      rw [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hij, smul_zero]
    have h := hA (LinearEquiv.transvection h0) (LinearEquiv.transvection.det_eq_one h0) (b i)
    have hc : b.coord i (b i) = 1 := by
      rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]
    rw [LinearEquiv.transvection.apply, LinearEquiv.transvection.apply, map_add, hc,
      one_smul] at h
    rw [mul_smul]
    exact add_left_cancel h
  set l := b.coord 0 (A (b 0)) with hl
  set m := b.coord 1 (A (b 1)) with hm
  have h01 : ∀ t : k, A (t • b 1) = (l * t) • b 1 := key 0 1 (by decide)
  have h10 : ∀ t : k, A (t • b 0) = (m * t) • b 0 := key 1 0 (by decide)
  have hlm : l = m := by
    have h := h10 1
    rw [one_smul, mul_one] at h
    rw [hl, h, map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul,
      mul_one]
  refine ⟨l, fun v => ?_⟩
  have hv : v = b.repr v 0 • b 0 + b.repr v 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two]
  rw [hv, map_add, h10, h01, ← hlm, smul_add, mul_smul, mul_smul]

theorem commute_specialLinearTwo_iff [FiniteDimensional k V] (hV : finrank k V = 2)
    (A : V →ₗ[ZMod 2] V) :
    (∀ s ∈ specialLinearTwo k V, ∀ v, A (s v) = s (A v)) ↔ ∃ a : k, ∀ v, A v = a • v := by
  constructor
  · intro hA
    refine exists_smul_of_commute_specialLinear hV fun g hg v => ?_
    exact hA (restrictTwoHom (SpecialLinearGroup.toLinearEquiv ⟨g, hg⟩)) ⟨⟨g, hg⟩, rfl⟩ v
  · rintro ⟨a, ha⟩ s hs v
    rw [ha, ha, smul_comm_of_mem_specialLinearTwo hs]

theorem exists_smul_of_mem_normalizer [FiniteDimensional k V] (hV : finrank k V = 2)
    {n : V ≃ₗ[ZMod 2] V}
    (hn : n ∈ normalizer (specialLinearTwo k V : Set (V ≃ₗ[ZMod 2] V))) (a : k) :
    ∃ c : k, ∀ w, n (a • w) = c • n w := by
  set M : V →ₗ[ZMod 2] V :=
    (n : V →ₗ[ZMod 2] V) ∘ₗ scalarTwo a ∘ₗ (n.symm : V →ₗ[ZMod 2] V) with hM
  obtain ⟨c, hc⟩ := (commute_specialLinearTwo_iff hV M).1 fun s hs v => by
    have hs' : n⁻¹ * s * n ∈ specialLinearTwo k V := by
      have := (mem_normalizer_iff.1 (inv_mem hn) s).1 hs
      rwa [inv_inv] at this
    have h1 : n.symm (s v) = (n⁻¹ * s * n) (n.symm v) := by
      change n.symm (s v) = n.symm (s (n (n.symm v)))
      rw [LinearEquiv.apply_symm_apply]
    have h2 : n ((n⁻¹ * s * n) (a • n.symm v)) = s (n (a • n.symm v)) := by
      change n (n.symm (s (n (a • n.symm v)))) = s (n (a • n.symm v))
      rw [LinearEquiv.apply_symm_apply]
    simp only [hM, LinearMap.comp_apply, LinearEquiv.coe_coe, scalarTwo_apply]
    rw [h1, ← smul_comm_of_mem_specialLinearTwo hs', h2]
  refine ⟨c, fun w => ?_⟩
  have := hc (n w)
  simp only [hM, LinearMap.comp_apply, LinearEquiv.coe_coe, scalarTwo_apply,
    LinearEquiv.symm_apply_apply] at this
  exact this

omit [Field k] in
theorem field_four_two [Field k] [Fintype k] (hk : Fintype.card k = 4) : (1 + 1 : k) = 0 := by
  have h := FiniteField.cast_card_eq_zero k
  rw [hk] at h
  have h4 : ((4 : ℕ) : k) = (1 + 1) * (1 + 1) := by norm_num
  rw [h4] at h
  exact mul_self_eq_zero.1 h

omit [Field k] in
theorem field_four_omega [Field k] [Fintype k] (hk : Fintype.card k = 4) :
    ∃ ω : k, ω * ω = ω + 1 ∧ ∀ a : k, a = 0 ∨ a = 1 ∨ a = ω ∨ a = ω + 1 := by
  classical
  have h2 := field_four_two hk
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : k, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := fun a _ => by
      by_cases ha : a = 0
      · simp [ha]
      · simp [h a ha]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hk] at h1
    have h3 : ({0, 1} : Finset k).card ≤ 2 := Finset.card_le_two
    omega
  have h3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hk] at this
  have hq : ω * ω + ω + 1 = 0 := by
    have hne : ω - 1 ≠ 0 := sub_ne_zero.2 hω1
    have : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.1 this).resolve_left hne
  have hsq : ω * ω = ω + 1 := by linear_combination hq - (ω + 1) * h2
  refine ⟨ω, hsq, fun a => ?_⟩
  have hd1 : ω + 1 ≠ 0 := fun h => hω1 (by linear_combination h - h2)
  have hd2 : ω + 1 ≠ 1 := fun h => hω0 (by linear_combination h)
  have hd3 : ω ≠ ω + 1 := fun h => one_ne_zero (by linear_combination -h)
  have hcard : ({0, 1, ω, ω + 1} : Finset k).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hd3]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hω1.symm, hd2.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨zero_ne_one, hω0.symm, hd1.symm⟩
  have huniv := Finset.eq_univ_of_card _ (hcard.trans hk.symm)
  have ha : a ∈ ({0, 1, ω, ω + 1} : Finset k) := huniv ▸ Finset.mem_univ a
  simpa using ha

theorem nq_natural_four_field_normalizer_bound [Fintype k] (hk : Fintype.card k = 4)
    (hV : finrank k V = 2) :
    (∀ A : V →ₗ[ZMod 2] V, (∀ s ∈ specialLinearTwo k V, ∀ v, A (s v) = s (A v)) ↔
      ∃ a : k, ∀ v, A v = a • v) ∧
    Nat.card (normalizer (specialLinearTwo k V : Set (V ≃ₗ[ZMod 2] V))) ∣ 360 ∧
    ((specialLinearTwo k V).subgroupOf
      (normalizer (specialLinearTwo k V : Set (V ≃ₗ[ZMod 2] V)))).index ∣ 6 ∧
    ¬ 4 ∣ ((specialLinearTwo k V).subgroupOf
      (normalizer (specialLinearTwo k V : Set (V ≃ₗ[ZMod 2] V)))).index := by
  classical
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have : Finite V := Module.finite_of_finite k
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) DFunLike.coe_injective
  set S := specialLinearTwo k V with hS
  set N := normalizer (S : Set (V ≃ₗ[ZMod 2] V)) with hN
  let b := Module.finBasisOfFinrankEq k V hV
  have hGL : Nat.card (V ≃ₗ[k] V) = 180 := by
    rw [← Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V)).toEquiv, Matrix.card_GL_field, hk,
      Fin.prod_univ_two]
    rfl
  have hScard : Nat.card S = 60 := by
    have hinj : Function.Injective
        ((restrictTwoHom (k := k) (V := V)).comp SpecialLinearGroup.toLinearEquiv) :=
      restrictTwoHom_injective.comp SpecialLinearGroup.toLinearEquiv_injective
    rw [hS, specialLinearTwo, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      ← Nat.card_congr (Matrix.SpecialLinearGroup.toLin_equiv b).toEquiv,
      Matrix.card_SL_field, hk, Fin.prod_univ_two]
    rfl
  obtain ⟨ω, hωω, hall⟩ := field_four_omega hk
  have h2 := field_four_two hk
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
  have hne : ∀ n : V ≃ₗ[ZMod 2] V, n w₀ ≠ 0 := fun n h =>
    hw₀ (n.injective (h.trans (map_zero n).symm))
  have hsplit : ∀ w : V, (ω + 1) • w = ω • w + w := fun w => by rw [add_smul, one_smul]
  have hcase : ∀ n ∈ N, (∀ w, n (ω • w) = ω • n w) ∨ (∀ w, n (ω • w) = (ω + 1) • n w) := by
    intro n hn
    obtain ⟨c, hc⟩ := exists_smul_of_mem_normalizer hV hn ω
    have hcc : c * c = c + 1 := by
      have h1 := hc (ω • w₀)
      rw [hc w₀, smul_smul, smul_smul, hωω, hsplit, map_add, hc w₀] at h1
      apply smul_left_injective k (hne n)
      simp only
      rw [add_smul, one_smul]
      exact h1.symm
    rcases hall c with rfl | rfl | rfl | rfl
    · simp at hcc
    · simp at hcc
    · exact Or.inl hc
    · exact Or.inr hc
  have hexcl : ∀ n : V ≃ₗ[ZMod 2] V, (∀ w, n (ω • w) = ω • n w) →
      ¬ ∀ w, n (ω • w) = (ω + 1) • n w := fun n h1 h1' => by
    have h3 := smul_left_injective k (hne n) ((h1 w₀).symm.trans (h1' w₀))
    exact one_ne_zero (α := k) (by linear_combination -h3)
  set P : (V ≃ₗ[ZMod 2] V) → Prop := fun n => ∀ w, n (ω • w) = ω • n w with hP
  set Q : (V ≃ₗ[ZMod 2] V) → Prop := fun n => ∀ w, n (ω • w) = (ω + 1) • n w with hQ
  have hPP : ∀ n m, P n → P m → P (n * m) := fun n m hn hm w => by
    rw [LinearEquiv.mul_apply, hm, hn, LinearEquiv.mul_apply]
  have hPQ : ∀ n m, P n → Q m → Q (n * m) := fun n m hn hm w => by
    rw [LinearEquiv.mul_apply, hm, hsplit, map_add, hn, LinearEquiv.mul_apply, hsplit]
  have hQP : ∀ n m, Q n → P m → Q (n * m) := fun n m hn hm w => by
    rw [LinearEquiv.mul_apply, hm, hn, LinearEquiv.mul_apply]
  have hvv : ∀ x : V, x + x = 0 := fun x => by
    calc x + x = (1 + 1 : k) • x := by rw [add_smul, one_smul]
      _ = 0 := by rw [h2, zero_smul]
  have hQQ : ∀ n m, Q n → Q m → P (n * m) := fun n m hn hm w => by
    rw [LinearEquiv.mul_apply, hm, hsplit, map_add, hn, LinearEquiv.mul_apply, hsplit, add_assoc,
      hvv, add_zero]
  let χ : N →* Multiplicative (ZMod 2) :=
    MonoidHom.mk' (fun n => if P n.1 then 1 else Multiplicative.ofAdd 1) fun n m => by
      have hof : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
      change (if P (n.1 * m.1) then (1 : Multiplicative (ZMod 2)) else Multiplicative.ofAdd 1) =
        (if P n.1 then 1 else Multiplicative.ofAdd 1) *
          (if P m.1 then 1 else Multiplicative.ofAdd 1)
      rcases hcase n.1 n.2 with hn | hn <;> rcases hcase m.1 m.2 with hm | hm
      · rw [ite_eq_left (hPP _ _ hn hm), ite_eq_left hn, ite_eq_left hm, one_mul]
      · rw [ite_eq_right (hexcl _ · (hPQ _ _ hn hm)), ite_eq_left hn,
          ite_eq_right (hexcl _ · hm), one_mul]
      · rw [ite_eq_right (hexcl _ · (hQP _ _ hn hm)), ite_eq_right (hexcl _ · hn),
          ite_eq_left hm, mul_one]
      · rw [ite_eq_left (hQQ _ _ hn hm), ite_eq_right (hexcl _ · hn),
          ite_eq_right (hexcl _ · hm), hof]
  have hklin : ∀ n : V ≃ₗ[ZMod 2] V, P n → ∀ (a : k) (w : V), n (a • w) = a • n w := by
    intro n hn a w
    rcases hall a with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact hn w
    · rw [hsplit, map_add, hn, hsplit]
  have hker_le : (χ.ker).map N.subtype ≤ (restrictTwoHom (k := k) (V := V)).range := by
    rintro _ ⟨n, hn, rfl⟩
    have hPn : P n.1 := by
      by_contra hc
      have h := (MonoidHom.mem_ker).1 hn
      change (if P n.1 then 1 else Multiplicative.ofAdd (1 : ZMod 2)) = 1 at h
      rw [ite_eq_right hc] at h
      exact absurd h (by decide)
    exact ⟨{ n.1.toAddEquiv with map_smul' := fun a w => hklin n.1 hPn a w },
      LinearEquiv.ext fun _ => rfl⟩
  have hkercard : Nat.card χ.ker ∣ 180 := by
    rw [← hGL, Nat.card_congr (MonoidHom.ofInjective restrictTwoHom_injective).toEquiv,
      ← card_map_of_injective N.subtype_injective]
    exact card_dvd_of_le hker_le
  have hNcard : Nat.card N ∣ 360 := by
    have h1 := card_mul_index χ.ker
    rw [index_ker] at h1
    have h3 : Nat.card χ.range ∣ 2 := by
      have hC2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
        rw [Nat.card_eq_fintype_card]
        rfl
      have := Subgroup.card_subgroup_dvd_card χ.range
      rwa [hC2] at this
    rw [← h1]
    exact Nat.mul_dvd_mul hkercard h3
  have hSN : S ≤ N := le_normalizer
  have hidx : Nat.card S * (S.subgroupOf N).index = Nat.card N := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv, card_mul_index]
  have hidx6 : (S.subgroupOf N).index ∣ 6 := by
    rw [hScard] at hidx
    have h3 : 60 * (S.subgroupOf N).index ∣ 60 * 6 := hidx ▸ hNcard
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  refine ⟨commute_specialLinearTwo_iff hV, hNcard, hidx6, fun h4 => ?_⟩
  have := Nat.dvd_trans h4 hidx6
  norm_num at this

end CFSG.Quasithin.SteinbergCB
