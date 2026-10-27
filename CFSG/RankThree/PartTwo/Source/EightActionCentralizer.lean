module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.RankThree.PartTwo.EightActionSmallFixedSpace
import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.PartTwo.Source

open CFSG.RankThree.LocalRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem commute_on_finrank_le_one {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {W : Submodule K V} (hW : Module.finrank K W ≤ 1)
    {f g : Module.End K V} (hf : ∀ w ∈ W, f w ∈ W) (hg : ∀ w ∈ W, g w ∈ W) :
    ∀ w ∈ W, f (g w) = g (f w) := by
  intro w hw
  by_cases hw0 : w = 0
  · rw [hw0, map_zero, map_zero, map_zero]
  have hspan : K ∙ w = W := by
    apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem w W).mpr hw)
    rw [finrank_span_singleton hw0]
    exact hW
  have hscal : ∀ u ∈ W, ∃ c : K, u = c • w := by
    intro u hu
    rw [← hspan] at hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨c, rfl⟩
  obtain ⟨a, ha⟩ := hscal _ (hf w hw)
  obtain ⟨b, hb⟩ := hscal _ (hg w hw)
  rw [hb, map_smul, ha, map_smul, hb, smul_smul, smul_smul, mul_comm]

theorem commute_of_eight_action {G : Type*} [Group G] [Finite G] {r : ℕ} [hr : Fact r.Prime]
    (hr2 : r ≠ 2) {Y F K : Subgroup G} (hYc : IsMulCommutative Y) (hYr : ∀ y ∈ Y, y ^ r = 1)
    (hFc : IsMulCommutative F) (hF2 : ∀ t ∈ F, t ^ 2 = 1) (hF8 : Nat.card F = 8)
    (hFY : F ≤ Subgroup.normalizer (Y : Set G))
    (hFfaith : F ⊓ Subgroup.centralizer (Y : Set G) = ⊥)
    (hfix : ∀ t ∈ F, t ≠ 1 → Nat.card (Y ⊓ Subgroup.centralizer {t} : Subgroup G) ≤ r ^ 2)
    (hKY : K ≤ Subgroup.normalizer (Y : Set G)) (hKF : K ≤ Subgroup.centralizer (F : Set G))
    (hKfaith : K ⊓ Subgroup.centralizer (Y : Set G) = ⊥) :
    ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k := by
  classical
  have hr' : r.Prime := hr.out
  have hYelem : CFSG.IsElementaryAbelian r Y :=
    { toIsMulCommutative := hYc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hYr _ y.2) }
  have hFelem : CFSG.IsElementaryAbelian 2 F :=
    { toIsMulCommutative := hFc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun t =>
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hF2 _ t.2) }
  have : Finite (Additive Y) := inferInstanceAs (Finite Y)
  have : FiniteDimensional (ZMod r) (Additive Y) := Module.Finite.of_finite
  let E : MulAut Y →* Module.End (ZMod r) (Additive Y) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap r
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  let conj : ∀ g : G, g ∈ Subgroup.normalizer (Y : Set G) → Module.End (ZMod r) (Additive Y) :=
    fun g hg => E (Y.normalizerMonoidHom ⟨g, hg⟩)
  have hconj : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G)) (v : Additive Y),
      ((Additive.toMul (conj g hg v) : Y) : G) = g * (Additive.toMul v : Y) * g⁻¹ :=
    fun _ _ _ => rfl
  let ρF : Representation (ZMod r) F (Additive Y) :=
    E.comp (Y.normalizerMonoidHom.comp (Subgroup.inclusion hFY))
  have hρF : ∀ (t : F) (v : Additive Y), ρF t v = conj t (hFY t.2) v := fun _ _ => rfl
  have h2 : (2 : ZMod r) ≠ 0 := CFSG.RankThree.PartTwo.two_ne_zero_zmod hr' hr2
  have hinj : Function.Injective ρF := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have htC : (t : G) ∈ F ⊓ Subgroup.centralizer (Y : Set G) := by
      refine ⟨t.2, ?_⟩
      show (t : G) ∈ Subgroup.centralizer (Y : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg (fun f : Module.End (ZMod r) (Additive Y) =>
        ((Additive.toMul (f (Additive.ofMul ⟨y, hy⟩)) : Y) : G)) ht
      simp only [hρF, hconj, Module.End.one_apply, toMul_ofMul] at h
      calc y * (t : G) = (t : G) * y * (t : G)⁻¹ * t := by rw [h]
        _ = t * y := by group
    rw [hFfaith, Subgroup.mem_bot] at htC
    exact Subtype.ext htC
  have hfixV : ∀ t : F, t ≠ 1 →
      Module.finrank (ZMod r) (Module.End.eigenspace (ρF t) 1) ≤ 2 := by
    intro t ht
    have ht' : (t : G) ≠ 1 := fun h => ht (Subtype.ext h)
    have hcard : Nat.card (Module.End.eigenspace (ρF t) 1) ≤ r ^ 2 := by
      refine le_trans (Nat.card_le_card_of_injective
        (β := (Y ⊓ Subgroup.centralizer {(t : G)} : Subgroup G))
        (fun v => ⟨((Additive.toMul (v : Additive Y) : Y) : G),
          (Additive.toMul (v : Additive Y)).2, ?_⟩) ?_) (hfix t t.2 ht')
      · have hv := v.2
        rw [Module.End.mem_eigenspace_iff, one_smul] at hv
        have h := congrArg (fun w : Additive Y => ((Additive.toMul w : Y) : G)) hv
        rw [hρF, hconj] at h
        show ((Additive.toMul (v : Additive Y) : Y) : G) ∈ Subgroup.centralizer {(t : G)}
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc ((Additive.toMul (v : Additive Y) : Y) : G) * (t : G) =
            (t : G) * (Additive.toMul (v : Additive Y) : Y) * (t : G)⁻¹ * t := by rw [h]
          _ = t * (Additive.toMul (v : Additive Y) : Y) := by group
      · intro v w h
        apply Subtype.ext
        have h' := congrArg Subtype.val h
        exact Additive.toMul.injective (Subtype.ext h')
    have : Fintype (Module.End.eigenspace (ρF t) 1) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod r) (V := Module.End.eigenspace (ρF t) 1)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    rw [hpow] at hcard
    exact (Nat.pow_le_pow_iff_right hr'.one_lt).mp hcard
  obtain ⟨χ, -, -, hone, hweights, hσ1, -, -, -⟩ :=
    CFSG.RankThree.PartTwo.eight_action_small_fixed_space hF8 h2 ρF hinj hfixV
  have hle1 : ∀ ψ, Module.finrank (ZMod r) (signWeightSpace ρF ψ) ≤ 1 := by
    intro ψ
    by_cases hψ : signWeightSpace ρF ψ = ⊥
    · rw [hψ, finrank_bot]
      exact zero_le_one
    rcases hweights ψ hψ with ⟨i, rfl⟩ | rfl
    · exact (hone i).le
    · exact hσ1
  have hcommFK : ∀ (t : F) (k : G) (hk : k ∈ K) (v : Additive Y),
      ρF t (conj k (hKY hk) v) = conj k (hKY hk) (ρF t v) := by
    intro t k hk v
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [hρF, hconj]
    have htk : (t : G) * k = k * t := Subgroup.mem_centralizer_iff.mp (hKF hk) t t.2
    calc (t : G) * (k * (Additive.toMul v : Y) * k⁻¹) * (t : G)⁻¹ =
        ((t : G) * k) * (Additive.toMul v : Y) * ((t : G) * k)⁻¹ := by group
      _ = (k * t) * (Additive.toMul v : Y) * (k * t)⁻¹ := by rw [htk]
      _ = k * ((t : G) * (Additive.toMul v : Y) * (t : G)⁻¹) * k⁻¹ := by group
  have hpres : ∀ (ψ) (k : G) (hk : k ∈ K), ∀ v ∈ signWeightSpace ρF ψ,
      conj k (hKY hk) v ∈ signWeightSpace ρF ψ := by
    intro ψ k hk v hv
    rw [mem_signWeightSpace] at hv ⊢
    intro a
    rw [hcommFK a k hk v, hv a, map_smul]
  let := Fintype.ofFinite F
  have : Finite (Module.Dual (ZMod 2) (Additive F)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive F) => (f : Additive F → ZMod 2))
      DFunLike.coe_injective
  let := Fintype.ofFinite (Module.Dual (ZMod 2) (Additive F))
  have hcommV : ∀ (k : G) (hk : k ∈ K) (k' : G) (hk' : k' ∈ K) (v : Additive Y),
      conj k (hKY hk) (conj k' (hKY hk') v) = conj k' (hKY hk') (conj k (hKY hk) v) := by
    intro k hk k' hk' v
    have hv : v ∈ ⨆ ψ, signWeightSpace ρF ψ := by
      rw [iSup_signWeightSpace_eq_top ρF h2]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (signWeightSpace ρF)
      (motive := fun w => conj k (hKY hk) (conj k' (hKY hk') w) =
        conj k' (hKY hk') (conj k (hKY hk) w)) hv
      (fun ψ w hw => commute_on_finrank_le_one (hle1 ψ) (hpres ψ k hk) (hpres ψ k' hk') w hw)
      (by simp only [map_zero]) (fun x y hx hy => by simp only [map_add, hx, hy])
  intro k hk k' hk'
  have hc : k⁻¹ * k'⁻¹ * k * k' ∈ K ⊓ Subgroup.centralizer (Y : Set G) := by
    refine ⟨K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hk) (K.inv_mem hk')) hk) hk', ?_⟩
    show k⁻¹ * k'⁻¹ * k * k' ∈ Subgroup.centralizer (Y : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun w : Additive Y => ((Additive.toMul w : Y) : G))
      (hcommV k hk k' hk' (Additive.ofMul ⟨y, hy⟩))
    simp only [hconj, toMul_ofMul] at h
    calc y * (k⁻¹ * k'⁻¹ * k * k') = k⁻¹ * k'⁻¹ * (k' * (k * y * k⁻¹) * k'⁻¹) * k * k' := by
          group
      _ = k⁻¹ * k'⁻¹ * (k * (k' * y * k'⁻¹) * k⁻¹) * k * k' := by rw [h]
      _ = (k⁻¹ * k'⁻¹ * k * k') * y := by group
  rw [hKfaith, Subgroup.mem_bot] at hc
  calc k * k' = k' * k * (k⁻¹ * k'⁻¹ * k * k') := by group
    _ = k' * k := by rw [hc, mul_one]

theorem exists_large_fixed_of_eight_action_involution {G : Type*} [Group G] [Finite G] {r : ℕ}
    [hr : Fact r.Prime] (hr2 : r ≠ 2) {Y F : Subgroup G} {s : G} (hYc : IsMulCommutative Y)
    (hYr : ∀ y ∈ Y, y ^ r = 1) (hFc : IsMulCommutative F) (hF2 : ∀ t ∈ F, t ^ 2 = 1)
    (hF8 : Nat.card F = 8) (hFY : F ≤ Subgroup.normalizer (Y : Set G))
    (hFfaith : F ⊓ Subgroup.centralizer (Y : Set G) = ⊥)
    (hfix : ∀ t ∈ F, t ≠ 1 → Nat.card (Y ⊓ Subgroup.centralizer {t} : Subgroup G) ≤ r ^ 2)
    (hs2 : s ^ 2 = 1) (hsF : s ∉ F) (hsY : s ∈ Subgroup.normalizer (Y : Set G))
    (hsc : s ∈ Subgroup.centralizer (F : Set G)) :
    ∃ u ∈ F ⊔ Subgroup.zpowers s, u ≠ 1 ∧
      r ^ 2 < Nat.card (Y ⊓ Subgroup.centralizer {u} : Subgroup G) := by
  classical
  have hr' : r.Prime := hr.out
  have hYelem : CFSG.IsElementaryAbelian r Y :=
    { toIsMulCommutative := hYc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hYr _ y.2) }
  have hFelem : CFSG.IsElementaryAbelian 2 F :=
    { toIsMulCommutative := hFc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun t =>
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hF2 _ t.2) }
  have : Finite (Additive Y) := inferInstanceAs (Finite Y)
  have : FiniteDimensional (ZMod r) (Additive Y) := Module.Finite.of_finite
  let E : MulAut Y →* Module.End (ZMod r) (Additive Y) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap r
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  let conj : ∀ g : G, g ∈ Subgroup.normalizer (Y : Set G) → Module.End (ZMod r) (Additive Y) :=
    fun g hg => E (Y.normalizerMonoidHom ⟨g, hg⟩)
  have hconj : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G)) (v : Additive Y),
      ((Additive.toMul (conj g hg v) : Y) : G) = g * (Additive.toMul v : Y) * g⁻¹ :=
    fun _ _ _ => rfl
  let ρF : Representation (ZMod r) F (Additive Y) :=
    E.comp (Y.normalizerMonoidHom.comp (Subgroup.inclusion hFY))
  have hρF : ∀ (t : F) (v : Additive Y), ρF t v = conj t (hFY t.2) v := fun _ _ => rfl
  have h2 : (2 : ZMod r) ≠ 0 := CFSG.RankThree.PartTwo.two_ne_zero_zmod hr' hr2
  have hinj : Function.Injective ρF := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have htC : (t : G) ∈ F ⊓ Subgroup.centralizer (Y : Set G) := by
      refine ⟨t.2, ?_⟩
      show (t : G) ∈ Subgroup.centralizer (Y : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg (fun f : Module.End (ZMod r) (Additive Y) =>
        ((Additive.toMul (f (Additive.ofMul ⟨y, hy⟩)) : Y) : G)) ht
      simp only [hρF, hconj, Module.End.one_apply, toMul_ofMul] at h
      calc y * (t : G) = (t : G) * y * (t : G)⁻¹ * t := by rw [h]
        _ = t * y := by group
    rw [hFfaith, Subgroup.mem_bot] at htC
    exact Subtype.ext htC
  have hfixV : ∀ t : F, t ≠ 1 →
      Module.finrank (ZMod r) (Module.End.eigenspace (ρF t) 1) ≤ 2 := by
    intro t ht
    have ht' : (t : G) ≠ 1 := fun h => ht (Subtype.ext h)
    have hcard : Nat.card (Module.End.eigenspace (ρF t) 1) ≤ r ^ 2 := by
      refine le_trans (Nat.card_le_card_of_injective
        (β := (Y ⊓ Subgroup.centralizer {(t : G)} : Subgroup G))
        (fun v => ⟨((Additive.toMul (v : Additive Y) : Y) : G),
          (Additive.toMul (v : Additive Y)).2, ?_⟩) ?_) (hfix t t.2 ht')
      · have hv := v.2
        rw [Module.End.mem_eigenspace_iff, one_smul] at hv
        have h := congrArg (fun w : Additive Y => ((Additive.toMul w : Y) : G)) hv
        rw [hρF, hconj] at h
        show ((Additive.toMul (v : Additive Y) : Y) : G) ∈ Subgroup.centralizer {(t : G)}
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc ((Additive.toMul (v : Additive Y) : Y) : G) * (t : G) =
            (t : G) * (Additive.toMul (v : Additive Y) : Y) * (t : G)⁻¹ * t := by rw [h]
          _ = t * (Additive.toMul (v : Additive Y) : Y) := by group
      · intro v w h
        apply Subtype.ext
        have h' := congrArg Subtype.val h
        exact Additive.toMul.injective (Subtype.ext h')
    have : Fintype (Module.End.eigenspace (ρF t) 1) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod r) (V := Module.End.eigenspace (ρF t) 1)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    rw [hpow] at hcard
    exact (Nat.pow_le_pow_iff_right hr'.one_lt).mp hcard
  obtain ⟨χ, hli, hχspan, hone, -, -, -, -, -⟩ :=
    CFSG.RankThree.PartTwo.eight_action_small_fixed_space hF8 h2 ρF hinj hfixV
  let := Fintype.ofFinite F
  set T := conj s hsY with hT_def
  have hTF : ∀ (f : F) (v : Additive Y), ρF f (T v) = T (ρF f v) := by
    intro f v
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [hρF, hT_def, hconj]
    have hsf : (f : G) * s = s * f := Subgroup.mem_centralizer_iff.mp hsc f f.2
    calc (f : G) * (s * (Additive.toMul v : Y) * s⁻¹) * (f : G)⁻¹ =
        ((f : G) * s) * (Additive.toMul v : Y) * ((f : G) * s)⁻¹ := by group
      _ = (s * f) * (Additive.toMul v : Y) * (s * f)⁻¹ := by rw [hsf]
      _ = s * ((f : G) * (Additive.toMul v : Y) * (f : G)⁻¹) * s⁻¹ := by group
  have hT2 : ∀ v : Additive Y, T (T v) = v := by
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [hT_def, hconj]
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq, hs2])
    rw [hs']
    have hss : s * s = 1 := by rw [← sq, hs2]
    calc s * (s * (Additive.toMul v : Y) * s) * s = (s * s) * (Additive.toMul v : Y) * (s * s) := by
          simp only [mul_assoc]
      _ = _ := by rw [hss, one_mul, mul_one]
  have hTpres : ∀ ψ, ∀ v ∈ signWeightSpace ρF ψ, T v ∈ signWeightSpace ρF ψ := by
    intro ψ v hv
    rw [mem_signWeightSpace] at hv ⊢
    intro a
    rw [hTF a v, hv a, map_smul]
  have hsign : ∀ i, ∃ w ∈ signWeightSpace ρF (χ i), w ≠ 0 ∧ ∃ ε : ZMod r,
      (ε = 1 ∨ ε = -1) ∧ ∀ v ∈ signWeightSpace ρF (χ i), T v = ε • v := by
    intro i
    have hne : signWeightSpace ρF (χ i) ≠ ⊥ := by
      intro h
      have := hone i
      rw [h, finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hspan : (ZMod r) ∙ w = signWeightSpace ρF (χ i) := by
      apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hw)
      rw [finrank_span_singleton hw0, hone i]
    have hscal : ∀ v ∈ signWeightSpace ρF (χ i), ∃ c : ZMod r, v = c • w := by
      intro v hv
      rw [← hspan] at hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      exact ⟨c, rfl⟩
    obtain ⟨ε, hε⟩ := hscal _ (hTpres _ w hw)
    have hε2 : ε * ε = 1 := by
      have h := hT2 w
      rw [hε, map_smul, hε, smul_smul] at h
      have h' : (ε * ε - 1) • w = 0 := by rw [sub_smul, h, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hw0)
    refine ⟨w, hw, hw0, ε, mul_self_eq_one_iff.mp hε2, fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := hscal v hv
    rw [map_smul, hε, smul_comm]
  choose w hw hw0 ε hε hTε using hsign
  have : FiniteDimensional (ZMod 2) (Additive F) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) (Additive F) = 3 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive F)
    rw [ZMod.card] at h
    have h8 : Fintype.card (Additive F) = 2 ^ 3 := by
      rw [show Fintype.card (Additive F) = Nat.card F from (Nat.card_eq_fintype_card).symm, hF8]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans h8)
  let Φ : Additive F →ₗ[ZMod 2] (Fin 3 → ZMod 2) := LinearMap.pi χ
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) x).mp fun φ => ?_
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp
      (hχspan ▸ Submodule.mem_top : φ ∈ Submodule.span (ZMod 2) (Set.range χ))
    rw [← hc, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.smul_apply, show χ i x = 0 from congrFun hx i, smul_zero]
  have hΦsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hdim, Module.finrank_fin_fun])).mp hΦinj
  obtain ⟨x, hx⟩ := hΦsurj fun i => if ε i = 1 then 0 else 1
  set f : F := Additive.toMul x with hf_def
  have hfw : ∀ i, ∀ v ∈ signWeightSpace ρF (χ i), ρF f v = ε i • v := by
    intro i v hv
    rw [(mem_signWeightSpace ρF (χ i) v).mp hv f]
    have hχx : χ i (Additive.ofMul f) = if ε i = 1 then 0 else 1 := congrFun hx i
    have hv0 : (0 : ZMod 2).val = 0 := rfl
    have hv1 : (1 : ZMod 2).val = 1 := rfl
    rw [hχx]
    rcases hε i with h1 | h1
    · simp only [h1, ↓reduceIte, hv0, pow_zero]
    · have hneg : (-1 : ZMod r) ≠ 1 := fun h => h2 (by linear_combination -h)
      simp only [h1, hneg, ↓reduceIte, hv1, pow_one]
  refine ⟨s * f, Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
    (Subgroup.mem_sup_left f.2), fun h => hsF ?_, ?_⟩
  · have : s = (f : G)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact F.inv_mem f.2
  have hu : s * f ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ hsY (hFY f.2)
  have hconj_u : ∀ v : Additive Y, conj (s * f) hu v = T (ρF f v) := by
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [hρF, hT_def, hconj]
    group
  have hfixed : ∀ i, signWeightSpace ρF (χ i) ≤ Module.End.eigenspace (conj (s * f) hu) 1 := by
    intro i v hv
    rw [Module.End.mem_eigenspace_iff, one_smul, hconj_u, hfw i v hv, map_smul, hTε i v hv,
      smul_smul]
    rcases hε i with h1 | h1 <;> rw [h1] <;> simp
  let := Fintype.ofFinite F
  have : Finite (Module.Dual (ZMod 2) (Additive F)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive F) => (f : Additive F → ZMod 2))
      DFunLike.coe_injective
  let := Fintype.ofFinite (Module.Dual (ZMod 2) (Additive F))
  have hind := iSupIndep_signWeightSpace ρF h2
  have hχinj : Function.Injective χ := hli.injective
  have d3 : Disjoint (signWeightSpace ρF (χ 0) ⊔ signWeightSpace ρF (χ 1))
      (signWeightSpace ρF (χ 2)) :=
    ((hind (χ 2)).mono_right (sup_le
      (le_iSup₂_of_le (χ 0) (fun h => absurd (hχinj h) (by decide)) le_rfl)
      (le_iSup₂_of_le (χ 1) (fun h => absurd (hχinj h) (by decide)) le_rfl))).symm
  have h3 := CFSG.RankThree.PartTwo.finrank_sup_of_disjoint d3
  rw [CFSG.RankThree.PartTwo.finrank_sup_of_disjoint (hind.pairwiseDisjoint
    (fun h => absurd (hχinj h) (by decide) : χ 0 ≠ χ 1)), hone 0, hone 1, hone 2] at h3
  have hle3 : 3 ≤ Module.finrank (ZMod r) (Module.End.eigenspace (conj (s * f) hu) 1) := by
    have := Submodule.finrank_mono (sup_le (sup_le (hfixed 0) (hfixed 1)) (hfixed 2))
    omega
  have : Fintype (Module.End.eigenspace (conj (s * f) hu) 1) := Fintype.ofFinite _
  have hpow := Module.card_eq_pow_finrank (K := ZMod r)
    (V := Module.End.eigenspace (conj (s * f) hu) 1)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
  have hinjE : Nat.card (Module.End.eigenspace (conj (s * f) hu) 1) ≤
      Nat.card (Y ⊓ Subgroup.centralizer {s * (f : G)} : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun v => ⟨((Additive.toMul (v : Additive Y) : Y) : G),
        (Additive.toMul (v : Additive Y)).2, ?_⟩) ?_
    · have hv := v.2
      rw [Module.End.mem_eigenspace_iff, one_smul] at hv
      have h := congrArg (fun w : Additive Y => ((Additive.toMul w : Y) : G)) hv
      rw [hconj] at h
      show ((Additive.toMul (v : Additive Y) : Y) : G) ∈ Subgroup.centralizer {s * (f : G)}
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((Additive.toMul (v : Additive Y) : Y) : G) * (s * f) =
          (s * f) * (Additive.toMul (v : Additive Y) : Y) * (s * f)⁻¹ * (s * f) := by rw [h]
        _ = (s * f) * (Additive.toMul (v : Additive Y) : Y) := by group
    · intro v w h
      apply Subtype.ext
      have h' : ((Additive.toMul (v : Additive Y) : Y) : G) =
          ((Additive.toMul (w : Additive Y) : Y) : G) := by
        simpa using Subtype.ext_iff.mp h
      exact Additive.toMul.injective (Subtype.ext h')
  have hr3 : r ^ 3 ≤ r ^ Module.finrank (ZMod r) (Module.End.eigenspace (conj (s * f) hu) 1) :=
    Nat.pow_le_pow_right hr'.pos hle3
  have hlt : r ^ 2 < r ^ 3 := Nat.pow_lt_pow_right hr'.one_lt (by norm_num)
  omega

end CFSG.RankThree.PartTwo.Source
