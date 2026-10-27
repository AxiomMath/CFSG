module

import CFSG.RankThree.PartTwo.Census.LinearRank
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
public import Mathlib.RepresentationTheory.Basic
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

namespace CFSG.RankThree.PartOne.LIT

open Module CFSG.RankThree.PartTwo.Census

universe u v w

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem exists_fixed_of_sq_le_card [FiniteDimensional K V] {r : ℕ} (hr : r.Prime)
    (hrK : (r : K) ≠ 0) (E : Subgroup (V ≃ₗ[K] V)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ r = 1)
    (hcard : r ^ 2 ≤ Nat.card E) :
    ∃ x ∈ E, x ≠ 1 ∧ ∃ v : V, v ≠ 0 ∧ x v = v := by
  classical
  let _ : CommGroup E := { (inferInstance : Group E) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hexpE : ∀ a : E, a ^ r = 1 := fun a => Subtype.ext (hexp a a.2)
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_exponent hr hexpE
  have : NeZero (Nat.card E : K) :=
    ⟨by rw [hk, Nat.cast_pow]; exact pow_ne_zero k hrK⟩
  let ρ : E →* (V ≃ₗ[K] V) := E.subtype
  let representation := CFSG.LargeEvenClassification.Helpers.linearActionRepresentation ρ
  have : FiniteDimensional K representation.asModule :=
    LinearEquiv.finiteDimensional representation.asModuleEquiv.symm
  obtain ⟨count, summands, equivalence, hsimple, hdimension⟩ :=
    maschke_decomposition (K := K) (A := E) representation.asModule
  have hr2 : 2 ≤ r := hr.two_le
  have hEne : 1 < Nat.card E := lt_of_lt_of_le (by nlinarith) hcard
  have hVpos : 0 < finrank K V := by
    by_contra h
    have h0 : finrank K V = 0 := by omega
    have : Subsingleton V := finrank_zero_iff.mp h0
    have hsub : Subsingleton E :=
      ⟨fun a b => Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)⟩
    have := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    omega
  have hdim : 0 < ∑ i, finrank K (summands i) := by
    rw [← hdimension, representation.asModuleEquiv.finrank_eq]
    exact hVpos
  have hcount : 0 < count := by
    rcases Nat.eq_zero_or_pos count with h | h
    · subst h
      simp at hdim
    · exact h
  let i : Fin count := ⟨0, hcount⟩
  have : IsSimpleModule (MonoidAlgebra K E) (summands i) := hsimple i
  let act := CFSG.LargeEvenClassification.Helpers.groupAlgebraModuleAction (ScalarField := K)
    (Acting := E) (summands i)
  have : IsCyclic act.range :=
    CFSG.LargeEvenClassification.Helpers.simple_groupAlgebra_action_cyclic (summands i)
  have hdvd : Nat.card act.range ∣ r :=
    CFSG.LargeEvenClassification.Helpers.cyclic_action_card_dvd_exponent act hexpE
  have hrange : Nat.card act.range ≤ r := Nat.le_of_dvd hr.pos hdvd
  have hmul : Nat.card E = Nat.card (E ⧸ act.ker) * Nat.card act.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup act.ker
  have hquot : Nat.card (E ⧸ act.ker) = Nat.card act.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange act).toEquiv
  have hker : 1 < Nat.card act.ker := by
    by_contra h
    have h1 : Nat.card act.ker ≤ 1 := by omega
    have hpos : 0 < Nat.card act.ker := Nat.card_pos
    have h2 : Nat.card act.ker = 1 := by omega
    rw [h2, mul_one, hquot] at hmul
    nlinarith
  have hnt : Nontrivial act.ker := Finite.one_lt_card_iff_nontrivial.mp hker
  obtain ⟨⟨x, hxker⟩, hx1⟩ := exists_ne (1 : act.ker)
  have hnz : Nontrivial (summands i) := IsSimpleModule.nontrivial (MonoidAlgebra K E) _
  obtain ⟨s, hs⟩ := exists_ne (0 : summands i)
  have hxs : (MonoidAlgebra.of K E) x • (s : representation.asModule) =
      (s : representation.asModule) := by
    have h := congrArg (fun φ : (summands i) ≃ₗ[K] (summands i) => (φ s : representation.asModule))
      (MonoidHom.mem_ker.mp hxker)
    exact h
  refine ⟨(x : V ≃ₗ[K] V), x.2, fun h => hx1 (Subtype.ext (Subtype.ext h)),
    representation.asModuleEquiv (s : representation.asModule), ?_, ?_⟩
  · intro h
    apply hs
    have := representation.asModuleEquiv.injective (h.trans (map_zero _).symm)
    exact Subtype.ext this
  · have h := congrArg representation.asModuleEquiv hxs
    rw [representation.asModuleEquiv_map_smul, representation.asAlgebraHom_of] at h
    exact h

@[expose] def fixedSpace (x : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.ker ((x : V →ₗ[K] V) - LinearMap.id)

@[expose] def commSpace (x : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.range ((x : V →ₗ[K] V) - LinearMap.id)

theorem mem_fixedSpace {x : V ≃ₗ[K] V} {v : V} : v ∈ fixedSpace x ↔ x v = v := by
  simp [fixedSpace, LinearMap.mem_ker, sub_eq_zero]

theorem mem_commSpace {x : V ≃ₗ[K] V} {w : V} : w ∈ commSpace x ↔ ∃ y, x y - y = w := by
  simp [commSpace, LinearMap.mem_range]

theorem coe_pow_eq (x : V ≃ₗ[K] V) (n : ℕ) :
    ((x ^ n : V ≃ₗ[K] V) : V →ₗ[K] V) = (x : V →ₗ[K] V) ^ n := by
  ext v
  simp [Module.End.pow_apply, LinearEquiv.coe_pow]

theorem isCompl_fixedSpace_commSpace [FiniteDimensional K V] {r : ℕ} (hrK : (r : K) ≠ 0)
    {x : V ≃ₗ[K] V} (hx : x ^ r = 1) : IsCompl (fixedSpace x) (commSpace x) := by
  have hdim : finrank K V ≤ finrank K (fixedSpace x) + finrank K (commSpace x) := by
    have := LinearMap.finrank_range_add_finrank_ker ((x : V →ₗ[K] V) - LinearMap.id)
    unfold fixedSpace commSpace
    omega
  rw [Submodule.isCompl_iff_disjoint _ _ hdim, Submodule.disjoint_def]
  intro v hvU hvW
  have hxr : (x : V →ₗ[K] V) ^ r = 1 := by
    rw [← coe_pow_eq, hx]
    rfl
  obtain ⟨y, hy⟩ := mem_commSpace.mp hvW
  have hfix := mem_fixedSpace.mp hvU
  have hN : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) ((x : V →ₗ[K] V) y - y) = 0 := by
    have h := geom_sum_mul (x : V →ₗ[K] V) r
    rw [hxr, sub_self] at h
    have h2 := congrArg (fun f : V →ₗ[K] V => f y) h
    simpa using h2
  have hpow : ∀ i : ℕ, ((x : V →ₗ[K] V) ^ i) v = v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ, Module.End.mul_apply]; simpa [hfix] using ih
  have hN' : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) v = (r : K) • v := by
    rw [LinearMap.sum_apply]
    simp [hpow, Nat.cast_smul_eq_nsmul K]
  have : (r : K) • v = 0 := by
    rw [← hN', ← hy]
    simpa using hN
  rcases smul_eq_zero.mp this with h | h
  · exact absurd h hrK
  · exact h

theorem map_mem_fixedSpace {x g : V ≃ₗ[K] V} (hxg : g * x = x * g) {u : V}
    (hu : u ∈ fixedSpace x) : g u ∈ fixedSpace x := by
  rw [mem_fixedSpace] at hu ⊢
  have h := LinearEquiv.congr_fun hxg u
  simp only [LinearEquiv.mul_apply] at h
  rw [← h, hu]

theorem map_mem_commSpace {x g : V ≃ₗ[K] V} (hxg : g * x = x * g) {w : V}
    (hw : w ∈ commSpace x) : g w ∈ commSpace x := by
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hw
  refine mem_commSpace.mpr ⟨g y, ?_⟩
  have h := LinearEquiv.congr_fun hxg y
  simp only [LinearEquiv.mul_apply] at h
  rw [map_sub, ← h]

@[expose] def restrictAction {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[K] V)) (S : Submodule K V)
    (hS : ∀ g, ∀ s ∈ S, ρ g s ∈ S) : G →* (S ≃ₗ[K] S) where
  toFun g :=
    { toFun := fun s => ⟨ρ g s, hS g s s.2⟩
      invFun := fun s => ⟨ρ g⁻¹ s, hS g⁻¹ s s.2⟩
      map_add' := fun a b => Subtype.ext (map_add _ _ _)
      map_smul' := fun c a => Subtype.ext (map_smul _ _ _)
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun a => Subtype.ext (by simp) }
  map_one' := LinearEquiv.ext fun a => Subtype.ext (by simp)
  map_mul' g h := LinearEquiv.ext fun a => Subtype.ext (by simp)

theorem restrictAction_apply {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[K] V)) (S : Submodule K V)
    (hS : ∀ g, ∀ s ∈ S, ρ g s ∈ S) (g : G) (s : S) :
    ((restrictAction ρ S hS g s : S) : V) = ρ g s := rfl

theorem ext_of_isCompl {U W : Submodule K V} (h : IsCompl U W) {f g : V →ₗ[K] V}
    (hU : ∀ u ∈ U, f u = g u) (hW : ∀ w ∈ W, f w = g w) : f = g :=
  LinearMap.ext_on_codisjoint h.codisjoint hU hW

theorem det_eq_mul_of_isCompl [FiniteDimensional K V] {U W : Submodule K V} (h : IsCompl U W)
    (f : V →ₗ[K] V) (hU : ∀ u ∈ U, f u ∈ U) (hW : ∀ w ∈ W, f w ∈ W) :
    LinearMap.det f = LinearMap.det (f.restrict hU) * LinearMap.det (f.restrict hW) := by
  let e := Submodule.prodEquivOfIsCompl U W h
  have key : (e : (U × W) →ₗ[K] V).comp ((f.restrict hU).prodMap (f.restrict hW)) =
      f.comp (e : (U × W) →ₗ[K] V) := by
    ext ⟨u, w⟩ <;> simp [e, Submodule.coe_prodEquivOfIsCompl]
  rw [← LinearMap.det_prodMap, ← LinearMap.det_conj ((f.restrict hU).prodMap (f.restrict hW)) e]
  congr 1
  ext v
  have := LinearMap.congr_fun key (e.symm v)
  simpa using this.symm

theorem eq_id_of_det_eq_one_of_finrank_eq_one [FiniteDimensional K V] (hV : finrank K V = 1)
    (g : V →ₗ[K] V) (hg : LinearMap.det g = 1) : g = LinearMap.id := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hV g
  rw [hc, LinearMap.det_smul, hV, pow_one, LinearMap.det_id, mul_one] at hg
  rw [hc, hg, one_smul]

@[expose, instance_reducible] def commGroupOfCommSubgroup {G : Type*} [Group G] (E : Subgroup G)
    (h : ∀ g ∈ E, ∀ k ∈ E, g * k = k * g) : CommGroup E :=
  { (inferInstance : Group E) with mul_comm := fun a b => Subtype.ext (h a a.2 b b.2) }

theorem card_le_pow_finrank_sub [FiniteDimensional K V] {r : ℕ} (hr : r.Prime)
    (hrK : (r : K) ≠ 0) (E : Subgroup (V ≃ₗ[K] V)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ r = 1) :
    Nat.card E ≤ r ^ finrank K V := by
  let _ := commGroupOfCommSubgroup E hcomm
  exact card_le_pow_finrank_of_faithful hr hrK (fun a : E => Subtype.ext (hexp a a.2))
    E.subtype E.subtype_injective

theorem card_le_sq_of_det_eq_one [FiniteDimensional K V] {r : ℕ} (hr : r.Prime)
    (hrK : (r : K) ≠ 0) (hV : finrank K V = 3) (E : Subgroup (V ≃ₗ[K] V)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ r = 1)
    (hdet : ∀ g ∈ E, LinearMap.det (g : V →ₗ[K] V) = 1) : Nat.card E ≤ r ^ 2 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hr hrK E hcomm hexp hlt.le
  have hc := isCompl_fixedSpace_commSpace hrK (hexp x hxE)
  have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
  have hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x :=
    fun g u hu => map_mem_fixedSpace (hxcomm g g.2) hu
  have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
    fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hUpos : 0 < finrank K (fixedSpace x) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨v, mem_fixedSpace.mpr hxv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have hWpos : 0 < finrank K (commSpace x) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    by_contra hcon
    have hcon' : ∀ w : commSpace x, w = 0 := fun w => by_contra fun hw => hcon ⟨w, hw⟩
    apply hx1
    apply LinearEquiv.ext
    intro y
    have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
    have h2 : x y - y = 0 := congrArg Subtype.val (hcon' ⟨x y - y, hy⟩)
    simpa [sub_eq_zero] using h2
  let ρ : E →* (V ≃ₗ[K] V) := E.subtype
  let ρU := restrictAction ρ (fixedSpace x) hUinv
  let ρW := restrictAction ρ (commSpace x) hWinv
  have hdet2 : ∀ g : E, LinearMap.det (ρU g : fixedSpace x →ₗ[K] fixedSpace x) *
      LinearMap.det (ρW g : commSpace x →ₗ[K] commSpace x) = 1 := by
    intro g
    have h := det_eq_mul_of_isCompl hc (g : V ≃ₗ[K] V).toLinearMap (hUinv g) (hWinv g)
    rw [hdet g g.2] at h
    exact h.symm
  have hext : ∀ g : E, ρU g = 1 → ρW g = 1 → g = 1 := by
    intro g h1 h2
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    have hfun : (g : V ≃ₗ[K] V).toLinearMap = LinearMap.id := by
      apply ext_of_isCompl hc
      · intro u hu
        exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h1 ⟨u, hu⟩))
      · intro w hw
        exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h2 ⟨w, hw⟩))
    exact LinearMap.congr_fun hfun y
  have hexpE : ∀ a : E, a ^ r = 1 := fun a => Subtype.ext (hexp a a.2)
  have hcases : finrank K (fixedSpace x) = 1 ∨ finrank K (commSpace x) = 1 := by omega
  let _ := commGroupOfCommSubgroup E hcomm
  rcases hcases with hU1 | hW1
  · have hinj : Function.Injective ρW := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      have hd : LinearMap.det (ρU g : fixedSpace x →ₗ[K] fixedSpace x) = 1 := by
        have := hdet2 g
        rw [hg] at this
        simpa using this
      have h1 : ρU g = 1 :=
        LinearEquiv.ext fun a => LinearMap.congr_fun
          (eq_id_of_det_eq_one_of_finrank_eq_one hU1 _ hd) a
      exact Subgroup.mem_bot.2 (hext g h1 hg)
    have := card_le_pow_finrank_of_faithful hr hrK hexpE ρW hinj
    have h2 : finrank K (commSpace x) = 2 := by omega
    rw [h2] at this
    omega
  · have hinj : Function.Injective ρU := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      have hd : LinearMap.det (ρW g : commSpace x →ₗ[K] commSpace x) = 1 := by
        have := hdet2 g
        rw [hg] at this
        simpa using this
      have h1 : ρW g = 1 :=
        LinearEquiv.ext fun a => LinearMap.congr_fun
          (eq_id_of_det_eq_one_of_finrank_eq_one hW1 _ hd) a
      exact Subgroup.mem_bot.2 (hext g hg h1)
    have := card_le_pow_finrank_of_faithful hr hrK hexpE ρU hinj
    have h2 : finrank K (fixedSpace x) = 2 := by omega
    rw [h2] at this
    omega

theorem alt_skew {B : V →ₗ[K] V →ₗ[K] K} (hB : ∀ v, B v v = 0) (a b : V) :
    B a b = - B b a := by
  have h := hB (a + b)
  simp only [map_add, LinearMap.add_apply, hB a, hB b] at h
  linear_combination h

theorem card_le_pow_half_of_alt {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0) :
    ∀ (n : ℕ) (X : Type v) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
      finrank K X = n → ∀ (B : X →ₗ[K] X →ₗ[K] K), (∀ v, (∀ w, B v w = 0) → v = 0) →
      (∀ v, B v v = 0) → ∀ (E : Subgroup (X ≃ₗ[K] X)) [Finite E],
      (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ r = 1) →
      (∀ g ∈ E, ∀ u w, B (g u) (g w) = B u w) → Nat.card E ≤ r ^ (n / 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn B hB hAlt E _ hcomm hexp hpres
  have hexpE : ∀ a : E, a ^ r = 1 := fun a => Subtype.ext (hexp a a.2)
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_exponent hr hexpE
  have hr2 : 2 ≤ r := hr.two_le
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · have : Subsingleton X := finrank_zero_iff.mp hn
      have hsub : Subsingleton E :=
        ⟨fun a b => Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)⟩
      have := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
      simp
    · exfalso
      have hpos : 0 < finrank K X := by omega
      obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
      have hall := (finrank_eq_one_iff_of_nonzero' v hv).mp hn
      apply hv
      apply hB
      intro w
      obtain ⟨c, rfl⟩ := hall w
      rw [map_smul, hAlt, smul_zero]
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : Nat.card E ≤ r := by
        rw [hk]
        calc r ^ k ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos (by omega)
          _ = r := pow_one r
      calc Nat.card E ≤ r := this
        _ = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ (n / 2) := Nat.pow_le_pow_right hr.pos (by omega)
    · have hbig : r ^ 2 ≤ Nat.card E := by
        rw [hk]; exact Nat.pow_le_pow_right hr.pos hk2
      obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hr hrK E hcomm hexp hbig
      have hc := isCompl_fixedSpace_commSpace hrK (hexp x hxE)
      have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
      have hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x :=
        fun g u hu => map_mem_fixedSpace (hxcomm g g.2) hu
      have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
        fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
      have hsum := Submodule.finrank_add_eq_of_isCompl hc
      have hUpos : 0 < finrank K (fixedSpace x) := by
        apply Module.finrank_pos_iff_exists_ne_zero.mpr
        exact ⟨⟨v, mem_fixedSpace.mpr hxv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
      have hWpos : 0 < finrank K (commSpace x) := by
        apply Module.finrank_pos_iff_exists_ne_zero.mpr
        by_contra hcon
        have hcon' : ∀ w : commSpace x, w = 0 := fun w => by_contra fun hw => hcon ⟨w, hw⟩
        apply hx1
        apply LinearEquiv.ext
        intro y
        have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
        have h2 : x y - y = 0 := congrArg Subtype.val (hcon' ⟨x y - y, hy⟩)
        simpa [sub_eq_zero] using h2
      have hskew := alt_skew hAlt
      have hUW : ∀ u ∈ fixedSpace x, ∀ w ∈ commSpace x, B u w = 0 := by
        intro u hu w hw
        obtain ⟨y, rfl⟩ := mem_commSpace.mp hw
        have h1 := hpres x hxE u y
        rw [mem_fixedSpace.mp hu] at h1
        rw [map_sub, h1, sub_self]
      have hWU : ∀ w ∈ commSpace x, ∀ u ∈ fixedSpace x, B w u = 0 := by
        intro w hw u hu
        rw [hskew w u, hUW u hu w hw, neg_zero]
      have hsplit : ∀ y : X, ∃ u ∈ fixedSpace x, ∃ w ∈ commSpace x, u + w = y := by
        intro y
        have : y ∈ fixedSpace x ⊔ commSpace x := by rw [hc.sup_eq_top]; trivial
        exact Submodule.mem_sup.mp this
      let ρ : E →* (X ≃ₗ[K] X) := E.subtype
      let ρU := restrictAction ρ (fixedSpace x) hUinv
      let ρW := restrictAction ρ (commSpace x) hWinv
      let BU : fixedSpace x →ₗ[K] fixedSpace x →ₗ[K] K :=
        B.compl₁₂ (fixedSpace x).subtype (fixedSpace x).subtype
      let BW : commSpace x →ₗ[K] commSpace x →ₗ[K] K :=
        B.compl₁₂ (commSpace x).subtype (commSpace x).subtype
      have hBU : ∀ u : fixedSpace x, (∀ u' : fixedSpace x, BU u u' = 0) → u = 0 := by
        intro u hu
        apply Subtype.ext
        apply hB
        intro y
        obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hsplit y
        rw [map_add, hUW u u.2 w₁ hw₁, add_zero]
        exact hu ⟨u₁, hu₁⟩
      have hBW : ∀ w : commSpace x, (∀ w' : commSpace x, BW w w' = 0) → w = 0 := by
        intro w hw
        apply Subtype.ext
        apply hB
        intro y
        obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hsplit y
        rw [map_add, hWU w w.2 u₁ hu₁, zero_add]
        exact hw ⟨w₁, hw₁⟩
      have hAltU : ∀ u : fixedSpace x, BU u u = 0 := fun u => hAlt u
      have hAltW : ∀ w : commSpace x, BW w w = 0 := fun w => hAlt w
      let EU : Subgroup (fixedSpace x ≃ₗ[K] fixedSpace x) := ρU.range
      let EW : Subgroup (commSpace x ≃ₗ[K] commSpace x) := ρW.range
      have : Finite EU := Finite.of_surjective ρU.rangeRestrict ρU.rangeRestrict_surjective
      have : Finite EW := Finite.of_surjective ρW.rangeRestrict ρW.rangeRestrict_surjective
      have hcommU : ∀ g ∈ EU, ∀ h ∈ EU, g * h = h * g := by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg ρU (Subtype.ext (hcomm a a.2 b b.2))
      have hcommW : ∀ g ∈ EW, ∀ h ∈ EW, g * h = h * g := by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg ρW (Subtype.ext (hcomm a a.2 b b.2))
      have hexpU : ∀ g ∈ EU, g ^ r = 1 := by
        rintro _ ⟨a, rfl⟩
        rw [← map_pow, hexpE a, map_one]
      have hexpW : ∀ g ∈ EW, g ^ r = 1 := by
        rintro _ ⟨a, rfl⟩
        rw [← map_pow, hexpE a, map_one]
      have hpresU : ∀ g ∈ EU, ∀ u w, BU (g u) (g w) = BU u w := by
        rintro _ ⟨a, rfl⟩ u w
        exact hpres a a.2 u w
      have hpresW : ∀ g ∈ EW, ∀ u w, BW (g u) (g w) = BW u w := by
        rintro _ ⟨a, rfl⟩ u w
        exact hpres a a.2 u w
      have hIU := ih (finrank K (fixedSpace x)) (by omega) (fixedSpace x) rfl BU hBU hAltU EU
        hcommU hexpU hpresU
      have hIW := ih (finrank K (commSpace x)) (by omega) (commSpace x) rfl BW hBW hAltW EW
        hcommW hexpW hpresW
      have hinj : Function.Injective
          (fun g : E => ((⟨ρU g, g, rfl⟩ : EU), (⟨ρW g, g, rfl⟩ : EW))) := by
        intro g h hgh
        simp only [Prod.mk.injEq] at hgh
        obtain ⟨h1, h2⟩ := hgh
        have h1' : ρU g = ρU h := congrArg Subtype.val h1
        have h2' : ρW g = ρW h := congrArg Subtype.val h2
        apply Subtype.ext
        apply LinearEquiv.ext
        intro y
        have hfun : (g : X ≃ₗ[K] X).toLinearMap = (h : X ≃ₗ[K] X).toLinearMap := by
          apply ext_of_isCompl hc
          · intro u hu
            exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
              ((congrArg Subtype.val (LinearEquiv.congr_fun h1' ⟨u, hu⟩)).trans
                (restrictAction_apply ρ (fixedSpace x) hUinv h ⟨u, hu⟩))
          · intro w hw
            exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
              ((congrArg Subtype.val (LinearEquiv.congr_fun h2' ⟨w, hw⟩)).trans
                (restrictAction_apply ρ (commSpace x) hWinv h ⟨w, hw⟩))
        exact LinearMap.congr_fun hfun y
      have hle : Nat.card E ≤ Nat.card EU * Nat.card EW := by
        rw [← Nat.card_prod]
        exact Nat.card_le_card_of_injective _ hinj
      calc Nat.card E ≤ Nat.card EU * Nat.card EW := hle
        _ ≤ r ^ (finrank K (fixedSpace x) / 2) * r ^ (finrank K (commSpace x) / 2) :=
          Nat.mul_le_mul hIU hIW
        _ = r ^ (finrank K (fixedSpace x) / 2 + finrank K (commSpace x) / 2) :=
          (pow_add _ _ _).symm
        _ ≤ r ^ (n / 2) := Nat.pow_le_pow_right hr.pos (by omega)

end CFSG.RankThree.PartOne.LIT
