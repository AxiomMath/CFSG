module

public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.RankThree.PartTwo.EightActionSmallFixedSpace
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
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

open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo

@[expose] def fixedSubgroupOf {P : Type*} [Group P] (σ : MulAut P) : Subgroup P :=
  σ.toMonoidHom.eqLocus (MonoidHom.id P)

theorem mem_fixedSubgroupOf {P : Type*} [Group P] (σ : MulAut P) (x : P) :
    x ∈ fixedSubgroupOf σ ↔ σ x = x :=
  Iff.rfl

theorem two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have := hp.two_le
  omega

theorem not_two_dvd_card_of_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (hG : IsPGroup p G) : ¬ 2 ∣ Nat.card G := by
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  rw [hk]
  intro h
  have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).mp
    (Nat.prime_two.dvd_of_dvd_pow h)
  exact hp2 h2.symm

theorem subgroup_commutator_le_center {P : Type*} [Group P]
    (hclass : commutator P ≤ Subgroup.center P) (C : Subgroup P) :
    commutator C ≤ Subgroup.center C := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  have hxy : ⁅(x : P), (y : P)⁆ ∈ Subgroup.center P := hclass (by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hcoe : ((⁅x, y⁆ : C) : P) = ⁅(x : P), (y : P)⁆ := by
    simp [commutatorElement_def]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
  exact Subgroup.mem_center_iff.mp hxy z

theorem zpow_apply_eq_self_of_apply_eq_self {X : Type*} [Group X] {σ : MulAut X} {x : X}
    (h : σ x = x) (k : ℤ) : (σ ^ k) x = x := by
  have hσ : σ ∈ MulAction.stabilizer (MulAut X) x := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have := (MulAction.stabilizer (MulAut X) x).zpow_mem hσ k
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

theorem class_two_eight_action_inverting_quotient {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hexp : ∀ x : P, x ^ p = 1)
    (hclass : commutator P ≤ Subgroup.center P)
    {A : Type*} [CommGroup A] [Finite A] (hA2 : ∀ a : A, a ^ 2 = 1) (hA8 : Nat.card A = 8)
    (ρ : A →* MulAut P) (hρ : Function.Injective ρ)
    (hfix : ∀ a : A, a ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ a)) ≤ 2) :
    (CFSG.pRank p (P ⧸ frattini P) = 3 ∨ CFSG.pRank p (P ⧸ frattini P) = 4) ∧
    (∃! a₀ : A, a₀ ≠ 1 ∧
      ∀ x : P, ((ρ a₀ x : P) : P ⧸ frattini P) = ((x : P ⧸ frattini P))⁻¹) ∧
    ∀ a₀ : A, (a₀ ≠ 1 ∧ ∀ x : P, ((ρ a₀ x : P) : P ⧸ frattini P) = ((x : P ⧸ frattini P))⁻¹) →
      ∀ (β : MulAut P) (γ : A ≃* A), (∀ a : A, β * ρ a * β⁻¹ = ρ (γ a)) →
        γ a₀ = a₀ ∧ Subgroup.closure (Set.range fun a : A => a⁻¹ * γ a) ≠ ⊤ := by
  classical
  have hp' : p.Prime := hp.out
  obtain ⟨hchar, hVcomm, hVexp, hVelem, d, hVcard, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient hP
  have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
  have : FiniteDimensional (ZMod p) (Additive (P ⧸ frattini P)) := Module.Finite.of_finite
  let E : MulAut (P ⧸ frattini P) →* Module.End (ZMod p) (Additive (P ⧸ frattini P)) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap p
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hE : ∀ (σ : MulAut (P ⧸ frattini P)) (q : P ⧸ frattini P),
      E σ (Additive.ofMul q) = Additive.ofMul (σ q) := fun _ _ => rfl
  let q := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini P)
  have hq : ∀ (σ : MulAut P) (x : P), q σ (x : P ⧸ frattini P) = ((σ x : P) : P ⧸ frattini P) :=
    fun σ x => CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ σ x
  let ρV : Representation (ZMod p) A (Additive (P ⧸ frattini P)) := E.comp (q.comp ρ)
  have hρV : ∀ (a : A) (x : P), ρV a (Additive.ofMul (x : P ⧸ frattini P)) =
      Additive.ofMul ((ρ a x : P) : P ⧸ frattini P) := fun a x => by
    change E (q (ρ a)) _ = _
    rw [hE, hq]
  let : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule fun x => by
    change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
    rw [hA2]
  have hinjV : Function.Injective ρV := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra ha1
    have hρa : ρ a ≠ 1 := fun h => ha1 (hρ (h.trans (map_one ρ).symm))
    have hord : orderOf (ρ a) = 2 := orderOf_eq_prime (by rw [← map_pow, hA2, map_one]) hρa
    apply hρa
    refine CFSG.OrderReductions.FrattiniAutomorphisms.prime_order_frattini_kernel_trivial 2
      (ρ a) hord (not_two_dvd_card_of_odd hp2 hP) ?_
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    have h := congrArg (fun f : Module.End (ZMod p) (Additive (P ⧸ frattini P)) =>
      f (Additive.ofMul (x : P ⧸ frattini P))) ha
    simp only [hρV, Module.End.one_apply] at h
    exact congrArg Additive.toMul h
  have hfixV : ∀ a : A, a ≠ 1 →
      Module.finrank (ZMod p) (Module.End.eigenspace (ρV a) 1) ≤ 2 := by
    intro a ha
    set C := fixedSubgroupOf (ρ a) with hC_def
    let Z := Subgroup.zpowers a
    have hZ2 : IsPGroup 2 Z := fun g => ⟨1, by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hA2, one_zpow, Subgroup.coe_one]⟩
    let α : Z →* MulAut P := ρ.comp Z.subtype
    have hN : ∀ b : Z, ∀ n ∈ frattini P, α b n ∈ frattini P := by
      intro b n hn
      have h := Subgroup.characteristic_iff_map_eq.mp hchar (α b)
      rw [← h]
      exact Subgroup.mem_map_of_mem _ hn
    have hcop : ¬ 2 ∣ Nat.card (frattini P) := not_two_dvd_card_of_odd hp2 (hP.to_subgroup _)
    have hset := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hZ2 α (frattini P) hN
      hcop
    have hlift : ∀ w ∈ Module.End.eigenspace (ρV a) 1,
        ∃ c ∈ C, w = Additive.ofMul (c : P ⧸ frattini P) := by
      intro w hw
      rw [Module.End.mem_eigenspace_iff, one_smul] at hw
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
      have hwx : w = Additive.ofMul (x : P ⧸ frattini P) := by rw [hx]; rfl
      have hfixa : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN
          ⟨a, Subgroup.mem_zpowers a⟩ (x : P ⧸ frattini P) = (x : P ⧸ frattini P) := by
        rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
        have h := hw
        rw [hwx, hρV] at h
        exact congrArg Additive.toMul h
      have hmem : (x : P ⧸ frattini P) ∈ {q : P ⧸ frattini P | ∀ b : Z,
          CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN b q =
            q} := by
        rintro ⟨b, hb⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        have hb' : (⟨a ^ k, hb⟩ : Z) = ⟨a, Subgroup.mem_zpowers a⟩ ^ k := Subtype.ext (by simp)
        rw [hb', map_zpow]
        exact zpow_apply_eq_self_of_apply_eq_self hfixa k
      rw [hset] at hmem
      obtain ⟨c, hc, hcx⟩ := hmem
      refine ⟨c, hc ⟨a, Subgroup.mem_zpowers a⟩, ?_⟩
      rw [hwx, ← hcx]
      rfl
    let f : C →* P ⧸ frattini P := (QuotientGroup.mk' (frattini P)).comp C.subtype
    have hcomm_ker : commutator C ≤ f.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hVcomm.is_comm.comm _ _
    have hrange : Nat.card f.range ≤ Nat.card (C ⧸ commutator C) := by
      have h1 := Subgroup.card_ker_mul_card_range f
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator C)
      have h3 := Subgroup.card_le_of_le hcomm_ker
      have hpos : 0 < Nat.card f.ker := Nat.card_pos
      have h4 : Nat.card f.range * Nat.card f.ker ≤
          Nat.card (C ⧸ commutator C) * Nat.card f.ker := by
        calc Nat.card f.range * Nat.card f.ker = Nat.card C := by rw [← h1, mul_comm]
          _ = Nat.card (C ⧸ commutator C) * Nat.card (commutator C) := h2
          _ ≤ Nat.card (C ⧸ commutator C) * Nat.card f.ker := Nat.mul_le_mul_left _ h3
      exact Nat.le_of_mul_le_mul_right h4 hpos
    have hCC : Nat.card (C ⧸ commutator C) ≤ p ^ 2 := by
      have hC : IsPGroup p C := hP.to_subgroup C
      have hrank := (class_two_small_rank_order_bounds hC (subgroup_pow_eq_one hexp C)
        (subgroup_commutator_le_center hclass C)).1 (hfix a ha)
      obtain ⟨k, hk⟩ := (hC.to_quotient (commutator C)).exists_card_eq
      have hk2 := (quotient_commutator_rank hp' (subgroup_pow_eq_one hexp C) hk).2
      rw [hk]
      exact Nat.pow_le_pow_right hp'.pos (hk2 ▸ hrank)
    have hcardE : Nat.card (Module.End.eigenspace (ρV a) 1) ≤ p ^ 2 := by
      refine le_trans ?_ (hrange.trans hCC)
      refine Nat.card_le_card_of_injective
        (fun w => (⟨Additive.toMul (w : Additive (P ⧸ frattini P)), ?_⟩ : f.range)) ?_
      · obtain ⟨c, hc, hcw⟩ := hlift w w.2
        exact ⟨⟨c, hc⟩, by rw [hcw]; rfl⟩
      · intro w₁ w₂ h
        apply Subtype.ext
        simpa using congrArg Subtype.val h
    have : Fintype (Module.End.eigenspace (ρV a) 1) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := Module.End.eigenspace (ρV a) 1)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    rw [hpow] at hcardE
    exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp hcardE
  obtain ⟨-, -, -, -, -, -, hdimV, ⟨a₀, ha₀, huniq⟩, hne⟩ :=
    eight_action_small_fixed_space hA8 (two_ne_zero_zmod hp' hp2) ρV hinjV hfixV
  have hinv_iff : ∀ b : A, ρV b = -1 ↔
      ∀ x : P, ((ρ b x : P) : P ⧸ frattini P) = ((x : P ⧸ frattini P))⁻¹ := by
    intro b
    constructor
    · intro h x
      have h1 := congrArg (fun g : Module.End (ZMod p) (Additive (P ⧸ frattini P)) =>
        g (Additive.ofMul (x : P ⧸ frattini P))) h
      simp only [hρV, LinearMap.neg_apply, Module.End.one_apply] at h1
      exact congrArg Additive.toMul h1
    · intro h
      apply LinearMap.ext
      intro w
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
      have hwx : w = Additive.ofMul (x : P ⧸ frattini P) := by rw [hx]; rfl
      rw [hwx, hρV, h x, LinearMap.neg_apply, Module.End.one_apply]
      rfl
  have hunique : ∀ b : A, (b ≠ 1 ∧
      ∀ x : P, ((ρ b x : P) : P ⧸ frattini P) = ((x : P ⧸ frattini P))⁻¹) → b = a₀ :=
    fun b hb => huniq b ((hinv_iff b).mpr hb.2)
  refine ⟨?_, ⟨a₀, ⟨hne a₀ ha₀, (hinv_iff a₀).mp ha₀⟩, hunique⟩, ?_⟩
  ·
    have : Fintype (Additive (P ⧸ frattini P)) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive (P ⧸ frattini P))
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    have hrank := pRank_eq_of_isMulCommutative hp' hVexp hVcomm (k := Module.finrank (ZMod p)
      (Additive (P ⧸ frattini P))) hpow
    rw [hrank]
    exact hdimV
  · intro b hb β γ hβγ
    have hb₀ : b = a₀ := hunique b hb
    subst hb₀
    have hconj : ρV (γ b) = E (q β) * ρV b * E (q β⁻¹) := by
      change E (q (ρ (γ b))) = E (q β) * E (q (ρ b)) * E (q β⁻¹)
      rw [← hβγ b, map_mul, map_mul, map_mul, map_mul]
    have hγ : γ b = b := by
      apply huniq
      have hββ : E (q β) * E (q β⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
      rw [hconj, ha₀]
      apply LinearMap.ext
      intro w
      have h := congrArg (fun g : Module.End (ZMod p) (Additive (P ⧸ frattini P)) => g w) hββ
      simp only [Module.End.mul_apply, Module.End.one_apply] at h
      simp only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply, map_neg, h]
    refine ⟨hγ, ?_⟩
    let g : A →* A :=
      { toFun := fun a => a⁻¹ * γ a
        map_one' := by simp
        map_mul' := fun a c => by
          rw [map_mul, mul_inv_rev]
          rw [mul_comm c⁻¹ a⁻¹, mul_mul_mul_comm] }
    have hclosure : Subgroup.closure (Set.range fun a : A => a⁻¹ * γ a) = g.range := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro _ ⟨a, rfl⟩
        exact ⟨a, rfl⟩
      · rintro _ ⟨a, rfl⟩
        exact Subgroup.subset_closure ⟨a, rfl⟩
    rw [hclosure]
    intro htop
    have hker : b ∈ g.ker := by
      change b⁻¹ * γ b = 1
      rw [hγ, inv_mul_cancel]
    have hker1 : Nat.card g.ker ≠ 1 := by
      rw [Ne, Subgroup.card_eq_one]
      intro h
      rw [h, Subgroup.mem_bot] at hker
      exact hne b ha₀ hker
    have h1 := Subgroup.card_ker_mul_card_range g
    rw [htop, Subgroup.card_top] at h1
    have hA : 0 < Nat.card A := Nat.card_pos
    exact hker1 (Nat.eq_of_mul_eq_mul_right hA (h1.trans (one_mul _).symm))


theorem not_commutator_eq_top_of_semidirect {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hexp : ∀ x : P, x ^ p = 1)
    (hclass : commutator P ≤ Subgroup.center P)
    {A : Type*} [CommGroup A] [Finite A] (hA2 : ∀ a : A, a ^ 2 = 1) (hA8 : Nat.card A = 8)
    (ρ : A →* MulAut P) (hρ : Function.Injective ρ)
    (hfix : ∀ a : A, a ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ a)) ≤ 2)
    (θ : MulAut (P ⋊[ρ] A))
    (hθP : ∀ x : P, ∃ y : P, θ (SemidirectProduct.inl x) = SemidirectProduct.inl y)
    (hθA : ∀ a : A, ∃ b : A, θ (SemidirectProduct.inr a) = SemidirectProduct.inr b) :
    ∃ γ : A ≃* A, (∀ a : A, θ (SemidirectProduct.inr a) = SemidirectProduct.inr (γ a)) ∧
      Subgroup.closure (Set.range fun a : A => a⁻¹ * γ a) ≠ ⊤ := by
  choose β hβ using hθP
  choose γ hγ using hθA
  have hinl := SemidirectProduct.inl_injective (φ := ρ)
  have hinr := SemidirectProduct.inr_injective (φ := ρ)
  let βh : P →* P :=
    { toFun := β
      map_one' := hinl (by rw [← hβ, map_one, map_one])
      map_mul' := fun x y => hinl (by rw [← hβ, map_mul, map_mul, map_mul, hβ, hβ]) }
  let γh : A →* A :=
    { toFun := γ
      map_one' := hinr (by rw [← hγ, map_one, map_one])
      map_mul' := fun a b => hinr (by rw [← hγ, map_mul, map_mul, map_mul, hγ, hγ]) }
  have hβinj : Function.Injective βh := fun x y h =>
    hinl (θ.injective (by rw [hβ, hβ]; exact congrArg SemidirectProduct.inl h))
  have hγinj : Function.Injective γh := fun a b h =>
    hinr (θ.injective (by rw [hγ, hγ]; exact congrArg SemidirectProduct.inr h))
  let βe : MulAut P := MulEquiv.ofBijective βh (Finite.injective_iff_bijective.mp hβinj)
  let γe : A ≃* A := MulEquiv.ofBijective γh (Finite.injective_iff_bijective.mp hγinj)
  have hcomm : ∀ (a : A) (x : P), β (ρ a x) = ρ (γ a) (β x) := by
    intro a x
    apply hinl
    rw [← hβ, SemidirectProduct.inl_aut, map_mul, map_mul,
      map_inv (SemidirectProduct.inr : A →* P ⋊[ρ] A), map_inv θ, hβ, hγ,
      ← map_inv (SemidirectProduct.inr : A →* P ⋊[ρ] A), ← SemidirectProduct.inl_aut]
  have hβγ : ∀ a : A, βe * ρ a * βe⁻¹ = ρ (γe a) := by
    intro a
    ext y
    obtain ⟨x, rfl⟩ := (Finite.injective_iff_bijective.mp hβinj).2 y
    change βe (ρ a (βe⁻¹ (βh x))) = ρ (γ a) (βh x)
    have hx : βe⁻¹ (βh x) = x := by
      rw [MulAut.inv_apply]
      exact βe.symm_apply_apply x
    rw [hx]
    exact hcomm a x
  obtain ⟨-, ⟨a₀, ha₀, -⟩, hlast⟩ :=
    class_two_eight_action_inverting_quotient hp2 hP hexp hclass hA2 hA8 ρ hρ hfix
  exact ⟨γe, hγ, (hlast a₀ ha₀ βe γe hβγ).2⟩

end CFSG.RankThree.PartTwo
