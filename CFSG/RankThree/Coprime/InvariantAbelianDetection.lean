module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
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

namespace CFSG.RankThree.Coprime

open Subgroup
open scoped commutatorElement

section Detection

variable {P : Type*} [Group P] {A : Type*} [CommGroup A] [MulDistribMulAction A P]

theorem mul_self_eq_one_of_zmod_two [Module (ZMod 2) (Additive A)] (b : A) : b * b = 1 := by
  have h := ZModModule.char_nsmul_eq_zero 2 (Additive.ofMul b)
  rw [two_nsmul] at h
  have h' : Additive.ofMul (b * b) = Additive.ofMul 1 := by
    rw [ofMul_mul, ofMul_one]
    exact h
  exact Additive.ofMul.injective h'

omit [MulDistribMulAction A P] in
theorem smul_mem_center_of_mem {A : Type*} [Group A] [MulDistribMulAction A P] {z : P}
    (hz : z ∈ center P) (a : A) : a • z ∈ center P := by
  rw [mem_center_iff] at hz ⊢
  intro g
  have h := hz (a⁻¹ • g)
  calc g * a • z = a • (a⁻¹ • g) * a • z := by rw [smul_inv_smul]
    _ = a • (a⁻¹ • g * z) := by rw [smul_mul']
    _ = a • (z * a⁻¹ • g) := by rw [h]
    _ = a • z * g := by rw [smul_mul', smul_inv_smul]

omit [MulDistribMulAction A P] in
theorem normal_of_commutatorElement_mem {D : Subgroup P} (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ D) :
    D.Normal := by
  refine ⟨fun d hd x => ?_⟩
  have h : x * d * x⁻¹ = ⁅x, d⁆ * d := by
    rw [commutatorElement_def]
    group
  rw [h]
  exact D.mul_mem (hcomm x d) hd

theorem inv_mul_smul_mem_centralizer {D : Subgroup P} (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ D) {a : A}
    (ha : ∀ d ∈ D, a • d = d) (x : P) : x⁻¹ * (a • x) ∈ centralizer (D : Set P) := by
  rw [mem_centralizer_iff]
  intro d hd
  have hk : a • ⁅x, d⁆ = ⁅x, d⁆ := ha _ (hcomm x d)
  rw [commutatorElement_def, smul_mul', smul_mul', smul_mul', smul_inv', smul_inv', ha d hd]
    at hk
  have h1 : x * d * x⁻¹ = a • x * d * (a • x)⁻¹ := by
    have := congrArg (· * d) hk
    simpa [mul_assoc] using this.symm
  calc d * (x⁻¹ * a • x) = x⁻¹ * (x * d * x⁻¹) * a • x := by group
    _ = x⁻¹ * (a • x * d * (a • x)⁻¹) * a • x := by rw [h1]
    _ = x⁻¹ * a • x * d := by group

theorem inv_mul_smul_sq_eq_one {D : Subgroup P} {a : A} (ha2 : a * a = 1)
    (ha : ∀ d ∈ D, a • d = d) {x : P} (hc : x⁻¹ * (a • x) ∈ D) :
    (x⁻¹ * (a • x)) ^ 2 = 1 := by
  have hac := ha _ hc
  have hx : a • x = x * (x⁻¹ * (a • x)) := by group
  have h2 : a • (a • x) = x := by rw [← mul_smul, ha2, one_smul]
  rw [hx, smul_mul', hac] at h2
  calc (x⁻¹ * (a • x)) ^ 2 = x⁻¹ * (a • x * (x⁻¹ * (a • x))) := by rw [sq]; group
    _ = 1 := by rw [h2, inv_mul_cancel]

theorem eq_one_of_sq_of_pow_odd {G : Type*} [Group G] {p : ℕ} (hodd : Odd p) {c : G}
    (h2 : c ^ 2 = 1) (hp : c ^ p = 1) : c = 1 := by
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hodd
  have h := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2)
    hcop) (orderOf_dvd_of_pow_eq_one hp)
  exact orderOf_eq_one_iff.mp h

theorem smul_mem_or_of_minimal [Finite P] {D M L : Subgroup P} (hDn : D.Normal)
    (hDinv : ∀ b : A, ∀ x ∈ D, b • x ∈ D) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ D)
    (hsq : ∀ b : A, b * b = 1)
    (hL : Minimal (fun L : Subgroup P => D < L ∧ L ≤ M ∧ ∀ b : A, ∀ x ∈ L, b • x ∈ L) L)
    (b : A) : (∀ l ∈ L, l⁻¹ * (b • l) ∈ D) ∨ (∀ l ∈ L, l * (b • l) ∈ D) := by
  obtain ⟨hDL, hLM, hLinv⟩ := hL.prop
  let Lp : Subgroup P :=
    { carrier := {l | l ∈ L ∧ l⁻¹ * (b • l) ∈ D}
      one_mem' := ⟨L.one_mem, by simp [D.one_mem]⟩
      mul_mem' := by
        rintro l m ⟨hl, hl'⟩ ⟨hm, hm'⟩
        refine ⟨L.mul_mem hl hm, ?_⟩
        have h : (l * m)⁻¹ * (b • (l * m)) =
            m⁻¹ * (l⁻¹ * (b • l)) * m⁻¹⁻¹ * (m⁻¹ * (b • m)) := by
          rw [smul_mul']
          group
        rw [h]
        exact D.mul_mem (hDn.conj_mem _ hl' m⁻¹) hm'
      inv_mem' := by
        rintro l ⟨hl, hl'⟩
        refine ⟨L.inv_mem hl, ?_⟩
        have h : l⁻¹⁻¹ * (b • l⁻¹) = l * (l⁻¹ * (b • l))⁻¹ * l⁻¹ := by
          rw [smul_inv']
          group
        rw [h]
        exact hDn.conj_mem _ (D.inv_mem hl') l }
  have hDLp : D ≤ Lp := fun d hd => ⟨hDL.le hd, D.mul_mem (D.inv_mem hd) (hDinv b d hd)⟩
  have hLpL : Lp ≤ L := fun l hl => hl.1
  have hLpinv : ∀ e : A, ∀ x ∈ Lp, e • x ∈ Lp := by
    rintro e l ⟨hl, hl'⟩
    refine ⟨hLinv e l hl, ?_⟩
    have h : (e • l)⁻¹ * (b • (e • l)) = e • (l⁻¹ * (b • l)) := by
      rw [← mul_smul, mul_comm, mul_smul, smul_mul', smul_inv']
    rw [h]
    exact hDinv e _ hl'
  by_cases hlt : D < Lp
  · left
    intro l hl
    exact (hL.le_of_le ⟨hlt, hLpL.trans hLM, hLpinv⟩ hLpL hl).2
  · right
    have hEq : D = Lp := eq_of_le_of_not_lt hDLp hlt
    intro l hl
    have hu : l * (b • l) ∈ Lp := by
      refine ⟨L.mul_mem hl (hLinv b l hl), ?_⟩
      have h : (l * (b • l))⁻¹ * (b • (l * (b • l))) = ⁅(b • l)⁻¹, l⁻¹⁆ := by
        rw [smul_mul', ← mul_smul, hsq, one_smul, commutatorElement_def]
        group
      rw [h]
      exact hcomm _ _
    rw [← hEq] at hu
    exact hu

theorem exists_invariant_closure_sup [Finite P] {D M : Subgroup P} (hDn : D.Normal)
    (hDinv : ∀ b : A, ∀ x ∈ D, b • x ∈ D) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ D)
    (hsq : ∀ b : A, b * b = 1) (hDM : D < M) (hMinv : ∀ b : A, ∀ x ∈ M, b • x ∈ M) :
    ∃ y ∈ M, y ∉ D ∧ ∀ b : A, ∀ z ∈ closure {y} ⊔ D, b • z ∈ closure {y} ⊔ D := by
  obtain ⟨L, hLM, hL⟩ := Finite.exists_le_minimal
    (p := fun L : Subgroup P => D < L ∧ L ≤ M ∧ ∀ b : A, ∀ x ∈ L, b • x ∈ L)
    ⟨hDM, le_rfl, hMinv⟩
  obtain ⟨y, hyL, hyD⟩ := IsConcreteLE.exists_of_lt hL.prop.1
  refine ⟨y, hLM hyL, hyD, fun b => ?_⟩
  have hy : b • y ∈ closure {y} ⊔ D := by
    have hyc : y ∈ closure {y} ⊔ D := mem_sup_left (subset_closure rfl)
    rcases smul_mem_or_of_minimal hDn hDinv hcomm hsq hL b with h | h
    · have := mul_mem hyc (mem_sup_right (h y hyL) : y⁻¹ * (b • y) ∈ closure {y} ⊔ D)
      rwa [mul_inv_cancel_left] at this
    · have := mul_mem (inv_mem hyc) (mem_sup_right (h y hyL) : y * (b • y) ∈ closure {y} ⊔ D)
      rwa [inv_mul_cancel_left] at this
  have hle : closure {y} ⊔ D ≤
      (closure {y} ⊔ D).comap (MulDistribMulAction.toMonoidHom P b) := by
    refine sup_le ((closure_le _).2 ?_) fun d hd => ?_
    · rintro _ rfl
      exact hy
    · exact mem_sup_right (hDinv b d hd)
  exact fun z hz => hle hz

theorem smul_eq_self_of_maximal [Finite P] [Module (ZMod 2) (Additive A)] {p : ℕ}
    (hodd : Odd p) (hexp : ∀ x : P, x ^ p = 1) (hcomm : commutator P ≤ center P)
    {D : Subgroup P}
    (hD : Maximal (fun D : Subgroup P =>
      (∀ a : A, ∀ x ∈ D, a • x ∈ D) ∧ IsMulCommutative D ∧ center P ≤ D) D)
    {a : A} (ha : ∀ d ∈ D, a • d = d) (x : P) : a • x = x := by
  obtain ⟨hDinv, hDab, hZD⟩ := hD.prop
  have hcD : ∀ x y : P, ⁅x, y⁆ ∈ D := fun x y => hZD (hcomm (by
    rw [_root_.commutator_def]
    exact commutator_mem_commutator (mem_top x) (mem_top y)))
  have hDn : D.Normal := normal_of_commutatorElement_mem hcD
  have hsq : ∀ b : A, b * b = 1 := mul_self_eq_one_of_zmod_two
  by_contra hx
  have hcM := inv_mul_smul_mem_centralizer hcD ha x
  have hcD' : x⁻¹ * (a • x) ∉ D := by
    intro hc
    have h1 := eq_one_of_sq_of_pow_odd hodd (inv_mul_smul_sq_eq_one (hsq a) ha hc) (hexp _)
    apply hx
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  have hDcent : D ≤ centralizer (D : Set P) := le_centralizer_iff_isMulCommutative.mpr hDab
  have hDM : D < centralizer (D : Set P) := lt_of_le_of_ne hDcent fun h => hcD' (h ▸ hcM)
  have hMinv : ∀ b : A, ∀ m ∈ centralizer (D : Set P), b • m ∈ centralizer (D : Set P) := by
    intro b m hm
    rw [mem_centralizer_iff] at hm ⊢
    intro d hd
    have h := hm (b⁻¹ • d) (by simpa using hDinv b⁻¹ d hd)
    calc d * b • m = b • (b⁻¹ • d * m) := by rw [smul_mul', smul_inv_smul]
      _ = b • (m * b⁻¹ • d) := by rw [h]
      _ = b • m * d := by rw [smul_mul', smul_inv_smul]
  obtain ⟨y, hyM, hyD, hyinv⟩ := exists_invariant_closure_sup hDn hDinv hcD hsq hDM hMinv
  have hab : IsMulCommutative (closure {y} ⊔ D : Subgroup P) := by
    have h := isMulCommutative_closure (G := P) (k := {y} ∪ (D : Set P)) (by
      rintro u (rfl | hu) v (rfl | hv) huv
      · exact absurd rfl huv
      · exact ((mem_centralizer_iff.mp hyM) v hv).symm
      · exact (mem_centralizer_iff.mp hyM) u hu
      · exact (mem_centralizer_iff.mp (hDcent hv)) u hu)
    rwa [Subgroup.closure_union, Subgroup.closure_eq] at h
  have hle := hD.le_of_ge ⟨hyinv, hab, hZD.trans le_sup_right⟩ le_sup_right
  exact hyD (hle (mem_sup_left (subset_closure rfl)))

end Detection

theorem elementary_two_invariant_abelian_detection {p : ℕ} (_hp : p.Prime) (hodd : Odd p)
    {P : Type*} [Group P] [Finite P] (_hP : IsPGroup p P) (hexp : ∀ x : P, x ^ p = 1)
    (hcomm : commutator P ≤ Subgroup.center P)
    {A : Type*} [CommGroup A] [Finite A] [Module (ZMod 2) (Additive A)]
    [MulDistribMulAction A P] :
    (∃ D : Subgroup P, Maximal (fun D : Subgroup P =>
      (∀ a : A, ∀ x ∈ D, a • x ∈ D) ∧ IsMulCommutative D ∧ Subgroup.center P ≤ D) D) ∧
    ∀ D : Subgroup P, Maximal (fun D : Subgroup P =>
      (∀ a : A, ∀ x ∈ D, a • x ∈ D) ∧ IsMulCommutative D ∧ Subgroup.center P ≤ D) D →
      CFSG.IsElementaryAbelian p D ∧ D.Normal ∧
      CFSG.fixingSubgroupOf A P (D : Set P) = CFSG.fixingSubgroupOf A P Set.univ ∧
      (FaithfulSMul A P → ∀ a : A, (∀ x ∈ D, a • x = x) → a = 1) := by
  refine ⟨?_, fun D hD => ?_⟩
  · obtain ⟨D, -, hD⟩ := Finite.exists_le_maximal
      (p := fun D : Subgroup P =>
        (∀ a : A, ∀ x ∈ D, a • x ∈ D) ∧ IsMulCommutative D ∧ Subgroup.center P ≤ D)
      (a := Subgroup.center P)
      ⟨fun a _ hx => smul_mem_center_of_mem hx a, inferInstance, le_rfl⟩
    exact ⟨D, hD⟩
  obtain ⟨-, hDab, hZD⟩ := hD.prop
  have hcD : ∀ x y : P, ⁅x, y⁆ ∈ D := fun x y => hZD (hcomm (by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)))
  have hfix : ∀ a : A, (∀ d ∈ D, a • d = d) → ∀ x : P, a • x = x :=
    fun a ha => smul_eq_self_of_maximal hodd hexp hcomm hD ha
  refine ⟨⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hexp g)⟩,
    normal_of_commutatorElement_mem hcD, ?_, fun hfaith a ha => ?_⟩
  · apply le_antisymm
    · intro a ha
      rw [CFSG.fixingSubgroupOf, mem_fixingSubgroup_iff] at ha ⊢
      exact fun x _ => hfix a ha x
    · exact fixingSubgroup_antitone A P (Set.subset_univ _)
  · exact eq_of_smul_eq_smul fun x => by rw [hfix a ha x, one_smul]

end CFSG.RankThree.Coprime
