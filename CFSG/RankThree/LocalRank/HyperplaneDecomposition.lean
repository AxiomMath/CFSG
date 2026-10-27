module

public import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.LocalRank

open scoped DirectSum

section Averaging

variable {A : Type*} [CommGroup A] [Finite A] {K : Type*} [Field K]
  {U : Type*} [AddCommGroup U] [Module K U]

noncomputable def averaging (α : Representation K A U) (B : Subgroup A) : U →ₗ[K] U :=
  letI := Fintype.ofFinite B
  (Nat.card B : K)⁻¹ • ∑ b : B, α b

variable (α : Representation K A U)

theorem averaging_apply_sum (B : Subgroup A) (u : U) :
    letI := Fintype.ofFinite B
    averaging α B u = (Nat.card B : K)⁻¹ • ∑ b : B, α b u := by
  simp only [averaging, LinearMap.smul_apply, LinearMap.sum_apply]

theorem averaging_apply (B : Subgroup A) (u : U) :
    averaging α B u = (Nat.card B : K)⁻¹ • ∑ᶠ b : B, α b u := by
  let := Fintype.ofFinite B
  rw [finsum_eq_sum_of_fintype, averaging_apply_sum]

theorem rep_averaging {B : Subgroup A} {a : A} (ha : a ∈ B) (u : U) :
    α a (averaging α B u) = averaging α B u := by
  let := Fintype.ofFinite B
  rw [averaging_apply_sum, map_smul, map_sum]
  congr 1
  have h : ∀ b : B, α a (α b u) = α ((⟨a, ha⟩ * b : B) : A) u := fun b => by
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [h]
  exact Equiv.sum_comp (Equiv.mulLeft (⟨a, ha⟩ : B)) (fun b : B => α (b : A) u)

theorem averaging_rep {B : Subgroup A} {a : A} (ha : a ∈ B) (u : U) :
    averaging α B (α a u) = averaging α B u := by
  let := Fintype.ofFinite B
  rw [averaging_apply_sum, averaging_apply_sum]
  congr 1
  have h : ∀ b : B, α b (α a u) = α ((b * ⟨a, ha⟩ : B) : A) u := fun b => by
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [h]
  exact Equiv.sum_comp (Equiv.mulRight (⟨a, ha⟩ : B)) (fun b : B => α (b : A) u)

theorem averaging_rep_comm (B : Subgroup A) (a : A) (u : U) :
    averaging α B (α a u) = α a (averaging α B u) := by
  let := Fintype.ofFinite B
  rw [averaging_apply_sum, averaging_apply_sum, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem averaging_mem_invariants (B : Subgroup A) (u : U) :
    averaging α B u ∈ Representation.invariants (α.comp B.subtype) := by
  rw [Representation.mem_invariants]
  intro b
  exact rep_averaging α b.2 u

theorem averaging_apply_of_mem_invariants {B : Subgroup A} (hB : (Nat.card B : K) ≠ 0) {u : U}
    (hu : u ∈ Representation.invariants (α.comp B.subtype)) : averaging α B u = u := by
  let := Fintype.ofFinite B
  rw [Representation.mem_invariants] at hu
  rw [averaging_apply_sum]
  have h : ∀ b : B, α b u = u := fun b => hu b
  simp only [h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hB, one_smul]

omit [Finite A] in
theorem rep_mem_invariants (B : Subgroup A) (a : A) {u : U}
    (hu : u ∈ Representation.invariants (α.comp B.subtype)) :
    α a u ∈ Representation.invariants (α.comp B.subtype) := by
  rw [Representation.mem_invariants] at hu ⊢
  intro b
  have h := hu b
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h ⊢
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, h]

end Averaging

section Hyperplane

theorem sup_eq_top_of_index_eq_prime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {D E : Subgroup G} (hD : D.index = p) (hE : E.index = p) (hDE : D ≠ E) : D ⊔ E = ⊤ := by
  have h := Subgroup.relIndex_mul_index (le_sup_left : D ≤ D ⊔ E)
  rw [hD] at h
  rcases (Nat.dvd_prime hp).mp (Dvd.intro_left _ h) with h1 | h1
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    rw [h1] at h
    have hrel : D.relIndex (D ⊔ E) = 1 :=
      Nat.eq_of_mul_eq_mul_right hp.pos (h.trans (one_mul p).symm)
    have hED : E ≤ D := le_sup_right.trans (Subgroup.relIndex_eq_one.mp hrel)
    have h2 := Subgroup.relIndex_mul_index hED
    rw [hD, hE] at h2
    have hrel2 : E.relIndex D = 1 :=
      Nat.eq_of_mul_eq_mul_right hp.pos (h2.trans (one_mul p).symm)
    exact hDE (le_antisymm (Subgroup.relIndex_eq_one.mp hrel2) hED)

theorem natCast_card_subgroup_ne_zero {G : Type*} [Group G] [Finite G] {K : Type*} [Field K]
    {p : ℕ} (hp : p.Prime) (hG : ∀ g : G, g ^ p = 1) (hK : (p : K) ≠ 0) (B : Subgroup G) :
    (Nat.card B : K) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hGp : IsPGroup p G := fun g => ⟨1, by rw [pow_one, hG g]⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hGp.to_subgroup B)
  rw [hk, Nat.cast_pow]
  exact pow_ne_zero k hK

variable {p : ℕ} {A : Type*} [CommGroup A] [Finite A] {K : Type*} [Field K]
  {U : Type*} [AddCommGroup U] [Module K U] (α : Representation K A U)

theorem averaging_top_eq_zero
    (hspan : Submodule.span K {v | ∃ (a : A) (u : U), α a u - u = v} = ⊤) :
    averaging α ⊤ = 0 := by
  have hle : Submodule.span K {v | ∃ (a : A) (u : U), α a u - u = v} ≤
      LinearMap.ker (averaging α ⊤) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, u, rfl⟩
    simp [averaging_rep α (Subgroup.mem_top a)]
  rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hle
  exact hle

theorem averaging_eq_zero_of_mem_invariants (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1)
    (hK : (p : K) ≠ 0) (hzero : averaging α ⊤ = 0) {D E : Subgroup A} (hD : D.index = p)
    (hE : E.index = p) (hDE : D ≠ E) {u : U}
    (hu : u ∈ Representation.invariants (α.comp D.subtype)) : averaging α E u = 0 := by
  set w := averaging α E u with hw
  have hwE : ∀ e ∈ E, α e w = w := fun e he => rep_averaging α he u
  have hwD : ∀ d ∈ D, α d w = w := by
    intro d hd
    rw [Representation.mem_invariants] at hu
    have h := hu ⟨d, hd⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    rw [hw, ← averaging_rep_comm, h]
  let S : Subgroup A :=
    { carrier := {a | α a w = w}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        calc α a⁻¹ w = α a⁻¹ (α a w) := by rw [ha]
          _ = w := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← sup_eq_top_of_index_eq_prime hp hD hE hDE]
    exact sup_le (fun d hd => hwD d hd) (fun e he => hwE e he)
  have hwtop : w ∈ Representation.invariants (α.comp (⊤ : Subgroup A).subtype) := by
    rw [Representation.mem_invariants]
    intro a
    have ha : (a : A) ∈ S := by
      rw [hS]
      exact Subgroup.mem_top _
    exact ha
  rw [← averaging_apply_of_mem_invariants α (natCast_card_subgroup_ne_zero hp hA hK ⊤) hwtop,
    hzero, LinearMap.zero_apply]

theorem iSupIndep_hyperplane_invariants (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1)
    (hK : (p : K) ≠ 0) (hzero : averaging α ⊤ = 0) :
    iSupIndep fun D : {D : Subgroup A // D.index = p} =>
      Representation.invariants (α.comp D.1.subtype) := by
  intro D
  rw [Submodule.disjoint_def]
  intro u huD huS
  have h1 : averaging α D.1 u = u :=
    averaging_apply_of_mem_invariants α (natCast_card_subgroup_ne_zero hp hA hK D.1) huD
  have h2 : (⨆ (E : {D : Subgroup A // D.index = p}) (_ : E ≠ D),
      Representation.invariants (α.comp E.1.subtype)) ≤ LinearMap.ker (averaging α D.1) := by
    refine iSup₂_le fun E hE => ?_
    intro v hv
    exact averaging_eq_zero_of_mem_invariants α hp hA hK hzero E.2 D.2
      (fun h => hE (Subtype.ext h)) hv
  rw [← h1]
  exact h2 huS

theorem iSup_hyperplane_invariants_eq_top (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1)
    (hK : (p : K) ≠ 0) (hzero : averaging α ⊤ = 0) :
    ⨆ D : {D : Subgroup A // D.index = p}, Representation.invariants (α.comp D.1.subtype) =
      ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set W := ⨆ D : {D : Subgroup A // D.index = p},
    Representation.invariants (α.comp D.1.subtype) with hW
  have hWinv : ∀ (a : A) (w : U), w ∈ W → α a w ∈ W := by
    intro a w hw
    have hle : W ≤ W.comap (α a) := by
      refine iSup_le fun D v hv => ?_
      exact Submodule.mem_iSup_of_mem D (rep_mem_invariants α D.1 a hv)
    exact hle hw
  have hWalg : ∀ (x : MonoidAlgebra K A) (w : U), w ∈ W → α.asAlgebraHom x w ∈ W := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of a =>
      intro w hw
      rw [Representation.asAlgebraHom_of]
      exact hWinv a w hw
    | add x y hx hy =>
      intro w hw
      rw [map_add, LinearMap.add_apply]
      exact add_mem (hx w hw) (hy w hw)
    | smul c x hx =>
      intro w hw
      rw [map_smul, LinearMap.smul_apply]
      exact W.smul_mem c (hx w hw)
  rw [eq_top_iff]
  intro u _
  by_contra hu
  let I : Ideal (MonoidAlgebra K A) :=
    { carrier := {x | α.asAlgebraHom x u ∈ W}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, map_add, LinearMap.add_apply] at hx hy ⊢
        exact add_mem hx hy
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, Module.End.mul_apply] at hx ⊢
        exact hWalg c _ hx }
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : MonoidAlgebra K A) ∈ I := htop ▸ Submodule.mem_top
    exact hu (by simpa [I] using h1)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have : M.IsPrime := hM.isPrime
  let χ : A →* (MonoidAlgebra K A ⧸ M)ˣ :=
    (Units.map (Ideal.Quotient.mk M).toMonoidHom).comp (MonoidAlgebra.of K A).toHomUnits
  have hχ : ∀ a, ((χ a : (MonoidAlgebra K A ⧸ M)ˣ) : MonoidAlgebra K A ⧸ M) =
      Ideal.Quotient.mk M (MonoidAlgebra.of K A a) := fun a => rfl
  have hrange : Nat.card χ.range ≤ p := by
    have hle : χ.range ≤ rootsOfUnity p (MonoidAlgebra K A ⧸ M) := by
      rintro _ ⟨a, rfl⟩
      rw [mem_rootsOfUnity, ← map_pow, hA, map_one]
    have : NeZero p := ⟨hp.ne_zero⟩
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity _ p)
  have hindex : χ.ker = ⊤ ∨ χ.ker.index = p := by
    have hApg : IsPGroup p A := fun a => ⟨1, by rw [pow_one, hA a]⟩
    obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hApg
    have hdvd := Subgroup.card_range_dvd χ
    rw [hr] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hjp : p ^ j ≤ p := hj ▸ hrange
    have hj1 : j ≤ 1 := by
      by_contra hcon
      have h1 : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
      nlinarith [hp.two_le]
    interval_cases j
    · left
      rw [← Subgroup.index_eq_one, Subgroup.index_ker, hj, pow_zero]
    · right
      rw [Subgroup.index_ker, hj, pow_one]
  set N := χ.ker with hN
  have hNcard : (Nat.card N : K) ≠ 0 := natCast_card_subgroup_ne_zero hp hA hK N
  let := Fintype.ofFinite N
  let ε : MonoidAlgebra K A := (Nat.card N : K)⁻¹ • ∑ n : N, MonoidAlgebra.of K A n
  have hεI : ε ∈ I := by
    change α.asAlgebraHom ε u ∈ W
    have hε : α.asAlgebraHom ε = averaging α N := by
      simp only [ε, averaging, map_smul, map_sum, Representation.asAlgebraHom_of]
    rw [hε]
    rcases hindex with htop | hp'
    · rw [htop, hzero]
      exact W.zero_mem
    · exact Submodule.mem_iSup_of_mem ⟨N, hp'⟩ (averaging_mem_invariants α N u)
  have hεM : Ideal.Quotient.mk M ε = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hεI)
  have hof : ∀ n : N, Ideal.Quotient.mk M (MonoidAlgebra.of K A n) = 1 := by
    intro n
    have h := congrArg (fun z : (MonoidAlgebra K A ⧸ M)ˣ => (z : MonoidAlgebra K A ⧸ M))
      (χ.mem_ker.mp n.2)
    simpa [hχ] using h
  have hsum : Ideal.Quotient.mk M (∑ n : N, MonoidAlgebra.of K A n) =
      (Nat.card N : MonoidAlgebra K A ⧸ M) := by
    rw [map_sum]
    simp only [hof, Finset.sum_const, Finset.card_univ, nsmul_one, Nat.card_eq_fintype_card]
  have hε1 : Ideal.Quotient.mk M ε = 1 := by
    calc Ideal.Quotient.mk M ε = algebraMap K _ (Nat.card N : K)⁻¹ *
          Ideal.Quotient.mk M (∑ n : N, MonoidAlgebra.of K A n) := by
          simp only [ε, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]
      _ = algebraMap K _ ((Nat.card N : K)⁻¹ * (Nat.card N : K)) := by
          rw [hsum, map_mul, map_natCast]
      _ = 1 := by rw [inv_mul_cancel₀ hNcard, map_one]
  exact one_ne_zero (hε1.symm.trans hεM)

theorem averaging_coeLinearMap [DecidableEq {D : Subgroup A // D.index = p}] (hp : p.Prime)
    (hA : ∀ a : A, a ^ p = 1) (hK : (p : K) ≠ 0) (hzero : averaging α ⊤ = 0)
    (x : ⨁ (D : {D : Subgroup A // D.index = p}), Representation.invariants (α.comp D.1.subtype))
    (E : {D : Subgroup A // D.index = p}) :
    averaging α E.1 (DirectSum.coeLinearMap
      (fun D : {D : Subgroup A // D.index = p} =>
        Representation.invariants (α.comp D.1.subtype)) x) = x E := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of D v =>
    rw [DirectSum.coeLinearMap_of]
    by_cases hDE : D = E
    · subst hDE
      rw [DirectSum.of_eq_same]
      exact averaging_apply_of_mem_invariants α (natCast_card_subgroup_ne_zero hp hA hK D.1) v.2
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hDE), ZeroMemClass.coe_zero]
      exact averaging_eq_zero_of_mem_invariants α hp hA hK hzero D.2 E.2
        (fun h => hDE (Subtype.ext h)) v.2
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, DirectSum.add_apply, Submodule.coe_add]

open _root_.Classical in
theorem coprime_hyperplane_module_decomposition (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1)
    (hK : (p : K) ≠ 0)
    (hspan : Submodule.span K {v | ∃ (a : A) (u : U), α a u - u = v} = ⊤) :
    Function.Bijective (DirectSum.coeLinearMap
        fun D : {D : Subgroup A // D.index = p} =>
          Representation.invariants (α.comp D.1.subtype)) ∧
    (∀ (D : {D : Subgroup A // D.index = p}) (a : A) (u : U),
        u ∈ Representation.invariants (α.comp D.1.subtype) →
          α a u ∈ Representation.invariants (α.comp D.1.subtype)) ∧
    ∀ (x : ⨁ (D : {D : Subgroup A // D.index = p}),
        Representation.invariants (α.comp D.1.subtype))
      (E : {D : Subgroup A // D.index = p}),
      (Nat.card E.1 : K)⁻¹ • ∑ᶠ e : E.1, α e (DirectSum.coeLinearMap
        (fun D : {D : Subgroup A // D.index = p} =>
          Representation.invariants (α.comp D.1.subtype)) x) = x E := by
  have hzero := averaging_top_eq_zero α hspan
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_hyperplane_invariants α hp hA hK hzero)
      (iSup_hyperplane_invariants_eq_top α hp hA hK hzero),
    fun D a u hu => rep_mem_invariants α D.1 a hu, fun x E => ?_⟩
  rw [← averaging_apply]
  exact averaging_coeLinearMap α hp hA hK hzero x E

end Hyperplane

end CFSG.RankThree.LocalRank
