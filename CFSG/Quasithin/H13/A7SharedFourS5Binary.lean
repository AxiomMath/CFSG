module

public import CFSG.Quasithin.H13.A7SharedFourS5
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.A7

open Polynomial Module

theorem commute_aeval_of_commute {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {t x : A} (h : Commute t x) (p : R[X]) : Commute t (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_right hq
  | monomial n r =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right r t).mul_right (h.pow_right n)

theorem irreducible_X_sq_add_X_add_one_zmod_two :
    Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    rw [this]
    decide
  · intro x hx
    rw [IsRoot, eval_add, eval_add, eval_pow, eval_X, eval_one] at hx
    revert hx
    fin_cases x <;> decide

theorem A7_small_binary_S5_representations_kill_A5 {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W ≤ 6)
    (J : Module.End (ZMod 2) W) (hJ : J ^ 2 + J + 1 = 0)
    (β : Equiv.Perm (Fin 5) →* (W ≃ₗ[ZMod 2] W)) (hβJ : ∀ g w, β g (J w) = J (β g w)) :
    ∀ a ∈ alternatingGroup (Fin 5), β a = 1 := by
  classical
  set f : (ZMod 2)[X] := X ^ 2 + X + 1 with hfdef
  have hfirr : Irreducible f := irreducible_X_sq_add_X_add_one_zmod_two
  have : Fact (Irreducible f) := ⟨hfirr⟩
  have hf0 : f ≠ 0 := hfirr.ne_zero
  have hfdeg : f.natDegree = 2 := by
    rw [hfdef]
    compute_degree!
  set pb := AdjoinRoot.powerBasis hf0 with hpb
  have hk2 : finrank (ZMod 2) (AdjoinRoot f) = 2 := by
    rw [pb.finrank, hpb, AdjoinRoot.powerBasis_dim, hfdeg]
  have : Module.Finite (ZMod 2) (AdjoinRoot f) := pb.finite
  have : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod 2)
  let : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hk : Fintype.card (AdjoinRoot f) = 4 := by
    rw [← FiniteField.pow_finrank_eq_card 2, hk2]
    norm_num
  have hJf : aeval J f = 0 := by
    rw [hfdef, map_add, map_add, map_pow, aeval_X, map_one, hJ]
  have hI : ∀ a : (ZMod 2)[X], a ∈ Ideal.span {f} → aeval J a = 0 := by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hJf, mul_zero]
  set φ : AdjoinRoot f →ₐ[ZMod 2] Module.End (ZMod 2) W :=
    Ideal.Quotient.liftₐ (Ideal.span {f}) (aeval J) hI with hφ
  have hφmk : ∀ p : (ZMod 2)[X], φ (AdjoinRoot.mk f p) = aeval J p := fun _ => rfl
  let : Module (AdjoinRoot f) W := Module.compHom W φ.toRingHom
  have hsmul : ∀ (x : AdjoinRoot f) (w : W), x • w = φ x w := fun _ _ => rfl
  have : IsScalarTower (ZMod 2) (AdjoinRoot f) W := ⟨fun r x w => by
    rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  have : FiniteDimensional (AdjoinRoot f) W :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) (AdjoinRoot f) W
  have hrank := Module.finrank_mul_finrank (ZMod 2) (AdjoinRoot f) W
  rw [hk2] at hrank
  have hcomm : ∀ g (x : AdjoinRoot f) (w : W), β g (φ x w) = φ x (β g w) := by
    intro g x w
    induction x using AdjoinRoot.induction_on with
    | ih p =>
      rw [hφmk]
      have hc : Commute ((β g : W →ₗ[ZMod 2] W)) J := LinearMap.ext fun v => hβJ g v
      exact LinearMap.congr_fun (commute_aeval_of_commute hc p).eq w
  let β' : Equiv.Perm (Fin 5) →* (W ≃ₗ[AdjoinRoot f] W) :=
    { toFun := fun g =>
        { toFun := β g
          invFun := (β g).symm
          map_add' := (β g).map_add
          map_smul' := fun x w => hcomm g x w
          left_inv := (β g).left_inv
          right_inv := (β g).right_inv }
      map_one' := by
        ext w
        show β 1 w = w
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        ext w
        show β (g * h) w = β g (β h w)
        rw [map_mul]
        rfl }
  have hmain := A7_small_F4_S5_representations_kill_A5 hk (by omega) β'
  intro a ha
  ext w
  exact LinearEquiv.congr_fun (hmain a ha) w

end CFSG.Quasithin.H13.A7
