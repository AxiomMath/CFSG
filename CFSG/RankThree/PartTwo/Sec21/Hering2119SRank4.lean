module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SMat
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

section Rank4

variable {V : Type*} [AddCommGroup V] [Module F3 V] [Module.Finite F3 V]

theorem add_add_add_eq_zero_F3 (x : V) : x + x + x = 0 := by
  have h : (1 : F3) + 1 + 1 = 0 := by decide
  calc x + x + x = ((1 : F3) + 1 + 1) • x := by simp only [add_smul, one_smul]
    _ = 0 := by rw [h, zero_smul]

theorem eq_zero_of_eq_neg_F3 (x : V) (h : x = -x) : x = 0 := by
  have h2 : (2 : F3) • x = 0 := by
    rw [two_smul F3 x]
    calc x + x = x + -x := by rw [← h]
      _ = 0 := add_neg_cancel x
  rcases smul_eq_zero.mp h2 with h' | h'
  · exact absurd h' (by decide)
  · exact h'

theorem isCompl_ker_sub_one_ker_add_one (T : Module.End F3 V) (hT : T * T = 1) :
    IsCompl (LinearMap.ker (T - 1)) (LinearMap.ker (T + 1)) := by
  have hT' : ∀ x : V, T (T x) = x := fun x => by
    have h := congrArg (fun f : Module.End F3 V => f x) hT
    simpa using h
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hx'
    exact eq_zero_of_eq_neg_F3 x (hx.symm.trans hx')
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    rw [Submodule.mem_sup]
    refine ⟨-x - T x, ?_, T x - x, ?_, ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, map_sub,
        map_neg, hT']
      abel
    · rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
        add_eq_zero_iff_eq_neg, map_sub, hT']
      abel
    · have h4 : -x - T x + (T x - x) = -(x + x) := by abel
      rw [h4]
      exact neg_eq_iff_add_eq_zero.mpr (add_add_add_eq_zero_F3 x)

theorem even_finrank_of_mul_self_eq_neg_one {W : Type*} [AddCommGroup W] [Module F3 W]
    [Module.Finite F3 W] (J : Module.End F3 W) (hJ : J * J = -1) :
    Even (Module.finrank F3 W) := by
  rcases Nat.even_or_odd (Module.finrank F3 W) with he | ho
  · exact he
  · exfalso
    have h1 : LinearMap.det (J * J) = LinearMap.det J * LinearMap.det J :=
      map_mul LinearMap.det J J
    rw [hJ] at h1
    have h2 : LinearMap.det (-1 : Module.End F3 W) = (-1 : F3) ^ Module.finrank F3 W := by
      rw [← neg_one_smul F3 (1 : Module.End F3 W), LinearMap.det_smul, map_one, mul_one]
      rfl
    have h3 : (-1 : F3) ^ Module.finrank F3 W = -1 := ho.neg_one_pow
    rw [h2, h3] at h1
    have key : ∀ y : F3, y * y ≠ -1 := by decide
    exact key _ h1.symm

theorem finrank_le_of_injective_mapsTo {U W : Submodule F3 V} (f : Module.End F3 V)
    (hf : Function.Injective f) (h : ∀ x ∈ U, f x ∈ W) :
    Module.finrank F3 U ≤ Module.finrank F3 W := by
  have hle : U.map f ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  calc Module.finrank F3 U = Module.finrank F3 (U.map f) :=
        (Submodule.equivMapOfInjective f hf U).finrank_eq
    _ ≤ Module.finrank F3 W := Submodule.finrank_mono hle

theorem tau_mul_self_eq_one (A C : Module.End F3 V) (hA : A * A = -1) (hC : C * C = -1)
    (hAC : A * C = C * A) : (A * C) * (A * C) = 1 := by
  calc (A * C) * (A * C) = A * ((C * A) * C) := by simp only [mul_assoc]
    _ = A * ((A * C) * C) := by rw [← hAC]
    _ = (A * A) * (C * C) := by simp only [mul_assoc]
    _ = 1 := by rw [hA, hC, neg_one_mul, neg_neg]

theorem B_mul_tau_eq (A B C : Module.End F3 V) (hAB : A * B = -(B * A))
    (hBC : B * C = C * B) : B * (A * C) = -((A * C) * B) := by
  have hBA : B * A = -(A * B) := by rw [hAB, neg_neg]
  calc B * (A * C) = (B * A) * C := (mul_assoc B A C).symm
    _ = -((A * B) * C) := by rw [hBA, neg_mul]
    _ = -(A * (B * C)) := by rw [mul_assoc]
    _ = -(A * (C * B)) := by rw [hBC]
    _ = -((A * C) * B) := by rw [mul_assoc]

theorem tau_mul_A_eq (A C : Module.End F3 V) (hA : A * A = -1) (hAC : A * C = C * A) :
    (A * C) * A = A * (A * C) := by
  calc (A * C) * A = C * (A * A) := by rw [hAC, mul_assoc]
    _ = -C := by rw [hA, mul_neg, mul_one]
    _ = (A * A) * C := by rw [hA, neg_one_mul]
    _ = A * (A * C) := mul_assoc A A C

theorem B_injective_of_mul_self (B : Module.End F3 V) (hB : B * B = -1) :
    Function.Injective B := by
  have hBB : ∀ z : V, B (B z) = -z := fun z => by
    have h := congrArg (fun f : Module.End F3 V => f z) hB
    simpa using h
  intro x y hxy
  have h2 := congrArg B hxy
  rw [hBB, hBB] at h2
  exact neg_inj.mp h2

theorem rank_four (A B C : Module.End F3 V) (hA : A * A = -1) (hB : B * B = -1)
    (hC : C * C = -1) (hAB : A * B = -(B * A)) (hAC : A * C = C * A) (hBC : B * C = C * B) :
    4 ∣ Module.finrank F3 V ∧
      2 * Module.finrank F3 (LinearMap.ker (A * C - 1)) = Module.finrank F3 V := by
  have hτ : (A * C) * (A * C) = 1 := tau_mul_self_eq_one A C hA hC hAC
  have hBτ : B * (A * C) = -((A * C) * B) := B_mul_tau_eq A B C hAB hBC
  have hAτ : (A * C) * A = A * (A * C) := tau_mul_A_eq A C hA hAC
  have hBinj : Function.Injective B := B_injective_of_mul_self B hB
  have hsplit : Module.finrank F3 (LinearMap.ker (A * C - 1)) +
      Module.finrank F3 (LinearMap.ker (A * C + 1)) = Module.finrank F3 V :=
    Submodule.finrank_add_eq_of_isCompl (isCompl_ker_sub_one_ker_add_one (A * C) hτ)
  have hBP : ∀ x ∈ LinearMap.ker (A * C - 1), B x ∈ LinearMap.ker (A * C + 1) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
    have h0 := congrArg (fun f : Module.End F3 V => f x) hBτ
    have h : B ((A * C) x) = -((A * C) (B x)) := h0
    rw [hx] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have hBM : ∀ x ∈ LinearMap.ker (A * C + 1), B x ∈ LinearMap.ker (A * C - 1) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have h0 := congrArg (fun f : Module.End F3 V => f x) hBτ
    have h : B ((A * C) x) = -((A * C) (B x)) := h0
    rw [hx, map_neg] at h
    exact (neg_inj.mp h).symm
  have hPp_le : Module.finrank F3 (LinearMap.ker (A * C - 1)) ≤
      Module.finrank F3 (LinearMap.ker (A * C + 1)) :=
    finrank_le_of_injective_mapsTo B hBinj hBP
  have hPm_le : Module.finrank F3 (LinearMap.ker (A * C + 1)) ≤
      Module.finrank F3 (LinearMap.ker (A * C - 1)) :=
    finrank_le_of_injective_mapsTo B hBinj hBM
  have hAP : ∀ x ∈ LinearMap.ker (A * C - 1), A x ∈ LinearMap.ker (A * C - 1) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx ⊢
    have h : (A * C) (A x) = A ((A * C) x) := by
      calc (A * C) (A x) = ((A * C) * A) x := (Module.End.mul_apply (A * C) A x).symm
        _ = (A * (A * C)) x := by rw [hAτ]
        _ = A ((A * C) x) := Module.End.mul_apply A (A * C) x
    rw [h, hx]
  have hJJ : (A.restrict hAP) * (A.restrict hAP) = -1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun f : Module.End F3 V => f (x : V)) hA
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] at h
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply,
      LinearMap.coe_restrict_apply, Submodule.coe_neg]
    exact h
  have hEven : Even (Module.finrank F3 (LinearMap.ker (A * C - 1))) :=
    even_finrank_of_mul_self_eq_neg_one (A.restrict hAP) hJJ
  obtain ⟨k, hk⟩ := hEven
  exact ⟨by omega, by omega⟩

end Rank4

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
