module

public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.SimpleModule.Basic

public section

namespace CFSG.Quasithin.H13.L829N

open Module

section EField

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (X : Submodule A W) [IsSimpleModule A X]

noncomputable instance endFinite : Finite (Module.End A X) :=
  Finite.of_injective (fun f : Module.End A X => (f : X → X)) DFunLike.coe_injective

open Classical in
noncomputable instance endField : Field (Module.End A X) := by
  letI : DivisionRing (Module.End A X) := Module.End.instDivisionRing (R := A) (M := X)
  exact littleWedderburn (Module.End A X)

theorem charP_two_end : CharP (Module.End A X) 2 := by
  have hA2 : (2 : A) = 0 := by
    have h := congrArg (algebraMap (ZMod 2) A) (show (2 : ZMod 2) = 0 by decide)
    rw [map_zero, map_ofNat] at h
    exact h
  have hX2 : ∀ y : X, y + y = 0 := fun y => by
    rw [← two_smul A y, hA2, zero_smul]
  apply CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
  have h2 : (2 : Module.End A X) = 1 + 1 := one_add_one_eq_two.symm
  rw [h2]
  apply LinearMap.ext
  intro y
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply]
  exact hX2 y

theorem card_end_eq_two_pow : ∃ e : ℕ, 1 ≤ e ∧ Nat.card (Module.End A X) = 2 ^ e := by
  haveI := charP_two_end A X
  haveI : Fintype (Module.End A X) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card (Module.End A X) 2
  exact ⟨(n : ℕ), n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

private lemma exists_scalar_of_finrank_one_endField (hr : finrank (Module.End A X) X = 1) (c : A) :
    ∃ α : Module.End A X, ∀ y : X, c • y = α • y := by
  haveI : Module.Free (Module.End A X) X := Module.Free.of_divisionRing (Module.End A X) X
  obtain ⟨v, -, hv⟩ := (finrank_eq_one_iff' (K := Module.End A X) (V := X)).mp hr
  obtain ⟨α, hα⟩ := hv (c • v)
  refine ⟨α, fun y => ?_⟩
  obtain ⟨d, rfl⟩ := hv y
  calc c • (d • v) = d • (c • v) := (map_smul d c v).symm
    _ = d • (α • v) := by rw [hα]
    _ = (d * α) • v := (mul_smul d α v).symm
    _ = (α * d) • v := by rw [mul_comm]
    _ = α • (d • v) := mul_smul α d v

private lemma smul_comm_of_finrank_one_endField (hr : finrank (Module.End A X) X = 1)
    (a b : A) (x : X) : a • (b • x) = b • (a • x) := by
  obtain ⟨α, hα⟩ := exists_scalar_of_finrank_one_endField A X hr a
  obtain ⟨β, hβ⟩ := exists_scalar_of_finrank_one_endField A X hr b
  calc a • (b • x) = α • (b • x) := hα _
    _ = α • (β • x) := by rw [hβ x]
    _ = (α * β) • x := (mul_smul α β x).symm
    _ = (β * α) • x := by rw [mul_comm]
    _ = β • (α • x) := mul_smul β α x
    _ = β • (a • x) := by rw [hα x]
    _ = b • (a • x) := (hβ _).symm

theorem card_end_le
    (hX : Nat.card ↥X = 2 ∨ (Nat.card ↥X = 16 ∧ ∃ a ∈ A, ∃ b ∈ A, ∃ x ∈ X, a (b x) ≠ b (a x))) :
    Nat.card (Module.End A X) = 2 ∨ Nat.card (Module.End A X) = 4 := by
  obtain ⟨e, he1, hE⟩ := card_end_eq_two_pow A X
  haveI : Module.Finite (Module.End A X) X := Module.finite_iff_finite.mpr inferInstance
  have hcard : Nat.card X = 2 ^ (e * finrank (Module.End A X) X) := by
    rw [Module.natCard_eq_pow_finrank (K := Module.End A X), hE, pow_mul]
  rcases hX with h2 | ⟨h16, a, ha, b, hb, x, hx, hne⟩
  · have h' : (2 : ℕ) ^ (e * finrank (Module.End A X) X) = 2 ^ 1 := by
      rw [← hcard, h2, pow_one]
    have he : e * finrank (Module.End A X) X = 1 := Nat.pow_right_injective le_rfl h'
    have he1' : e = 1 := Nat.dvd_one.mp (Dvd.intro _ he)
    left
    simp [hE, he1']
  · have hr0 : finrank (Module.End A X) X ≠ 0 := by
      intro h0
      rw [h0, mul_zero, pow_zero] at hcard
      omega
    have h' : (2 : ℕ) ^ (e * finrank (Module.End A X) X) = 2 ^ 4 := by
      rw [← hcard, h16] <;> norm_num
    have hmul : e * finrank (Module.End A X) X = 4 := Nat.pow_right_injective le_rfl h'
    have hdvd : e ∣ 4 := Dvd.intro _ hmul
    have he4 : e ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases e
    · left
      simp [hE]
    · right
      simp [hE]
    · exfalso
      omega
    · exfalso
      have hr1 : finrank (Module.End A X) X = 1 := by omega
      have hcomm := congrArg Subtype.val
        (smul_comm_of_finrank_one_endField A X hr1 ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, hx⟩)
      exact hne hcomm

end EField

end CFSG.Quasithin.H13.L829N
