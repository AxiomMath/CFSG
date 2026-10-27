module

public import CFSG.Quasithin.Background.SimsG4Defs
public import Mathlib.LinearAlgebra.Trace

public section

namespace CFSG.Quasithin.SimsG4

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

section Polar

theorem polar_self_eq_zero [CharP K 2] (Q : QuadraticForm K W) (x : W) :
    QuadraticMap.polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

theorem polar_map_of_isometry (Q : QuadraticForm K W) {g : W ≃ₗ[K] W}
    (hg : ∀ x, Q (g x) = Q x) (x y : W) :
    QuadraticMap.polar Q (g x) (g y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, hg]

theorem polarBilin_flip_ne_zero (Q : QuadraticForm K W)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) {r : W} (hr : r ≠ 0) :
    (QuadraticMap.polarBilin Q).flip r ≠ 0 := by
  intro h
  apply hr
  refine hnd r fun y => ?_
  rw [QuadraticMap.polar_comm]
  exact LinearMap.congr_fun h y

end Polar

section Index

theorem eq_of_index_two_le {Γ : Type*} [Group Γ] {Ω G O : Subgroup Γ} (hΩG : Ω ≤ G)
    (hGO : G ≤ O) (hidx : (Ω.subgroupOf O).index = 2) (hG : ¬ G ≤ Ω) : G = O := by
  have hmul := Subgroup.relIndex_mul_relIndex Ω G O hΩG hGO
  rw [show Ω.relIndex O = 2 from hidx] at hmul
  have h1 : Ω.relIndex G ≠ 1 := fun h => hG (Subgroup.relIndex_eq_one.mp h)
  have h2 : G.relIndex O = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hmul) with h | h
    · exact absurd h h1
    · rw [h] at hmul
      omega
  exact le_antisymm hGO (Subgroup.relIndex_eq_one.mp h2)

end Index

section Refl

variable [CharP K 2]

theorem reflMap_involutive (Q : QuadraticForm K W) (r : W) :
    Function.Involutive fun x : W => x + QuadraticMap.polar Q x r • r := by
  intro x
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, polar_self_eq_zero,
    smul_eq_mul, mul_zero, add_zero]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

@[expose] def reflK (Q : QuadraticForm K W) (r : W) : W ≃ₗ[K] W :=
  LinearEquiv.ofInvolutive (LinearMap.id + ((QuadraticMap.polarBilin Q).flip r).smulRight r)
    (reflMap_involutive Q r)

theorem reflK_apply (Q : QuadraticForm K W) (r x : W) :
    reflK Q r x = x + QuadraticMap.polar Q x r • r :=
  rfl

theorem reflK_reflK (Q : QuadraticForm K W) (r x : W) : reflK Q r (reflK Q r x) = x :=
  reflMap_involutive Q r x

theorem reflK_mul_self (Q : QuadraticForm K W) (r : W) : reflK Q r * reflK Q r = 1 :=
  LinearEquiv.ext fun x => reflK_reflK Q r x

theorem reflK_isometry (Q : QuadraticForm K W) {r : W} (hr : Q r = 1) (x : W) :
    Q (reflK Q r x) = Q x := by
  rw [reflK_apply, QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul,
    QuadraticMap.polar_smul_right, hr, smul_eq_mul, smul_eq_mul, mul_one, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

theorem reflK_sub_id (Q : QuadraticForm K W) (r : W) :
    ((reflK Q r : W ≃ₗ[K] W) : W →ₗ[K] W) - LinearMap.id =
      ((QuadraticMap.polarBilin Q).flip r).smulRight r := by
  ext x
  simp [reflK_apply]

theorem isTransv_reflK (Q : QuadraticForm K W)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) {r : W} (hr : r ≠ 0) :
    IsTransv (reflK Q r) := by
  refine ⟨?_, ?_⟩
  · rw [reflK_sub_id, LinearMap.range_smulRight_apply (polarBilin_flip_ne_zero Q hnd hr),
      finrank_span_singleton hr]
  · rw [reflK_sub_id]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.flip_apply,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_smul_left, polar_self_eq_zero,
      smul_eq_mul, mul_zero, zero_smul, LinearMap.zero_apply]

theorem commSpace_reflK (Q : QuadraticForm K W)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) {r : W} (hr : r ≠ 0) :
    commSpace (reflK Q r) = Submodule.span K {r} := by
  rw [commSpace, reflK_sub_id, LinearMap.range_smulRight_apply (polarBilin_flip_ne_zero Q hnd hr)]

end Refl

section Trace

variable [CharP K 2]

theorem reflK_mul_eq (Q : QuadraticForm K W) (r s : W) :
    ((reflK Q r * reflK Q s : W ≃ₗ[K] W) : W →ₗ[K] W) =
      LinearMap.id + ((QuadraticMap.polarBilin Q).flip s).smulRight s +
        ((QuadraticMap.polarBilin Q).flip r).smulRight r +
          (QuadraticMap.polar Q s r • (QuadraticMap.polarBilin Q).flip s).smulRight r := by
  ext x
  simp only [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_apply, LinearEquiv.coe_coe,
    reflK_apply, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, LinearMap.smul_apply,
    QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, smul_eq_mul, add_smul, mul_smul]
  rw [smul_comm (QuadraticMap.polar Q x s) (QuadraticMap.polar Q s r) r]
  abel

theorem trace_reflK_mul [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hev : Even (Module.finrank K W)) (r s : W) :
    LinearMap.trace K W ((reflK Q r * reflK Q s : W ≃ₗ[K] W) : W →ₗ[K] W) =
      QuadraticMap.polar Q r s ^ 2 := by
  have hdim : (Module.finrank K W : K) = 0 :=
    (CharP.cast_eq_zero_iff K 2 _).mpr (even_iff_two_dvd.mp hev)
  rw [reflK_mul_eq, map_add, map_add, map_add, LinearMap.trace_id, LinearMap.trace_smulRight,
    LinearMap.trace_smulRight, LinearMap.trace_smulRight, hdim]
  simp only [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, LinearMap.smul_apply,
    polar_self_eq_zero, smul_eq_mul, zero_add]
  rw [QuadraticMap.polar_comm Q s r, sq]

theorem mem_of_sq_mem_subfield [Finite K] (K₁ : Subfield K) {z : K} (hz : z ^ 2 ∈ K₁) :
    z ∈ K₁ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  have hq : z ^ (2 ^ (f : ℕ)) = z := by
    have := FiniteField.pow_card z
    rwa [hcard] at this
  obtain ⟨g, hg⟩ : ∃ g, (f : ℕ) = g + 1 := ⟨(f : ℕ) - 1, by have := f.pos; omega⟩
  have h : z = (z ^ 2) ^ (2 ^ g) := by
    rw [← pow_mul, ← pow_succ', ← hg]
    exact hq.symm
  rw [h]
  exact K₁.pow_mem hz _

end Trace

end CFSG.Quasithin.SimsG4
