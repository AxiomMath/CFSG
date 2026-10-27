module

public import CFSG.Quasithin.Vol2.GoldschmidtA128LinChar
public import Mathlib.RingTheory.PiTensorProduct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.A128.Lin

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {n : ℕ}

structure IsRep (R : (Fin n → ZMod 2) → Module.End F V) : Prop where
  rep_zero : R 0 = 1
  rep_add : ∀ x y, R (x + y) = R x * R y

variable (R : (Fin n → ZMod 2) → Module.End F V)

def proj (l : Fin n → ZMod 2) : Module.End F V :=
  ((2 : F) ^ n)⁻¹ • ∑ x, chi F l x • R x

@[expose] def IsWeight (l : Fin n → ZMod 2) (w : V) : Prop :=
  ∀ y, R y w = chi F l y • w

variable {R}

theorem IsRep.sum_proj (hR : IsRep R) (h2 : (2 : F) ≠ 0) : ∑ l, proj R l = 1 := by
  have h2n : (2 : F) ^ n ≠ 0 := pow_ne_zero n h2
  unfold proj
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_chi_left h2, ite_smul, zero_smul]
  simp [hR.rep_zero, h2n]

theorem IsRep.mul_proj (hR : IsRep R) (y l : Fin n → ZMod 2) :
    R y * proj R l = chi F l y • proj R l := by
  have key : ∑ x, chi F l x • R (y + x) = chi F l y • ∑ x, chi F l x • R x := by
    have h := Equiv.sum_comp (Equiv.addLeft y) fun x => chi F l x • R (y + x)
    simp only [Equiv.coe_addLeft, vec_add_add_self] at h
    rw [← h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [chi_add_right, mul_smul]
  unfold proj
  rw [mul_smul_comm, smul_comm, Finset.mul_sum]
  congr 2
  simp_rw [mul_smul_comm, ← hR.rep_add]
  exact key

theorem IsRep.isWeight_proj (hR : IsRep R) (l : Fin n → ZMod 2) (v : V) :
    IsWeight R l (proj R l v) := fun y => by
  have h := congrArg (fun T => T v) (hR.mul_proj y l)
  simpa using h

theorem proj_apply_of_isWeight (h2 : (2 : F) ≠ 0) {l l' : Fin n → ZMod 2} {w : V}
    (hw : IsWeight R l w) : proj R l' w = if l' = l then w else 0 := by
  have h2n : (2 : F) ^ n ≠ 0 := pow_ne_zero n h2
  have hsum : ∑ x, chi F l' x • R x w = (∑ x, chi F (l' + l) x) • w := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hw x, smul_smul, chi_add_left]
  unfold proj
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  simp_rw [LinearMap.smul_apply]
  rw [hsum, sum_chi_right h2]
  by_cases h : l' = l
  · subst h
    simp only [vec_add_self, ↓reduceIte, smul_smul, inv_mul_cancel₀ h2n, one_smul]
  · have h' : ¬ (l' + l = 0) := fun h'' => h (vec_add_eq_zero_iff.mp h'')
    simp only [h, h', ↓reduceIte, zero_smul, smul_zero]

theorem linearIndependent_of_weights (h2 : (2 : F) ≠ 0) {ι : Type*} [Fintype ι]
    {lam : ι → Fin n → ZMod 2} (hlam : Function.Injective lam) {w : ι → V} (hw0 : ∀ i, w i ≠ 0)
    (hw : ∀ i, IsWeight R (lam i) (w i)) : LinearIndependent F w := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (proj R (lam i)) hg
  rw [map_sum, map_zero] at h
  simp_rw [map_smul, proj_apply_of_isWeight h2 (hw _), hlam.eq_iff, smul_ite, smul_zero] at h
  rw [Finset.sum_ite_eq] at h
  simp only [Finset.mem_univ, ↓reduceIte] at h
  exact (smul_eq_zero.mp h).resolve_right (hw0 i)

end CFSG.Quasithin.Vol2.A128.Lin
