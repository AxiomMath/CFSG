module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6LinDefs
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.QTwoD6

open Module

@[expose] def epsVec : Fin 6 → V7 :=
  ![![0, 1, 1, 1, 1, 2, 2], ![0, 0, 1, 1, 1, 2, 2], ![0, 0, 0, 1, 1, 2, 2],
    ![0, 0, 0, 0, 1, 2, 2], ![0, 0, 0, 0, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 2]]

theorem qd6g_simple_apply (j : Fin 6) (v : V7) :
    simpleD6 j v = v - (∑ i : Fin 6, (cartanD6 i j : ZMod 3) * v i.succ) • hvec j := by
  rw [simpleD6, Module.reflection_apply]
  rfl

theorem qd6g_simple_e0 (j : Fin 6) : simpleD6 j e0 = e0 := by
  rw [qd6g_simple_apply]
  have h : (∑ i : Fin 6, (cartanD6 i j : ZMod 3) * e0 i.succ) = 0 := by simp [e0]
  rw [h, zero_smul, sub_zero]

theorem qd6g_hvec_eq (i : Fin 6) :
    hvec i = (if i = 5 then epsVec 4 + epsVec 5 else epsVec i - epsVec (i + 1)) := by
  fin_cases i <;> decide +kernel

theorem qd6g_hvec_mem (i : Fin 6) :
    hvec i ∈ Submodule.span (ZMod 3) (Set.range epsVec) := by
  rw [qd6g_hvec_eq i]
  by_cases h : i = 5
  · rw [if_pos h]
    exact add_mem (Submodule.subset_span ⟨4, rfl⟩) (Submodule.subset_span ⟨5, rfl⟩)
  · rw [if_neg h]
    exact sub_mem (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨i + 1, rfl⟩)

theorem qd6g_span_eq_top :
    Submodule.span (ZMod 3) (insert e0 (Set.range epsVec)) = ⊤ := by
  have hle : Submodule.span (ZMod 3) (Set.range (Pi.basisFun (ZMod 3) (Fin 7))) ≤
      Submodule.span (ZMod 3) (insert e0 (Set.range epsVec)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    rw [Pi.basisFun_apply]
    refine Fin.cases ?_ (fun i => ?_) k
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.span_mono (Set.subset_insert _ _) (qd6g_hvec_mem i)
  rw [(Pi.basisFun (ZMod 3) (Fin 7)).span_eq] at hle
  exact top_le_iff.mp hle

theorem qd6g_ext {f g : V7 →ₗ[ZMod 3] V7}
    (h0 : f e0 = g e0) (h : ∀ a, f (epsVec a) = g (epsVec a)) : f = g :=
  LinearMap.ext_on qd6g_span_eq_top (by
    rintro x (rfl | ⟨a, rfl⟩)
    · exact h0
    · exact h a)

theorem qd6g_linEquiv_ext {f g : V7 ≃ₗ[ZMod 3] V7}
    (h0 : f e0 = g e0) (h : ∀ a, f (epsVec a) = g (epsVec a)) : f = g :=
  LinearEquiv.ext fun v =>
    congr_arg (fun φ : V7 →ₗ[ZMod 3] V7 => φ v) (qd6g_ext h0 h)

theorem qd6g_simple_eps_adj (i : Fin 5) (a : Fin 6) :
    simpleD6 i.castSucc (epsVec a) = epsVec (Equiv.swap i.castSucc i.succ a) := by
  fin_cases i <;> fin_cases a <;> rw [qd6g_simple_apply] <;> decide +kernel

theorem qd6g_simple5_eps (a : Fin 6) :
    simpleD6 5 (epsVec a) =
      (if a = 4 then -epsVec 5 else if a = 5 then -epsVec 4 else epsVec a) := by
  fin_cases a <;> rw [qd6g_simple_apply] <;> decide +kernel

theorem qd6g_f45_e0 : (simpleD6 4 * simpleD6 5) e0 = e0 := by
  change simpleD6 4 (simpleD6 5 e0) = e0
  rw [qd6g_simple_e0, qd6g_simple_e0]

theorem qd6g_f45_4 : (simpleD6 4 * simpleD6 5) (epsVec 4) = -epsVec 4 := by
  change simpleD6 4 (simpleD6 5 (epsVec 4)) = -epsVec 4
  rw [qd6g_simple5_eps]
  decide +kernel

theorem qd6g_f45_5 : (simpleD6 4 * simpleD6 5) (epsVec 5) = -epsVec 5 := by
  change simpleD6 4 (simpleD6 5 (epsVec 5)) = -epsVec 5
  rw [qd6g_simple5_eps]
  decide +kernel

theorem qd6g_f45_of_ne (c : Fin 6) (h4 : c ≠ 4) (h5 : c ≠ 5) :
    (simpleD6 4 * simpleD6 5) (epsVec c) = epsVec c := by
  change simpleD6 4 (simpleD6 5 (epsVec c)) = epsVec c
  fin_cases c <;> simp_all [qd6g_simple5_eps] <;> decide +kernel

@[expose] noncomputable def qd6g_tauLin : V7 →ₗ[ZMod 3] V7 where
  toFun v := v + (v 6 - v 5) • epsVec 5
  map_add' v w := by
    ext k
    fin_cases k <;> simp [Pi.add_apply] <;> ring
  map_smul' c v := by
    ext k
    fin_cases k <;> simp [Pi.smul_apply] <;> ring

theorem qd6g_tauLin_invol : qd6g_tauLin.comp qd6g_tauLin = LinearMap.id := by
  apply LinearMap.ext
  decide +kernel

@[expose] noncomputable def qd6g_tau : V7 ≃ₗ[ZMod 3] V7 where
  toFun := qd6g_tauLin
  map_add' := qd6g_tauLin.map_add
  map_smul' := qd6g_tauLin.map_smul
  invFun := qd6g_tauLin
  left_inv := fun v => LinearMap.ext_iff.mp qd6g_tauLin_invol v
  right_inv := fun v => LinearMap.ext_iff.mp qd6g_tauLin_invol v

theorem qd6g_tau_apply (v : V7) : qd6g_tau v = v + (v 6 - v 5) • epsVec 5 := rfl

theorem qd6g_tau_e0 : qd6g_tau e0 = e0 := by
  rw [qd6g_tau_apply]
  have h : e0 6 - e0 5 = 0 := by decide +kernel
  rw [h, zero_smul, add_zero]

theorem qd6g_tau_eps (a : Fin 6) :
    qd6g_tau (epsVec a) = (if a = 5 then -epsVec 5 else epsVec a) := by
  rw [qd6g_tau_apply]
  fin_cases a <;> decide +kernel

theorem qd6g_tau_hvec (i : Fin 6) : qd6g_tau (hvec i) = hvec (swapD6 i) := by
  rw [qd6g_tau_apply]
  fin_cases i <;> decide +kernel

@[expose] noncomputable def qd6g_kappa (lam : ZMod 3) (hlam : lam ≠ 0) : V7 ≃ₗ[ZMod 3] V7 where
  toFun v := Function.update v 0 (lam⁻¹ * v 0)
  invFun v := Function.update v 0 (lam * v 0)
  left_inv v := by
    ext k
    by_cases hk : k = 0
    · subst hk
      simp only [Function.update_self]
      rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
    · simp [Function.update, hk]
  right_inv v := by
    ext k
    by_cases hk : k = 0
    · subst hk
      simp only [Function.update_self]
      rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
    · simp [Function.update, hk]
  map_add' v w := by
    ext k
    by_cases hk : k = 0
    · subst hk; simp [Pi.add_apply, Function.update]; ring
    · simp [Pi.add_apply, Function.update, hk]
  map_smul' c v := by
    ext k
    by_cases hk : k = 0
    · subst hk; simp [Pi.smul_apply, Function.update]; ring
    · simp [Pi.smul_apply, Function.update, hk]

theorem qd6g_kappa_apply (lam : ZMod 3) (hlam : lam ≠ 0) (v : V7) (k : Fin 7) :
    qd6g_kappa lam hlam v k = if k = 0 then lam⁻¹ * v 0 else v k := by
  by_cases hk : k = 0
  · subst hk; simp [qd6g_kappa, Function.update]
  · simp [qd6g_kappa, Function.update, hk]

theorem qd6g_kappa_e0 (lam : ZMod 3) (hlam : lam ≠ 0) :
    qd6g_kappa lam hlam e0 = lam⁻¹ • e0 := by
  ext k
  rw [qd6g_kappa_apply]
  fin_cases k <;> simp [e0, Pi.smul_apply]

theorem qd6g_kappa_fix (lam : ZMod 3) (hlam : lam ≠ 0) (v : V7) (hv : v 0 = 0) :
    qd6g_kappa lam hlam v = v := by
  ext k
  rw [qd6g_kappa_apply]
  by_cases h : k = 0 <;> simp [h, hv]

theorem qd6g_kappa_eps (lam : ZMod 3) (hlam : lam ≠ 0) (a : Fin 6) :
    qd6g_kappa lam hlam (epsVec a) = epsVec a := by
  apply qd6g_kappa_fix
  fin_cases a <;> decide +kernel

theorem qd6g_kappa_hvec (lam : ZMod 3) (hlam : lam ≠ 0) (i : Fin 6) :
    qd6g_kappa lam hlam (hvec i) = hvec i := by
  apply qd6g_kappa_fix
  simp [hvec]

end CFSG.StandardType.QTwoD6

end
