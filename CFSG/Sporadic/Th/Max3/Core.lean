
module

import all CFSG.Sporadic.Th.Max3.CoreBase
public import CFSG.Sporadic.Th.Max3.CoreBase1
import all CFSG.Sporadic.Th.Max3.CoreBase1

public import CFSG.Sporadic.Th.Max3.Relations

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Certificates

theorem symplectic_rel :
    ExtraspecialNF.Rel z q c :=
  ⟨z_mul_self, z_mul_q, q_mul_self, q_mul_q⟩

theorem nf_injective_generic :
    Function.Injective (Function.uncurry (ExtraspecialNF.nf z q)) :=
  fun _ _ h => nf_injective h

theorem mem_Q_iff
    {g : J} : g ∈ Q ↔ ∃ (s : ZMod 2) (v : Fin 8 → ZMod 2), nf s v = g :=
  ExtraspecialNF.mem_closure_iff symplectic_rel

theorem card_Q :
    Nat.card Q = 512 := by
  have h := ExtraspecialNF.card_closure symplectic_rel nf_injective_generic
  rw [show (2 : ℕ) ^ (8 + 1) = 512 by norm_num] at h
  exact h

theorem center_Q :
    Subgroup.center Q = (Subgroup.zpowers z).subgroupOf Q :=
  ExtraspecialNF.center_eq symplectic_rel nf_injective_generic c_nondegenerate

theorem card_center_Q :
    Nat.card (Subgroup.center Q) = 2 :=
  ExtraspecialNF.card_center symplectic_rel nf_injective_generic c_nondegenerate

theorem isExtraspecialPGroup_Q :
    IsExtraspecialPGroup 2 Q :=
  ExtraspecialNF.isExtraspecialPGroup symplectic_rel nf_injective_generic c_nondegenerate
    (by norm_num)

noncomputable def theta :
    Multiplicative (Fin 8 → ZMod 2) ≃* Q ⧸ Subgroup.center Q :=
  ExtraspecialNF.thetaEquiv symplectic_rel nf_injective_generic c_nondegenerate

theorem nf_sq
    (s : ZMod 2) (v : Fin 8 → ZMod 2) :
    nf s v ^ 2 = z ^ (ExtraspecialNF.qf c v).val :=
  ExtraspecialNF.nf_sq symplectic_rel (fun i j => c_symm j i) s v

private theorem prod_nf
    (l : List (ZMod 2 × (Fin 8 → ZMod 2))) :
    ∃ t, (l.map fun p => nf p.1 p.2).prod = nf t (l.map Prod.snd).sum := by
  induction l with
  | nil => exact ⟨0, by simp [nf_eq_generic, ExtraspecialNF.nf_zero_zero]⟩
  | cons p l ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨p.1 + t + ExtraspecialNF.collect c p.2 (l.map Prod.snd).sum, ?_⟩
    rw [List.map_cons, List.prod_cons, ht, List.map_cons, List.sum_cons]
    exact ExtraspecialNF.nf_mul_nf symplectic_rel _ _ _ _

theorem conj_nf_zero
    (g : J) (a : Fin 8 → ZMod 2) (b : Fin 8 → Fin 8 → ZMod 2)
    (hg : ∀ i, g * q i * g⁻¹ = nf (a i) (b i)) (v : Fin 8 → ZMod 2) :
    ∃ t, g * nf 0 v * g⁻¹ = nf t fun k => ∑ i, v i * b i k := by
  have e : nf 0 v = (List.ofFn fun i => q i ^ (v i).val).prod := by
    simp [nf]
  have h1 : g * nf 0 v * g⁻¹ =
      (List.ofFn fun i => nf (v i * a i) fun k => v i * b i k).prod := by
    have := map_list_prod (MulAut.conj g) (List.ofFn fun i => q i ^ (v i).val)
    simp only [MulAut.conj_apply, List.map_ofFn] at this
    rw [e, this]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp only [Function.comp_apply]
    rw [map_pow, MulAut.conj_apply, hg i, nf_pow_val]
  obtain ⟨t, ht⟩ := prod_nf (List.ofFn fun i => (v i * a i, fun k => v i * b i k))
  have hmap : (List.ofFn fun i => (v i * a i, fun k => v i * b i k)).map
      (fun p => nf p.1 p.2) = List.ofFn fun i => nf (v i * a i) fun k => v i * b i k := by
    rw [List.map_ofFn]
    rfl
  have hsum : ((List.ofFn fun i => (v i * a i, fun k => v i * b i k)).map Prod.snd).sum =
      fun k => ∑ i, v i * b i k := by
    rw [List.map_ofFn, List.sum_ofFn]
    funext k
    simp [Finset.sum_apply]
  rw [hmap, hsum] at ht
  exact ⟨t, h1.trans ht⟩

theorem theta_B1
    (v : Fin 8 → ZMod 2) :
    theta (Multiplicative.ofAdd (Matrix.mulVec B1 v)) =
      QuotientGroup.mk ⟨x * nf 0 v * x⁻¹, x_conj_mem_Q (nf_mem_Q 0 v)⟩ := by
  obtain ⟨t, ht⟩ := conj_nf_zero x xz xv x_conj_q v
  have hw : (fun k => ∑ i, v i * xv i k) = Matrix.mulVec B1 v := by
    funext k
    simp [Matrix.mulVec, dotProduct, B1, mul_comm]
  rw [hw] at ht
  have e : (⟨x * nf 0 v * x⁻¹, x_conj_mem_Q (nf_mem_Q 0 v)⟩ : Q) =
      ⟨nf t (Matrix.mulVec B1 v), nf_mem_Q _ _⟩ := Subtype.ext ht
  rw [e]
  exact ExtraspecialNF.theta_apply_eq_mk symplectic_rel t _

theorem theta_B2
    (v : Fin 8 → ZMod 2) :
    theta (Multiplicative.ofAdd (Matrix.mulVec B2 v)) =
      QuotientGroup.mk ⟨y * nf 0 v * y⁻¹, y_conj_mem_Q (nf_mem_Q 0 v)⟩ := by
  obtain ⟨t, ht⟩ := conj_nf_zero y yz yv y_conj_q v
  have hw : (fun k => ∑ i, v i * yv i k) = Matrix.mulVec B2 v := by
    funext k
    simp [Matrix.mulVec, dotProduct, B2, mul_comm]
  rw [hw] at ht
  have e : (⟨y * nf 0 v * y⁻¹, y_conj_mem_Q (nf_mem_Q 0 v)⟩ : Q) =
      ⟨nf t (Matrix.mulVec B2 v), nf_mem_Q _ _⟩ := Subtype.ext ht
  rw [e]
  exact ExtraspecialNF.theta_apply_eq_mk symplectic_rel t _

end CFSG.Sporadic.Th.Max3
