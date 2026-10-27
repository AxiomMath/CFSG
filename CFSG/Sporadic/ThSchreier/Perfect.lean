
module

public import CFSG.Sporadic.ThSchreier.PerfectBase1

public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import CFSG.Sporadic.ThSchreier.PerfectBase
public import CFSG.Sporadic.ThSchreier.RigidityBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates
open scoped commutatorElement

theorem isPerfect_MQ :
    Group.IsPerfect AltQuot.MQ := by
  have := AltQuot.isSimpleGroup_MQ
  refine isPerfect_of_isSimpleGroup ⟨kappa.symm ⟨aPerm, aPerm_mem⟩, kappa.symm ⟨bPerm, bPerm_mem⟩,
    fun h => aPerm_mul_bPerm_ne ?_⟩
  have := congrArg (fun g => ((kappa g : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9))) h
  simpa using this

@[expose] noncomputable def piQ :
    Q →* Multiplicative (Fin 8 → ZMod 2) :=
  theta.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))

theorem piQ_eq_one_iff
    (g : Q) : piQ g = 1 ↔ g ∈ Subgroup.center Q := by
  simp [piQ, QuotientGroup.eq_one_iff]

theorem piQ_nf (v : Fin 8 → ZMod 2) :
    piQ ⟨nf 0 v, nf_mem_Q 0 v⟩ = Multiplicative.ofAdd v := by
  rw [piQ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  exact (theta_apply_nf 0 v).symm

theorem piQ_conj_x
    (v : Fin 8 → ZMod 2) :
    piQ ⟨x * nf 0 v * x⁻¹, x_conj_mem_Q (nf_mem_Q 0 v)⟩ =
      Multiplicative.ofAdd (Matrix.mulVec B1 v) := by
  rw [piQ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  exact (theta_B1 v).symm

theorem piQ_conj_y
    (v : Fin 8 → ZMod 2) :
    piQ ⟨y * nf 0 v * y⁻¹, y_conj_mem_Q (nf_mem_Q 0 v)⟩ =
      Multiplicative.ofAdd (Matrix.mulVec B2 v) := by
  rw [piQ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  exact (theta_B2 v).symm

@[expose] def commVecs :
    Set (Fin 8 → ZMod 2) :=
  {u | ∃ d : ↥M, d ∈ commM ∧ ∃ hd : (d : J) ∈ Q, piQ ⟨d, hd⟩ = Multiplicative.ofAdd u}

theorem commVecs_add
    {u w : Fin 8 → ZMod 2} (hu : u ∈ commVecs) (hw : w ∈ commVecs) :
    u + w ∈ commVecs := by
  obtain ⟨d, hdD, hdQ, hd⟩ := hu
  obtain ⟨e, heD, heQ, he⟩ := hw
  refine ⟨d * e, commM.mul_mem hdD heD, Q.mul_mem hdQ heQ, ?_⟩
  have : (⟨(d * e : ↥M), Q.mul_mem hdQ heQ⟩ : Q) = ⟨d, hdQ⟩ * ⟨e, heQ⟩ := rfl
  rw [this, map_mul, hd, he, ofAdd_add]

theorem commVecs_B1
    (v : Fin 8 → ZMod 2) : Matrix.mulVec (B1 - 1) v ∈ commVecs := by
  have hQ : ((⁅xM, nfM v⁆ : ↥M) : J) ∈ Q := by
    show x * nf 0 v * x⁻¹ * (nf 0 v)⁻¹ ∈ Q
    exact Q.mul_mem (x_conj_mem_Q (nf_mem_Q 0 v)) (Q.inv_mem (nf_mem_Q 0 v))
  refine ⟨⁅xM, nfM v⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
    (Subgroup.mem_top _), hQ, ?_⟩
  have e : (⟨((⁅xM, nfM v⁆ : ↥M) : J), hQ⟩ : Q) =
      ⟨x * nf 0 v * x⁻¹, x_conj_mem_Q (nf_mem_Q 0 v)⟩ * (⟨nf 0 v, nf_mem_Q 0 v⟩)⁻¹ := rfl
  rw [e, map_mul, map_inv, piQ_conj_x, piQ_nf, ← ofAdd_neg, ← ofAdd_add, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_add_neg]
  rfl

theorem commVecs_B2
    (v : Fin 8 → ZMod 2) : Matrix.mulVec (B2 - 1) v ∈ commVecs := by
  have hQ : ((⁅yM, nfM v⁆ : ↥M) : J) ∈ Q := by
    show y * nf 0 v * y⁻¹ * (nf 0 v)⁻¹ ∈ Q
    exact Q.mul_mem (y_conj_mem_Q (nf_mem_Q 0 v)) (Q.inv_mem (nf_mem_Q 0 v))
  refine ⟨⁅yM, nfM v⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
    (Subgroup.mem_top _), hQ, ?_⟩
  have e : (⟨((⁅yM, nfM v⁆ : ↥M) : J), hQ⟩ : Q) =
      ⟨y * nf 0 v * y⁻¹, y_conj_mem_Q (nf_mem_Q 0 v)⟩ * (⟨nf 0 v, nf_mem_Q 0 v⟩)⁻¹ := rfl
  rw [e, map_mul, map_inv, piQ_conj_y, piQ_nf, ← ofAdd_neg, ← ofAdd_add, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_add_neg]
  rfl

theorem mem_commVecs
    (u : Fin 8 → ZMod 2) : u ∈ commVecs := by
  rw [eq_add_of_vec u]
  exact commVecs_add (commVecs_B1 _) (commVecs_B2 _)

theorem z_mem_commM :
    (⟨z, z_mem_M⟩ : ↥M) ∈ commM := by
  have hc : ⁅(⟨q 0, q_mem_M 0⟩ : ↥M), (⟨q 1, q_mem_M 1⟩ : ↥M)⁆ = ⟨z, z_mem_M⟩ := by
    apply Subtype.ext
    show q 0 * q 1 * (q 0)⁻¹ * (q 1)⁻¹ = z
    have h := q_mul_q 0 1
    have hc01 : (c 0 1).val = 1 := by decide
    rw [hc01, pow_one] at h
    rw [h, AltQuot.q_inv, AltQuot.q_inv]
    have hz := z_mul_q 0
    calc q 1 * q 0 * z * q 0 * q 1 = q 1 * q 0 * (z * q 0) * q 1 := by group
      _ = q 1 * q 0 * (q 0 * z) * q 1 := by rw [hz]
      _ = q 1 * (q 0 * q 0) * (z * q 1) := by group
      _ = q 1 * (q 0 * q 0) * (q 1 * z) := by rw [z_mul_q 1]
      _ = z := by rw [q_mul_self, mul_one, ← mul_assoc, q_mul_self, one_mul]
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem mem_commM_of_mem_Q
    {m : ↥M} (hm : (m : J) ∈ Q) : m ∈ commM := by
  obtain ⟨d, hdD, hdQ, hd⟩ := mem_commVecs (Multiplicative.toAdd (piQ ⟨m, hm⟩))
  have hk : (⟨d, hdQ⟩ : Q)⁻¹ * ⟨m, hm⟩ ∈ Subgroup.center Q := by
    rw [← piQ_eq_one_iff, map_mul, map_inv, hd, ofAdd_toAdd]
    exact inv_mul_cancel _
  rw [center_Q, Subgroup.mem_subgroupOf] at hk
  obtain ⟨k, hk⟩ := hk
  have hzk : (⟨z, z_mem_M⟩ : ↥M) ^ k ∈ commM := commM.zpow_mem z_mem_commM k
  have e : m = d * (⟨z, z_mem_M⟩ : ↥M) ^ k := by
    apply Subtype.ext
    have hk' : z ^ k = (d : J)⁻¹ * m := hk
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow, hk', mul_inv_cancel_left]
  rw [e]
  exact commM.mul_mem hdD hzk

theorem isPerfect_M :
    Group.IsPerfect ↥M := by
  refine ⟨eq_top_iff.2 fun m _ => ?_⟩
  have hMQ := isPerfect_MQ.commutator_eq_top
  have himg : (commutator ↥M).map AltQuot.proj = commutator AltQuot.MQ := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ AltQuot.proj_surjective]
  have hm : AltQuot.proj m ∈ (commutator ↥M).map AltQuot.proj := by
    rw [himg, hMQ]
    exact Subgroup.mem_top _
  obtain ⟨d, hdD, hdm⟩ := hm
  have hq : (d : J)⁻¹ * m ∈ Q := AltQuot.proj_eq_proj_iff.1 hdm
  have : d⁻¹ * m ∈ commM := mem_commM_of_mem_Q hq
  have e : m = d * (d⁻¹ * m) := by group
  rw [e]
  exact commM.mul_mem hdD this

end CFSG.Sporadic.ThSchreier
