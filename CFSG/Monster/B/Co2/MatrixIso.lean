
module


public import CFSG.Monster.B.Co2.MatrixW

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv

theorem permutes_wvec
    (g : OLq) (hg : g ∈ Agrp) :
    (∀ j, ∃ j', wAct v0 ⟨g, Agrp_le hg⟩ (wvec j) = wvec j') ∧
      ∀ j, ∃ j', wAct v0 ⟨g⁻¹, Agrp_le (inv_mem hg)⟩ (wvec j) = wvec j' := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨fun j => ⟨pa j, wAct_A0_wvec j⟩, fun j =>
        ⟨pa⁻¹ j, wAct_inv_wvec_of (k := ⟨A0, A0_mem⟩) wAct_A0_wvec j⟩⟩
    · exact ⟨fun j => ⟨pb j, wAct_A1_wvec j⟩, fun j =>
        ⟨pb⁻¹ j, wAct_inv_wvec_of (k := ⟨A1, A1_mem⟩) wAct_A1_wvec j⟩⟩
  | one =>
    have e : (⟨(1 : OLq), Agrp_le (one_mem _)⟩ : Kstab v0) = 1 := rfl
    have e' : (⟨(1 : OLq)⁻¹, Agrp_le (inv_mem (one_mem _))⟩ : Kstab v0) = 1 :=
      Subtype.ext inv_one
    exact ⟨fun j => ⟨j, by rw [e, wAct_one]; rfl⟩, fun j => ⟨j, by rw [e', wAct_one]; rfl⟩⟩
  | mul x y hx hy ihx ihy =>
    refine ⟨fun j => ?_, fun j => ?_⟩
    · obtain ⟨j1, h1⟩ := ihx.1 j
      obtain ⟨j2, h2⟩ := ihy.1 j1
      refine ⟨j2, ?_⟩
      have e : (⟨x * y, Agrp_le (mul_mem hx hy)⟩ : Kstab v0) =
          ⟨x, Agrp_le hx⟩ * ⟨y, Agrp_le hy⟩ := rfl
      rw [e, wAct_mul, Module.End.mul_apply, h1, h2]
    · obtain ⟨j1, h1⟩ := ihy.2 j
      obtain ⟨j2, h2⟩ := ihx.2 j1
      refine ⟨j2, ?_⟩
      have e : (⟨(x * y)⁻¹, Agrp_le (inv_mem (mul_mem hx hy))⟩ : Kstab v0) =
          ⟨y⁻¹, Agrp_le (inv_mem hy)⟩ * ⟨x⁻¹, Agrp_le (inv_mem hx)⟩ :=
        Subtype.ext (mul_inv_rev x y)
      rw [e, wAct_mul, Module.End.mul_apply, h1, h2]
  | inv x hx ih =>
    refine ⟨fun j => ?_, fun j => ?_⟩
    · exact ih.2 j
    · obtain ⟨j', h'⟩ := ih.1 j
      refine ⟨j', ?_⟩
      have e : (⟨x⁻¹⁻¹, Agrp_le (inv_mem (inv_mem hx))⟩ : Kstab v0) = ⟨x, Agrp_le hx⟩ :=
        Subtype.ext (inv_inv x)
      rw [e, h']

@[expose] def aIdx
    (a : Agrp) (j : Ω) : Ω :=
  Classical.choose ((permutes_wvec (a : OLq) a.2).2 j)

theorem wvec_aIdx (a : Agrp) (j : Ω) :
    wvec (aIdx a j) = wAct v0 ⟨(a : OLq)⁻¹, Agrp_le (inv_mem a.2)⟩ (wvec j) :=
  (Classical.choose_spec ((permutes_wvec (a : OLq) a.2).2 j)).symm

@[expose, instance_reducible] def aAction :
    MulAction Agrp Ω where
  smul := aIdx
  one_smul j := wvec_injective (by
    change wvec (aIdx 1 j) = wvec j
    rw [wvec_aIdx]
    have e : (⟨((1 : Agrp) : OLq)⁻¹, Agrp_le (inv_mem (1 : Agrp).2)⟩ : Kstab v0) = 1 :=
      Subtype.ext (by simp)
    rw [e, wAct_one]
    rfl)
  mul_smul a b j := wvec_injective (by
    change wvec (aIdx (a * b) j) = wvec (aIdx a (aIdx b j))
    rw [wvec_aIdx, wvec_aIdx, wvec_aIdx]
    have e : (⟨((a * b : Agrp) : OLq)⁻¹, Agrp_le (inv_mem (a * b).2)⟩ : Kstab v0) =
        ⟨(b : OLq)⁻¹, Agrp_le (inv_mem b.2)⟩ * ⟨(a : OLq)⁻¹, Agrp_le (inv_mem a.2)⟩ :=
      Subtype.ext (by simp [mul_inv_rev])
    rw [e, wAct_mul, Module.End.mul_apply])

@[expose] def theta :
    Agrp →* Equiv.Perm Ω := @MulAction.toPermHom Agrp Ω _ aAction

theorem wvec_theta
    (a : Agrp) (j : Ω) :
    wvec (theta a j) = wAct v0 ⟨(a : OLq)⁻¹, Agrp_le (inv_mem a.2)⟩ (wvec j) :=
  wvec_aIdx a j

theorem theta_A0 :
    theta A0' = pa⁻¹ := by
  ext j
  have h := wvec_theta A0' j
  have e : (⟨((A0' : Agrp) : OLq)⁻¹, Agrp_le (inv_mem A0'.2)⟩ : Kstab v0) =
      (⟨A0, A0_mem⟩ : Kstab v0)⁻¹ := rfl
  rw [e, wAct_inv_wvec_of (k := ⟨A0, A0_mem⟩) wAct_A0_wvec j] at h
  exact congrArg Fin.val (wvec_injective h)

theorem theta_A1 :
    theta A1' = pb⁻¹ := by
  ext j
  have h := wvec_theta A1' j
  have e : (⟨((A1' : Agrp) : OLq)⁻¹, Agrp_le (inv_mem A1'.2)⟩ : Kstab v0) =
      (⟨A1, A1_mem⟩ : Kstab v0)⁻¹ := rfl
  rw [e, wAct_inv_wvec_of (k := ⟨A1, A1_mem⟩) wAct_A1_wvec j] at h
  exact congrArg Fin.val (wvec_injective h)

theorem theta_injective :
    Function.Injective theta := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hfix : ∀ j, wAct v0 ⟨(a : OLq)⁻¹, Agrp_le (inv_mem a.2)⟩ (wvec j) = wvec j := by
    intro j
    rw [← wvec_theta, ha]
    rfl
  have hw : wAct v0 ⟨(a : OLq)⁻¹, Agrp_le (inv_mem a.2)⟩ = 1 :=
    LinearMap.ext_on_range span_wvec fun j => by rw [hfix, Module.End.one_apply]
  have hK : KvAct v0 ⟨(a : OLq)⁻¹, Agrp_le (inv_mem a.2)⟩ = KvAct v0 1 := by
    rw [map_one]
    change MulOpposite.op (wAct v0 _) = 1
    rw [hw]
    rfl
  have h1 := congrArg Subtype.val (KvAct_injective_vMinus hK)
  apply Subtype.ext
  change (a : OLq) = 1
  have : (a : OLq)⁻¹ = 1 := h1
  simpa using this

theorem range_theta :
    theta.range = Pgrp := by
  have htop : (⊤ : Subgroup Agrp) =
      Subgroup.closure (((↑) : Agrp → OLq) ⁻¹' ({A0, A1} : Set OLq)) :=
    (Subgroup.closure_closure_coe_preimage).symm
  have himg : theta '' (((↑) : Agrp → OLq) ⁻¹' ({A0, A1} : Set OLq)) = ({pa, pb} : Set _)⁻¹ := by
    ext g
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.inv_insert, Set.inv_singleton]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases ha with ha | ha
      · left
        have : a = A0' := Subtype.ext ha
        rw [this, theta_A0]
      · right
        have : a = A1' := Subtype.ext ha
        rw [this, theta_A1]
    · rintro (rfl | rfl)
      · exact ⟨A0', Or.inl rfl, theta_A0⟩
      · exact ⟨A1', Or.inr rfl, theta_A1⟩
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure, himg, Subgroup.closure_inv, Pgrp]

@[expose] def agrpEquivPgrp :
    Agrp ≃* Pgrp :=
  (MonoidHom.ofInjective theta_injective).trans (MulEquiv.subgroupCongr range_theta)

theorem agrpEquivPgrp_apply
    (a : Agrp) : (agrpEquivPgrp a : Equiv.Perm Ω) = theta a := rfl

theorem native_short_stabilizer_matrix_action :
    dec 12288 = classOf (Griess.vMinus 0 1) ∧
    (∀ i : Fin 24, alpha i ∈ Kstab v0 ∧
      ∀ x : ℕ, kOp (alpha i) (dec x) = dec (VisCert.actRows (genMatrix i) x)) ∧
    (∀ t : Fin 22, dec (quotBasis t) ∈ vPerpL v0) ∧
    LinearIndependent (ZMod 2) qbW ∧ Submodule.span (ZMod 2) (Set.range qbW) = ⊤ ∧
    (∀ (i : Fin 24) (c : ℕ),
      wAct v0 ⟨alpha i, alpha_mem_Kv i⟩ (decW c) = decW (Native.actD 22 (genQuotMatrix i) c)) ∧
    Function.Injective wvec ∧ Submodule.span (ZMod 2) (Set.range wvec) = ⊤ ∧
    (∀ (i : Fin 24) (j : Ω), wAct v0 ⟨alpha i, alpha_mem_Kv i⟩ (wvec j) = wvec (pPerm i j)) ∧
    (∀ j : Ω, wAct v0 ⟨A0, A0_mem⟩ (wvec j) = wvec (pa j)) ∧
    (∀ j : Ω, wAct v0 ⟨A1, A1_mem⟩ (wvec j) = wvec (pb j)) ∧
    Agrp ≤ Kstab v0 ∧
    (∃ φ : Agrp ≃* Pgrp, ∀ (a : Agrp) (j : Ω),
      wvec ((φ a : Equiv.Perm Ω) j) = wAct v0 ⟨(a : OLq)⁻¹, Agrp_le (inv_mem a.2)⟩ (wvec j)) ∧
    orderOf pa = 2 ∧ orderOf pb = 5 ∧ orderOf (pa * pb) = 23 :=
  ⟨vShort_eq, fun i => ⟨alpha_mem_Kv i, kOp_alpha_dec i⟩, dec_quotBasis_mem, linearIndependent_qbW,
    span_qbW, wAct_alpha_decW, wvec_injective, span_wvec, wAct_alpha_wvec, wAct_A0_wvec,
    wAct_A1_wvec, Agrp_le, ⟨agrpEquivPgrp, fun a j => wvec_theta a j⟩, orderOf_pa, orderOf_pb,
    orderOf_pa_mul_pb⟩

end CFSG.Monster.B.Co2
