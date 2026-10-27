
module

public import CFSG.Monster.B.TwoA.Unitary.Stab891Base

public import CFSG.Monster.B.TwoA.Unitary.WStab
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import Certificates.Certificate3061
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public import Certificates.Certificate3041Base
public import CFSG.Monster.B.Co2.Simple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

theorem shortVec_zero : Native.vectors[0]! = 6144 :=
  Certificates.certificate3061.1

theorem sigmaW_eq_wvec :
    sigmaW = wvec 0 := by
  rw [sigmaW_eq_decW, wvec, shortVec]
  exact congrArg decW shortVec_zero.symm

@[expose] def kvEquivP :
    Kstab v0 ≃* Pgrp :=
  (MulEquiv.subgroupCongr Agrp_eq_Kv.symm).trans agrpEquivPgrp

theorem kvEquivP_apply_zero
    (k : Kstab v0) :
    wvec ((kvEquivP k : Equiv.Perm Ω) 0) = wAct v0 k⁻¹ sigmaW := by
  rw [kvEquivP, MulEquiv.trans_apply, agrpEquivPgrp_apply, wvec_theta, ← sigmaW_eq_wvec]
  rfl

theorem mem_Usig_iff_stabilizer
    (k : Kstab v0) :
    k ∈ Usig ↔ kvEquivP k ∈ MulAction.stabilizer Pgrp (0 : Ω) := by
  rw [MulAction.mem_stabilizer_iff, mem_Usig]
  change _ ↔ (kvEquivP k : Equiv.Perm Ω) 0 = 0
  rw [← wvec_injective.eq_iff, kvEquivP_apply_zero, ← sigmaW_eq_wvec]
  constructor
  · intro h
    conv_lhs => rw [← h]
    exact wAct_inv_apply k _
  · intro h
    conv_lhs => rw [← h]
    exact wAct_apply_inv k _

theorem map_Usig :
    Usig.map kvEquivP.toMonoidHom =
    MulAction.stabilizer Pgrp (0 : Ω) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (mem_Usig_iff_stabilizer k).1 hk
  · intro hx
    refine ⟨kvEquivP.symm x, (mem_Usig_iff_stabilizer _).2 ?_, kvEquivP.apply_symm_apply x⟩
    rw [MulEquiv.apply_symm_apply]
    exact hx

theorem natCard_Usig :
    Nat.card Usig =
    18393661440 := by
  rw [← natCard_stabilizer_Pgrp, ← map_Usig]
  exact Nat.card_congr (Usig.equivMapOfInjective _ kvEquivP.injective).toEquiv

attribute [local instance] wLeftAction

theorem stabilizer_H6K :
    MulAction.stabilizer H6K wFr = Mfr.subgroupOf H6K := by
  ext h
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Mfr, mem_wStab]
  change wAct v0 (h : Kstab v0)⁻¹ wFr = wFr ↔ _
  constructor
  · intro e
    conv_lhs => rw [← e]
    exact wAct_apply_inv _ _
  · intro e
    conv_lhs => rw [← e]
    exact wAct_inv_apply _ _

theorem H6K_inf_Mfr :
    H6K ⊓ Mfr = UsigW :=
  le_antisymm (inf_le_inf_right _ H6K_le_Usig) (le_inf UsigW_le_H6K inf_le_right)

theorem natCard_H6K :
    Nat.card H6K =
    18393661440 := by
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer H6K wFr)
  rw [MulAction.index_stabilizer, orbit_H6K, ncard_range_n6vec, stabilizer_H6K] at h1
  have h2 : Nat.card (Mfr.subgroupOf H6K) = Nat.card UsigW := by
    rw [← H6K_inf_Mfr, inf_comm, ← Subgroup.subgroupOf_map_subtype]
    exact Nat.card_congr ((Mfr.subgroupOf H6K).equivMapOfInjective _
      Subtype.val_injective).toEquiv
  rw [h2, natCard_UsigW] at h1
  omega

theorem H6K_eq_Usig :
    H6K = Usig :=
  Subgroup.eq_of_le_of_card_ge H6K_le_Usig (by rw [natCard_Usig, natCard_H6K])

theorem H6_eq_Usig :
    H6 = Usig.map (Kstab v0).subtype := by rw
    [← map_H6K, H6K_eq_Usig]

theorem orbit_Usig :
    MulAction.orbit Usig wFr = Set.range n6vec := by
  rw [← H6K_eq_Usig, orbit_H6K]

theorem mem_range_n6vec_iff
    (x : Wv v0) :
    (∃ u ∈ Usig, wAct v0 u wFr = x) ↔ x ∈ Set.range n6vec := by
  rw [← orbit_Usig]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, hu⟩⁻¹, ?_⟩
    change wAct v0 ((⟨u, hu⟩⁻¹ : Usig) : Kstab v0)⁻¹ wFr = wAct v0 u wFr
    rw [Subgroup.coe_inv, inv_inv]
  · rintro ⟨u, rfl⟩
    exact ⟨(u : Kstab v0)⁻¹, Usig.inv_mem u.2, rfl⟩

theorem exists_wAct_wFr
    (j : Fin 891) : ∃ u ∈ Usig, wAct v0 u wFr =
    n6vec j :=
  (mem_range_n6vec_iff _).2 ⟨j, rfl⟩

theorem transitive_n6vec
    (i j : Fin 891) : ∃ u ∈ Usig, wAct v0 u
    (n6vec i) = n6vec j := by
  obtain ⟨g, hg, hgi⟩ := exists_wAct_wFr i
  obtain ⟨h, hh, hhj⟩ := exists_wAct_wFr j
  refine ⟨g⁻¹ * h, Usig.mul_mem (Usig.inv_mem hg) hh, ?_⟩
  rw [← hgi, wAct_mul, Module.End.mul_apply, wAct_inv_apply, hhj]

theorem n6vec_mem_sigmaPerp
    (j : Fin 891) : n6vec j ∈ sigmaPerp := by
  obtain ⟨u, hu, e⟩ := exists_wAct_wFr j
  change bW sigmaW (n6vec j) = 0
  rw [← e, ← (mem_Usig.1 hu : wAct v0 u sigmaW = sigmaW), bW_wAct, bW_sigmaW_wFr]

theorem spanIdxN_ok : ∀ i < 21, spanIdxN.getD i 0 < 891 ∧
    n6VecArr[spanIdxN.getD i 0]! = n6SpanArr[i]! :=
  Certificates.certificate3061.2

@[expose] def spanVec (i : Fin 21) : Wv v0 :=
  n6vec ⟨spanIdxN.getD i 0, (spanIdxN_ok i i.2).1⟩

theorem spanVec_eq (i : Fin 21) : spanVec i = decW
    n6SpanArr[(i : ℕ)]! := by
  rw [spanVec, n6vec]
  exact congrArg decW (spanIdxN_ok i i.2).2

theorem linearIndependent_spanVec : LinearIndependent (ZMod 2)
    spanVec := by
  have hf : spanVec = (qbWBasis.equivFun.symm.toLinearMap :
      (Fin 22 → ZMod 2) →ₗ[ZMod 2] Wv v0) ∘ fun i : Fin 21 => bvec 22 n6SpanArr[(i : ℕ)]! := by
    funext i
    rw [spanVec_eq, decW_eq_equivFun]
    rfl
  rw [hf]
  refine LinearIndependent.map' ?_ _ (LinearMap.ker_eq_bot.2 qbWBasis.equivFun.symm.injective)
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun x => bvec 22 (spanDual.getD j 0) ⬝ᵥ x) hg
  simp only [dotProduct_sum, dotProduct_smul, spanDual_check, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, dotProduct_zero] at h
  exact h

theorem span_n6vec :
    Submodule.span (ZMod 2) (Set.range n6vec) =
    sigmaPerp := by
  have hle : Submodule.span (ZMod 2) (Set.range n6vec) ≤ sigmaPerp := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact n6vec_mem_sigmaPerp j
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [finrank_sigmaPerp, ← Fintype.card_fin 21, ← finrank_span_eq_card linearIndependent_spanVec]
  refine Submodule.finrank_mono (Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨_, rfl⟩

theorem eq_one_of_fix_n6vec
    {u : Kstab v0}
    (hfix : ∀ j, wAct v0 u (n6vec j) = n6vec j) :
    u = 1 := by
  have hspan : ∀ x ∈ sigmaPerp, wAct v0 u x = x := by
    intro x hx
    rw [← span_n6vec] at hx
    have := LinearMap.eqOn_span' (f := wAct v0 u) (g := LinearMap.id)
      (s := Set.range n6vec) (fun _ ⟨j, hj⟩ => by rw [← hj, hfix j, LinearMap.id_apply]) hx
    rwa [LinearMap.id_apply] at this
  have h1 := wAct_eq_one_of_fix u hspan
  apply KvAct_injective_vMinus
  rw [map_one]
  change MulOpposite.op (wAct v0 u) = 1
  rw [h1]
  rfl

theorem native_unitary_stabilizer_891_action :
    sigmaW = decW 6144 ∧ sigmaW = wvec 0 ∧
    H6 = Usig.map (Kstab v0).subtype ∧ Nat.card Usig = 18393661440 ∧
    (∀ k : Fin 17, n6Elt k ∈ Kstab v0 ∧
      ∀ c : ℕ, wAct v0 (genK k) (decW c) = decW (Native.actD 22 n6RowArr[(k : ℕ)]! c)) ∧
    (∀ (k : Fin 17) (j : Fin 891), wAct v0 (genK k) (n6vec j) = n6vec (n6perm k j)) ∧
    Function.Injective n6vec ∧ n6vec 0 = wFr ∧
    (∀ x : Wv v0, (∃ u ∈ Usig, wAct v0 u wFr = x) ↔ x ∈ Set.range n6vec) ∧
    Submodule.span (ZMod 2) (Set.range n6vec) = sigmaPerp ∧
    Module.finrank (ZMod 2) sigmaPerp = 21 ∧
    (∀ u ∈ Usig, (∀ j, wAct v0 u (n6vec j) = n6vec j) → u = 1) ∧
    (∀ i j : Fin 891, ∃ u ∈ Usig, wAct v0 u (n6vec i) = n6vec j) ∧
    (∀ k : Kstab v0, k ∈ Usig ⊓ Mfr ↔ ∃ a : C, (a : Fin 24 → ZMod 2) ∈ C012 ∧ ∃ p ∈ P2,
      (k : OLq) = QuotientGroup.mk (gO a * PO p)) ∧
    (∃ e : SDD c012Hyp ≃* (Usig ⊓ Mfr : Subgroup (Kstab v0)), ∀ (a : C012) (p : P2),
      ((e ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⟩ : Kstab v0) : OLq) =
        QuotientGroup.mk (gO ⟨a, (mem_C012.1 a.2).1⟩ * PO (p : AutPerm)⁻¹)) ∧
    Nat.card (Usig ⊓ Mfr : Subgroup (Kstab v0)) = 20643840 ∧
    Subgroup.closure (Set.range n6Aut) = P2 ∧ Nat.card P2 = 40320 := by
  refine ⟨sigmaW_eq_decW, sigmaW_eq_wvec, H6_eq_Usig, natCard_Usig,
    fun k => ⟨n6Elt_mem k, wAct_genK_decW k⟩, wAct_genK_n6vec, n6vec_injective, n6vec_zero,
    mem_range_n6vec_iff, span_n6vec, finrank_sigmaPerp, fun u _ h => eq_one_of_fix_n6vec h,
    transitive_n6vec, fun k => (mem_UsigW_iff k).trans (mem_monoSub_iff c012Hyp),
    ⟨UsigWEquiv, fun a p => (coe_UsigWEquiv _).trans (monoD_mk c012Hyp a p)⟩, natCard_UsigW,
    closure_n6Aut, natCard_P2⟩

end CFSG.Monster.B.TwoA.Unitary
