module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphRoot
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoCore
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

@[expose] def cnLabels
    (v w : CVert) : Set Shat := clabelS '' cgraph.commonNeighbors v w

@[expose] def cnGroup
    (v w : CVert) : Subgroup Shat := Subgroup.closure (cnLabels v w)

theorem clabelS_mem_cnGroup
    {v w u : CVert} (hu : u ∈ cgraph.commonNeighbors v w) :
    clabelS u ∈ cnGroup v w :=
  Subgroup.subset_closure ⟨u, hu, rfl⟩

theorem clabelS_cvMul
    (x : CVert) (s : Shat) : clabelS (cvMul x s) = s⁻¹ * clabelS x * s :=
  Subtype.ext (clabel_cvMul x s)

theorem cvMul_mem_commonNeighbors
    {v w x : CVert} {s : Shat} (hv : cvMul v s = v)
    (hw : cvMul w s = w) (hx : x ∈ cgraph.commonNeighbors v w) :
    cvMul x s ∈ cgraph.commonNeighbors v w := by
  have h1 := (cgraph_adj_cvMul v x s).2 hx.1
  have h2 := (cgraph_adj_cvMul w x s).2 hx.2
  rw [hv] at h1
  rw [hw] at h2
  exact ⟨h1, h2⟩

theorem conj_mem_cnGroup
    {v w : CVert} {q : Shat} (hq : q ∈ vStab v ⊓ vStab w) {h : Shat}
    (hh : h ∈ cnGroup v w) : q * h * q⁻¹ ∈ cnGroup v w := by
  have hq' := Subgroup.mem_inf.1 (inv_mem hq)
  have hle : Subgroup.closure (cnLabels v w) ≤
      (cnGroup v w).comap (MulAut.conj q).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨u, hu, rfl⟩
    show (MulAut.conj q) (clabelS u) ∈ cnGroup v w
    rw [MulAut.conj_apply]
    have e : q * clabelS u * q⁻¹ = clabelS (cvMul u q⁻¹) := by rw [clabelS_cvMul, inv_inv]
    rw [e]
    exact clabelS_mem_cnGroup (cvMul_mem_commonNeighbors (mem_vStab.1 hq'.1)
      (mem_vStab.1 hq'.2) hu)
  exact hle hh

theorem cnGroup_normal
    (v w : CVert) :
    ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w)).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    show (g : Shat) * n * (g : Shat)⁻¹ ∈ cnGroup v w
    exact conj_mem_cnGroup g.2 hn⟩

section Group

variable (H : ∀ x : CVert, LocalHom x)
include H

theorem clabelS_mem_qStab {v w u : CVert} (hu : u ∈ cgraph.commonNeighbors v w) :
    clabelS u ∈ vStab v ⊓ vStab w := by
  have hvu : cgraph.Adj u v := (hu.1 : cgraph.Adj v u).symm
  have hwu : cgraph.Adj u w := (hu.2 : cgraph.Adj w u).symm
  exact Subgroup.mem_inf.2 ⟨mem_vStab.2 (cvMul_clabelS_of_mem H (v := u) (x := v) hvu),
    mem_vStab.2 (cvMul_clabelS_of_mem H (v := u) (x := w) hwu)⟩

theorem cnGroup_le (v w : CVert) : cnGroup v w ≤ vStab v ⊓ vStab w := by
  rw [cnGroup, Subgroup.closure_le]
  rintro _ ⟨u, hu, rfl⟩
  exact clabelS_mem_qStab H hu

theorem eq_one_of_centralizes
    {v w : CVert} (hw : w ∈ sphereThree v) {q : Shat}
    (hq : q ∈ vStab v ⊓ vStab w)
    (hc : ∀ u ∈ cgraph.commonNeighbors v w, q * clabelS u = clabelS u * q) : q = 1 := by
  obtain ⟨hvw, hna, u₀, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 hw.1
  have hfaith := (order_three_common H hvw hna hw.2 ⟨u₀, hvu, huw.symm⟩).2
  have hq' := Subgroup.mem_inf.1 hq
  refine hfaith q (mem_vStab.1 hq'.1) (mem_vStab.1 hq'.2) fun x hx => ?_
  have hxq := cvMul_mem_commonNeighbors (mem_vStab.1 hq'.1) (mem_vStab.1 hq'.2) hx
  have e : clabelS (cvMul x q) = clabelS x := by
    rw [clabelS_cvMul, mul_assoc, ← hc x hx, ← mul_assoc, inv_mul_cancel, one_mul]
  exact clabel_injOn_neighborSet v hxq.1 hx.1 (congrArg Subtype.val e)

theorem eq_one_of_centralizes_cnGroup
    {v w : CVert} (hw : w ∈ sphereThree v) {q : Shat}
    (hq : q ∈ vStab v ⊓ vStab w) (hc : ∀ h ∈ cnGroup v w, q * h = h * q) : q = 1 :=
  eq_one_of_centralizes H hw hq fun _ hu => hc _ (clabelS_mem_cnGroup hu)

theorem center_cnGroup_eq_bot
    {v w : CVert} (hw : w ∈ sphereThree v) :
    Subgroup.center (cnGroup v w) = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine eq_one_of_centralizes H hw (cnGroup_le H v w h.2) fun u hu => ?_
  have e := Subgroup.mem_center_iff.1 hh ⟨clabelS u, clabelS_mem_cnGroup hu⟩
  exact (congrArg Subtype.val e).symm

theorem exists_conj_embedding
    {v w : CVert} (hw : w ∈ sphereThree v) :
    ∃ ψ : (vStab v ⊓ vStab w : Subgroup Shat) →* MulAut (cnGroup v w),
      Function.Injective ψ ∧ ∀ q h, ((ψ q h : cnGroup v w) : Shat) = q * h * (q : Shat)⁻¹ := by
  let ψ : (vStab v ⊓ vStab w : Subgroup Shat) →* MulAut (cnGroup v w) :=
    { toFun := fun q =>
        { toFun := fun h => ⟨(q : Shat) * h * (q : Shat)⁻¹, conj_mem_cnGroup q.2 h.2⟩
          invFun := fun h => ⟨(q : Shat)⁻¹ * h * q, by
            have h1 := conj_mem_cnGroup (inv_mem q.2) h.2
            rwa [inv_inv] at h1⟩
          left_inv := fun h => Subtype.ext (by
            show (q : Shat)⁻¹ * ((q : Shat) * h * (q : Shat)⁻¹) * q = h
            group)
          right_inv := fun h => Subtype.ext (by
            show (q : Shat) * ((q : Shat)⁻¹ * h * q) * (q : Shat)⁻¹ = h
            group)
          map_mul' := fun h h' => Subtype.ext (by
            show (q : Shat) * (h * h') * (q : Shat)⁻¹ =
              (q : Shat) * h * (q : Shat)⁻¹ * ((q : Shat) * h' * (q : Shat)⁻¹)
            group) }
      map_one' := MulEquiv.ext fun h => Subtype.ext (by
        show ((1 : Shat)) * h * (1 : Shat)⁻¹ = h
        group)
      map_mul' := fun q q' => MulEquiv.ext fun h => Subtype.ext (by
        show ((q : Shat) * q') * h * ((q : Shat) * q')⁻¹ =
          (q : Shat) * ((q' : Shat) * h * (q' : Shat)⁻¹) * (q : Shat)⁻¹
        group) }
  refine ⟨ψ, ?_, fun _ _ => rfl⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  apply Subtype.ext
  refine eq_one_of_centralizes_cnGroup H hw q.2 fun h hh => ?_
  have e := congrArg (fun φ : MulAut (cnGroup v w) => ((φ ⟨h, hh⟩ : cnGroup v w) : Shat)) hq
  have e' : (q : Shat) * h * (q : Shat)⁻¹ = h := e
  calc (q : Shat) * h = (q : Shat) * h * (q : Shat)⁻¹ * q := by group
    _ = h * q := by rw [e']

end Group

end CFSG.Monster.B.TwoA.Amalgam
