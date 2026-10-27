module

public import CFSG.Sporadic.Th.Recog.CentralLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Max3.InvRep
open CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G]

local instance (priority := high) instAddCommGroupZMod2HIsoM : AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

namespace FibreData

variable {S : ThSetting G}

private noncomputable abbrev aM : Max3.M := ⟨Max3.z, Max3.z_mem_M⟩

private noncomputable abbrev q0M : Max3.M := ⟨Max3.q 0, Max3.q_mem_M 0⟩

private noncomputable abbrev q0QM : ↥(Max3.Q.subgroupOf Max3.M) :=
  ⟨q0M, Subgroup.mem_subgroupOf.mpr (Max3.q_mem_Q 0)⟩

private theorem aM_ne_one : aM ≠ 1 := by
  intro h
  have hJ : (aM : J) = 1 := by rw [h]; rfl
  exact Max3.z_ne_one hJ

private theorem zM_ne_one : S.toSetting.zM ≠ 1 := by
  intro h
  have hG : (S.toSetting.zM : G) = 1 := by rw [h]; rfl
  rw [S.toSetting.coe_zM] at hG
  exact S.toSetting.z_ne_one hG

private theorem exists_conj_q0_of_mem_Q (Fd : FibreData S) {m : J} (hm : m ∈ Max3.Q)
    (hsq : m * m = 1) (hne : m ≠ Max3.z) (hne1 : m ≠ 1) :
    ∃ g ∈ Max3.M, g * m * g⁻¹ = Max3.q 0 := by
  obtain ⟨g, hgM, h | h⟩ := CFSG.Sporadic.Th.Max3.InvRep.exists_conj_of_mem_Q hm hsq hne1
  · exfalso
    apply hne
    have hcommM : (⟨g, hgM⟩ : Max3.M) * ⟨Max3.z, Max3.z_mem_M⟩ =
        ⟨Max3.z, Max3.z_mem_M⟩ * (⟨g, hgM⟩ : Max3.M) :=
      Subgroup.mem_center_iff.mp Max3.z_mem_center_M ⟨g, hgM⟩
    have hcomm : (g : J) * Max3.z = Max3.z * (g : J) := by
      simpa using congrArg (fun x : Max3.M => (x : J)) hcommM
    calc m = (g : J)⁻¹ * ((g : J) * m * (g : J)⁻¹) * (g : J) := by group
      _ = (g : J)⁻¹ * Max3.z * (g : J) := by rw [h]
      _ = Max3.z := by
        calc (g : J)⁻¹ * Max3.z * (g : J)
            = (g : J)⁻¹ * (Max3.z * (g : J)) := by group
          _ = (g : J)⁻¹ * ((g : J) * Max3.z) := by rw [← hcomm]
          _ = Max3.z := by group
  · exact ⟨g, hgM, h⟩

private theorem φQ_eq_zQ_iff (Fd : FibreData S) (x : S.toSetting.Q) :
    Fd.φQ x = Fd.φQ S.toSetting.zQ ↔
      (((Fd.φQ x : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.z := by
  constructor
  · intro h
    rw [h]
    exact Fd.φQ_z
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    change (((Fd.φQ x : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) =
      (((Fd.φQ S.toSetting.zQ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J)
    rw [Fd.φQ_z]
    exact h

theorem commute_iff (Fd : FibreData S) {h : S.toSetting.M} {m : Max3.M}
    (hm : (h, m) ∈ Fd.F) (x : S.toSetting.Q) :
    (h : G) * ((x : S.toSetting.M) : G) = ((x : S.toSetting.M) : G) * (h : G) ↔
      (m : J) * ((Fd.φQ x : Max3.M) : J) = ((Fd.φQ x : Max3.M) : J) * (m : J) := by
  have hact := ((Fd.mem_F_iff h m).mp hm).2 x
  constructor
  · intro hcomm
    have hcommM : h * (x : S.toSetting.M) = (x : S.toSetting.M) * h :=
      Subtype.ext hcomm
    have hconj : conjAut S.toSetting.normal h x = x := by
      apply Subtype.ext
      rw [conjAut_apply]
      calc h * (x : S.toSetting.M) * h⁻¹ = ((x : S.toSetting.M) * h) * h⁻¹ := by
            rw [hcommM]
        _ = (x : S.toSetting.M) := by group
    have hmconj : conjAut instNormalQSubgroupOfM m (Fd.φQ x) = Fd.φQ x := by
      rw [← hact, hconj]
    have hmconjM : m * (Fd.φQ x : Max3.M) * m⁻¹ = (Fd.φQ x : Max3.M) := by
      rw [show m * (Fd.φQ x : Max3.M) * m⁻¹ =
          ((conjAut instNormalQSubgroupOfM m (Fd.φQ x) :
            ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) from
        (conjAut_apply instNormalQSubgroupOfM m (Fd.φQ x)).symm]
      rw [hmconj]
    have hmconjJ : (m : J) * ((Fd.φQ x : Max3.M) : J) * (m : J)⁻¹ =
        ((Fd.φQ x : Max3.M) : J) := by
      calc (m : J) * ((Fd.φQ x : Max3.M) : J) * (m : J)⁻¹
          = ((m * (Fd.φQ x : Max3.M) * m⁻¹ : Max3.M) : J) := rfl
        _ = ((Fd.φQ x : Max3.M) : J) := by rw [hmconjM]
    calc (m : J) * ((Fd.φQ x : Max3.M) : J)
        = ((m : J) * ((Fd.φQ x : Max3.M) : J) * (m : J)⁻¹) * (m : J) := by group
      _ = ((Fd.φQ x : Max3.M) : J) * (m : J) := by rw [hmconjJ]
  · intro hmcomm
    have hmconjM : m * (Fd.φQ x : Max3.M) * m⁻¹ = (Fd.φQ x : Max3.M) := by
      apply Subtype.ext
      calc (m : J) * ((Fd.φQ x : Max3.M) : J) * (m : J)⁻¹
          = (((Fd.φQ x : Max3.M) : J) * (m : J)) * (m : J)⁻¹ := by rw [hmcomm]
        _ = ((Fd.φQ x : Max3.M) : J) := by group
    have hmconj : conjAut instNormalQSubgroupOfM m (Fd.φQ x) = Fd.φQ x := by
      apply Subtype.ext
      rw [conjAut_apply]
      exact hmconjM
    have hconj : conjAut S.toSetting.normal h x = x := by
      apply Fd.φQ.injective
      rw [hact, hmconj]
    have hconjM : h * (x : S.toSetting.M) * h⁻¹ = (x : S.toSetting.M) := by
      exact congrArg (fun y : S.toSetting.Q => (y : S.toSetting.M)) hconj
    have hcommM : h * (x : S.toSetting.M) = (x : S.toSetting.M) * h := by
      calc h * (x : S.toSetting.M) = (h * (x : S.toSetting.M) * h⁻¹) * h := by group
        _ = (x : S.toSetting.M) * h := by rw [hconjM]
    exact congrArg (fun y : S.toSetting.M => (y : G)) hcommM

private noncomputable def toSettingQ (S : ThSetting G) {x : G} (hx : x ∈ S.Q) :
    S.toSetting.Q :=
  ⟨S.toSettingE ⟨x, S.Q_le_H hx⟩, (mem_toSetting_Q_iff S _).mpr (by
    change x ∈ S.Q
    exact hx)⟩

theorem exists_swap (Fd : FibreData S) :
    ∃ h₁ : S.toSetting.Q, (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.q 0 ∧
      ∃ g : G, g * S.z * g⁻¹ = ((h₁ : S.toSetting.M) : G) ∧
        g * ((h₁ : S.toSetting.M) : G) * g⁻¹ = S.z := by
  classical
  obtain ⟨y, hyz, hkQ, hkne⟩ := S.exists_conj_Q
  let k : G := y * S.z * y⁻¹
  have hkQ' : k ∈ S.Q := hkQ
  have hk2 : k * k = 1 := by
    have hz2 : S.z * S.z = 1 := by rw [← pow_two, ← S.ord_z, pow_orderOf_eq_one]
    calc k * k = (y * S.z * y⁻¹) * (y * S.z * y⁻¹) := rfl
      _ = y * (S.z * S.z) * y⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hk1 : k ≠ 1 := by
    intro h
    apply S.toSetting.z_ne_one
    calc S.z = y⁻¹ * k * y := by
          rw [show k = y * S.z * y⁻¹ from rfl]
          group
      _ = 1 := by rw [h]; group
  let kQ : S.toSetting.Q := toSettingQ S hkQ'
  have hkQ_coe : ((kQ : S.toSetting.M) : G) = k := rfl
  have hkQ_sq : kQ * kQ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change k * k = 1
    exact hk2
  have hkQ_ne_z : kQ ≠ S.toSetting.zQ := by
    intro h
    apply hkne
    calc k = ((kQ : S.toSetting.M) : G) := hkQ_coe.symm
      _ = ((S.toSetting.zQ : S.toSetting.M) : G) := by rw [h]
      _ = S.z := rfl
  let kQM : ↥(Max3.Q.subgroupOf Max3.M) := Fd.φQ kQ
  have hkQM_mem : ((kQM : Max3.M) : J) ∈ Max3.Q :=
    Subgroup.mem_subgroupOf.mp kQM.2
  have hkQM_sq : ((kQM : Max3.M) : J) * ((kQM : Max3.M) : J) = 1 := by
    have h : kQM * kQM = 1 := by
      change Fd.φQ kQ * Fd.φQ kQ = 1
      rw [← map_mul, hkQ_sq, map_one]
    simpa using congrArg (fun z : ↥(Max3.Q.subgroupOf Max3.M) => ((z : Max3.M) : J)) h
  have hkQM_ne_z : ((kQM : Max3.M) : J) ≠ Max3.z := by
    intro h
    apply hkQ_ne_z
    exact Fd.φQ.injective ((φQ_eq_zQ_iff Fd kQ).mpr h)
  have hkQM_ne_one : ((kQM : Max3.M) : J) ≠ 1 := by
    intro h
    apply hk1
    have h1 : kQM = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
    have hkQ_one : kQ = 1 := Fd.φQ.injective (by
      change kQM = Fd.φQ (1 : S.toSetting.Q)
      rw [map_one]
      exact h1)
    calc k = ((kQ : S.toSetting.M) : G) := hkQ_coe.symm
      _ = 1 := by rw [hkQ_one]; rfl
  obtain ⟨m₁, hm₁M, hm₁⟩ :=
    exists_conj_q0_of_mem_Q Fd hkQM_mem hkQM_sq hkQM_ne_z hkQM_ne_one
  let h0Q : S.toSetting.Q := toSettingQ S S.h₀_mem_Q
  have hh0Q_coe : ((h0Q : S.toSetting.M) : G) = S.h₀ := rfl
  have hh0Q_sq : h0Q * h0Q = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show S.h₀ * S.h₀ = 1
    rw [← pow_two, ← S.orderOf_h₀, pow_orderOf_eq_one]
  have hh0Q_ne_z : h0Q ≠ S.toSetting.zQ := by
    intro h
    apply S.h₀_ne_z
    calc S.h₀ = ((h0Q : S.toSetting.M) : G) := hh0Q_coe.symm
      _ = ((S.toSetting.zQ : S.toSetting.M) : G) := by rw [h]
      _ = S.z := rfl
  have hh0Q_ne_one : h0Q ≠ 1 := by
    intro h
    have hG : S.h₀ = 1 := by
      calc S.h₀ = ((h0Q : S.toSetting.M) : G) := hh0Q_coe.symm
        _ = 1 := by rw [h]; rfl
    have hord := S.orderOf_h₀
    rw [hG, orderOf_one] at hord
    exact absurd hord (by norm_num)
  let h0QM : ↥(Max3.Q.subgroupOf Max3.M) := Fd.φQ h0Q
  have hh0QM_mem : ((h0QM : Max3.M) : J) ∈ Max3.Q :=
    Subgroup.mem_subgroupOf.mp h0QM.2
  have hh0QM_sq : ((h0QM : Max3.M) : J) * ((h0QM : Max3.M) : J) = 1 := by
    have h : h0QM * h0QM = 1 := by
      change Fd.φQ h0Q * Fd.φQ h0Q = 1
      rw [← map_mul, hh0Q_sq, map_one]
    simpa using congrArg (fun z : ↥(Max3.Q.subgroupOf Max3.M) => ((z : Max3.M) : J)) h
  have hh0QM_ne_z : ((h0QM : Max3.M) : J) ≠ Max3.z := by
    intro h
    apply hh0Q_ne_z
    exact Fd.φQ.injective ((φQ_eq_zQ_iff Fd h0Q).mpr h)
  have hh0QM_ne_one : ((h0QM : Max3.M) : J) ≠ 1 := by
    intro h
    apply hh0Q_ne_one
    have h1 : h0QM = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
    exact Fd.φQ.injective (by
      change h0QM = Fd.φQ (1 : S.toSetting.Q)
      rw [map_one]
      exact h1)
  obtain ⟨m₂, hm₂M, hm₂⟩ :=
    exists_conj_q0_of_mem_Q Fd hh0QM_mem hh0QM_sq hh0QM_ne_z hh0QM_ne_one
  let m₁M : Max3.M := ⟨m₁, hm₁M⟩
  let m₂M : Max3.M := ⟨m₂, hm₂M⟩
  obtain ⟨h1', h1'mem⟩ := Fd.exists_fst m₁M
  obtain ⟨h2', h2'mem⟩ := Fd.exists_fst m₂M
  have h1_conj : Fd.φQ (conjAut S.toSetting.normal h1' kQ) = q0QM := by
    rw [((Fd.mem_F_iff h1' m₁M).mp h1'mem).2 kQ]
    apply Subtype.ext
    apply Subtype.ext
    rw [conjAut_apply]
    simpa [m₁M, kQM, q0QM, q0M] using hm₁
  have h2_conj : Fd.φQ (conjAut S.toSetting.normal h2' h0Q) = q0QM := by
    rw [((Fd.mem_F_iff h2' m₂M).mp h2'mem).2 h0Q]
    apply Subtype.ext
    apply Subtype.ext
    rw [conjAut_apply]
    simpa [m₂M, h0QM, q0QM, q0M] using hm₂
  have hconj_eq : conjAut S.toSetting.normal h1' kQ =
      conjAut S.toSetting.normal h2' h0Q :=
    Fd.φQ.injective (h1_conj.trans h2_conj.symm)
  let n : S.toSetting.M := h2'⁻¹ * h1'
  have hn_conj : n * (kQ : S.toSetting.M) * n⁻¹ = (h0Q : S.toSetting.M) := by
    have h := congrArg (fun z : S.toSetting.Q => (z : S.toSetting.M)) hconj_eq
    rw [conjAut_apply, conjAut_apply] at h
    calc n * (kQ : S.toSetting.M) * n⁻¹
        = h2'⁻¹ * (h1' * (kQ : S.toSetting.M) * h1'⁻¹) * h2' := by
          change (h2'⁻¹ * h1') * (kQ : S.toSetting.M) * (h2'⁻¹ * h1')⁻¹ = _
          group
      _ = h2'⁻¹ * (h2' * (h0Q : S.toSetting.M) * h2'⁻¹) * h2' := by rw [h]
      _ = (h0Q : S.toSetting.M) := by group
  let g0 : G := n * y
  have hg0_z : g0 * S.z * g0⁻¹ = ((h0Q : S.toSetting.M) : G) := by
    calc g0 * S.z * g0⁻¹
        = (n : G) * (y * S.z * y⁻¹) * (n : G)⁻¹ := by
          rw [show g0 = (n : G) * y from rfl, mul_inv_rev]
          group
      _ = (n : G) * k * (n : G)⁻¹ := by rw [show y * S.z * y⁻¹ = k from rfl]
      _ = ((h0Q : S.toSetting.M) : G) := by
          calc (n : G) * k * (n : G)⁻¹
              = (n : G) * ((kQ : S.toSetting.M) : G) * (n : G)⁻¹ := by rw [hkQ_coe]
            _ = ((h0Q : S.toSetting.M) : G) := by
                simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
                  congrArg (fun z : S.toSetting.M => (z : G)) hn_conj
  have hg0_h0 : g0 * ((h0Q : S.toSetting.M) : G) * g0⁻¹ = S.z := by
    calc g0 * ((h0Q : S.toSetting.M) : G) * g0⁻¹
        = (n : G) * (y * ((h0Q : S.toSetting.M) : G) * y⁻¹) * (n : G)⁻¹ := by
          rw [show g0 = (n : G) * y from rfl, mul_inv_rev]
          group
      _ = (n : G) * S.z * (n : G)⁻¹ := by
          rw [show y * ((h0Q : S.toSetting.M) : G) * y⁻¹ = S.z by
            rw [hh0Q_coe]
            exact hyz]
      _ = S.z := by
          have hnz : n * S.toSetting.zM = S.toSetting.zM * n :=
            Subgroup.mem_center_iff.mp S.toSetting.zM_mem_center n
          have hnzG : (n : G) * S.z = S.z * (n : G) := by
            simpa [S.toSetting.coe_zM] using
              congrArg (fun z : S.toSetting.M => (z : G)) hnz
          calc (n : G) * S.z * (n : G)⁻¹ = (S.z * (n : G)) * (n : G)⁻¹ := by rw [hnzG]
            _ = S.z := by group
  let h₁ : S.toSetting.Q := conjAut S.toSetting.normal h2' h0Q
  let h2G : G := h2'
  let g : G := h2G * g0 * h2G⁻¹
  have h₁_coe : ((h₁ : S.toSetting.M) : G) =
      h2G * ((h0Q : S.toSetting.M) : G) * h2G⁻¹ := by
    change (((conjAut S.toSetting.normal h2' h0Q : S.toSetting.Q) : S.toSetting.M) : G) =
      (h2' : G) * ((h0Q : S.toSetting.M) : G) * (h2' : G)⁻¹
    exact congrArg (fun z : S.toSetting.M => (z : G))
      (conjAut_apply S.toSetting.normal h2' h0Q)
  have h2'z : h2G * S.z = S.z * h2G := by
    simpa [h2G, S.toSetting.coe_zM] using congrArg (fun z : S.toSetting.M => (z : G))
      (Subgroup.mem_center_iff.mp S.toSetting.zM_mem_center h2')
  have h2'z_inv : h2G⁻¹ * S.z = S.z * h2G⁻¹ := by
    calc h2G⁻¹ * S.z = h2G⁻¹ * (S.z * h2G) * h2G⁻¹ := by group
      _ = h2G⁻¹ * (h2G * S.z) * h2G⁻¹ := by rw [← h2'z]
      _ = S.z * h2G⁻¹ := by group
  refine ⟨h₁, ?_, g, ?_, ?_⟩
  · simpa [h₁, q0QM, q0M] using congrArg (fun z : ↥(Max3.Q.subgroupOf Max3.M) =>
      ((z : Max3.M) : J)) h2_conj
  · calc g * S.z * g⁻¹
        = h2G * (g0 * S.z * g0⁻¹) * h2G⁻¹ := by
          rw [show g = h2G * g0 * h2G⁻¹ from rfl]
          calc h2G * g0 * h2G⁻¹ * S.z * (h2G * g0 * h2G⁻¹)⁻¹
              = h2G * g0 * (h2G⁻¹ * S.z) * h2G * g0⁻¹ * h2G⁻¹ := by group
            _ = h2G * g0 * (S.z * h2G⁻¹) * h2G * g0⁻¹ * h2G⁻¹ := by rw [h2'z_inv]
            _ = h2G * (g0 * S.z * g0⁻¹) * h2G⁻¹ := by group
      _ = h2G * ((h0Q : S.toSetting.M) : G) * h2G⁻¹ := by rw [hg0_z]
      _ = ((h₁ : S.toSetting.M) : G) := h₁_coe.symm
  · calc g * ((h₁ : S.toSetting.M) : G) * g⁻¹
        = h2G * (g0 * ((h0Q : S.toSetting.M) : G) * g0⁻¹) * h2G⁻¹ := by
          rw [show g = h2G * g0 * h2G⁻¹ from rfl, h₁_coe]
          group
      _ = h2G * S.z * h2G⁻¹ := by rw [hg0_h0]
      _ = S.z := by
          calc h2G * S.z * h2G⁻¹ = (S.z * h2G) * h2G⁻¹ := by rw [h2'z]
            _ = S.z := by group

private theorem fiber_fst_ncard (Fd : FibreData S) {h : S.toSetting.M} {m : Max3.M}
    (hm : (h, m) ∈ Fd.F) :
    {m' : Max3.M | (h, m') ∈ Fd.F}.ncard = 2 := by
  have ha : ((1 : S.toSetting.M), aM) ∈ Fd.F := by
    refine (Fd.one_mk_mem_F_iff aM).mpr (Or.inr ?_)
    rfl
  have hset : {m' : Max3.M | (h, m') ∈ Fd.F} = {m, m * aM} := by
    ext m'
    constructor
    · intro hm'
      have hprod : ((h, m) : S.toSetting.M × Max3.M)⁻¹ * (h, m') ∈ Fd.F :=
        Fd.F.mul_mem (Fd.F.inv_mem hm) hm'
      have h1 : ((1 : S.toSetting.M), m⁻¹ * m') ∈ Fd.F := by
        convert hprod using 1
        apply Prod.ext <;> simp
      rcases (Fd.one_mk_mem_F_iff (m⁻¹ * m')).mp h1 with h1' | h1'
      · left
        calc m' = m * (m⁻¹ * m') := by group
          _ = m * 1 := by rw [h1']
          _ = m := by rw [mul_one]
      · right
        have hM : m⁻¹ * m' = aM := Subtype.ext h1'
        calc m' = m * (m⁻¹ * m') := by group
          _ = m * aM := by rw [hM]
    · rintro (rfl | rfl)
      · exact hm
      · simpa using Fd.F.mul_mem hm ha
  rw [hset]
  exact Set.ncard_pair (by
    intro hEq
    exact aM_ne_one (mul_left_cancel (by
      calc m * aM = m := hEq.symm
        _ = m * 1 := by rw [mul_one])))

private theorem fiber_snd_ncard (Fd : FibreData S) {h : S.toSetting.M} {m : Max3.M}
    (hm : (h, m) ∈ Fd.F) :
    {h' : S.toSetting.M | (h', m) ∈ Fd.F}.ncard = 2 := by
  have hz : (S.toSetting.zM, (1 : Max3.M)) ∈ Fd.F := by
    refine (Fd.mk_one_mem_F_iff S.toSetting.zM).mpr (Or.inr ?_)
    rw [S.toSetting.coe_zM, S.toSetting_z]
  have hset : {h' : S.toSetting.M | (h', m) ∈ Fd.F} = {h, h * S.toSetting.zM} := by
    ext h'
    constructor
    · intro hm'
      have hprod : ((h', m) : S.toSetting.M × Max3.M) * (h, m)⁻¹ ∈ Fd.F :=
        Fd.F.mul_mem hm' (Fd.F.inv_mem hm)
      have h1 : (h' * h⁻¹, (1 : Max3.M)) ∈ Fd.F := by
        convert hprod using 1
        apply Prod.ext <;> simp
      rcases (Fd.mk_one_mem_F_iff (h' * h⁻¹)).mp h1 with h1' | h1'
      · left
        calc h' = (h' * h⁻¹) * h := by group
          _ = 1 * h := by rw [h1']
          _ = h := by rw [one_mul]
      · right
        have hM : h' * h⁻¹ = S.toSetting.zM := Subtype.ext h1'
        calc h' = (h' * h⁻¹) * h := by group
          _ = S.toSetting.zM * h := by rw [hM]
          _ = h * S.toSetting.zM :=
              (Subgroup.mem_center_iff.mp S.toSetting.zM_mem_center h).symm
    · rintro (rfl | rfl)
      · exact hm
      · simpa using Fd.F.mul_mem hm hz
  rw [hset]
  exact Set.ncard_pair (by
    intro hEq
    exact zM_ne_one (mul_left_cancel (by
      calc h * S.toSetting.zM = h := hEq.symm
        _ = h * 1 := by rw [mul_one])))

private noncomputable def CH (h₁ : S.toSetting.Q) : Subgroup G :=
  Subgroup.centralizer ({S.z, ((h₁ : S.toSetting.M) : G)} : Set G)

private noncomputable def CM : Subgroup Max3.M :=
  Subgroup.centralizer ({(q0M : Max3.M)} : Set Max3.M)

private noncomputable def nCH (h₁ : S.toSetting.Q) (w : S.toSetting.M) : ℕ :=
  {x : G | x ∈ CH h₁ ∧ x ^ 2 = (w : G)}.ncard

private theorem nCH_eq_H_ncard (h1 : S.toSetting.Q) (w : S.toSetting.M) :
    nCH h1 w = {h : S.toSetting.M | ((h : S.toSetting.M) : G) ∈ CH h1 ∧
      ((h : S.toSetting.M) : G) ^ 2 = (w : G)}.ncard := by
  let f : (x : G) → x ∈ {x : G | x ∈ CH h1 ∧ x ^ 2 = (w : G)} → S.toSetting.M :=
    fun x hx => ⟨x, by
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hx.1) S.z (by simp)).symm⟩
  apply Set.ncard_congr f
  · intro x hx
    exact ⟨hx.1, hx.2⟩
  · intro x y hx hy hxy
    exact congrArg (fun z : S.toSetting.M => (z : G)) hxy
  · intro y hy
    exact ⟨(y : G), ⟨hy.1, hy.2⟩, rfl⟩

private theorem mem_CH_iff (h1 : S.toSetting.Q) (h : S.toSetting.M) :
    ((h : G) ∈ CH h1) ↔ h * h1 = h1 * h := by
  rw [CH, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc
    have := hc ((h1 : S.toSetting.M) : G) (by simp)
    exact Subtype.ext this.symm
  · intro hc
    intro y hy
    rcases hy with rfl | rfl
    · have hz := Subgroup.mem_center_iff.mp S.toSetting.zM_mem_center h
      simpa [Subgroup.coe_mul] using congrArg (fun x : S.toSetting.M => (x : G)) hz.symm
    · change ((h1 : S.toSetting.M) : G) * (h : G) = (h : G) * ((h1 : S.toSetting.M) : G)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
      exact congrArg (fun x : S.toSetting.M => (x : G)) hc.symm

private noncomputable def nCM (w : Max3.M) : ℕ :=
  {m : Max3.M | m ∈ CM ∧ m ^ 2 = w}.ncard

private noncomputable def nCMeps (w : Max3.M) (e : ℕ) : ℕ :=
  {m : Max3.M | m ∈ CM ∧ m ^ 2 = w ∧ eps (kap m) = e}.ncard

private theorem eps_eq_zero_or_one (σ : alternatingGroup (Fin 9)) :
    eps σ = 0 ∨ eps σ = 1 := by
  by_cases h : (σ : Equiv.Perm (Fin 9)).cycleType = {2, 2}
  · exact Or.inr ((eps_eq_one_iff σ).mpr h)
  · exact Or.inl ((eps_eq_zero_iff σ).mpr h)

private theorem ncard_eq_two_mul_ncard_of_fiber_two
    {X Y : Type} [Finite X] [Finite Y] (f : X → Y) (s : Set X) (t : Set Y)
    (hmaps : Set.MapsTo f s t)
    (hfib : ∀ y, y ∈ t → (s ∩ f ⁻¹' {y}).ncard = 2) :
    s.ncard = 2 * t.ncard := by
  classical
  have hsf : s.Finite := Set.toFinite s
  have htf : t.Finite := Set.toFinite t
  rw [Set.ncard_eq_toFinset_card s hsf, Set.ncard_eq_toFinset_card t htf]
  have hmaps' : Set.MapsTo f (hsf.toFinset : Set X) (htf.toFinset : Set Y) := by
    intro x hx
    exact htf.mem_toFinset.mpr (hmaps (hsf.mem_toFinset.mp hx))
  rw [Finset.card_eq_sum_card_fiberwise hmaps']
  have hfib' : ∀ y ∈ htf.toFinset, ((hsf.toFinset.filter (fun x => f x = y)).card) = 2 := by
    intro y hy
    have hyt : y ∈ t := htf.mem_toFinset.mp hy
    rw [← hfib y hyt]
    rw [Set.ncard_eq_toFinset_card (s ∩ f ⁻¹' {y}) (Set.toFinite _)]
    congr 1
    ext x
    simp [hsf.mem_toFinset]
  calc ∑ y ∈ htf.toFinset, ((hsf.toFinset.filter (fun x => f x = y)).card)
      = ∑ _y ∈ htf.toFinset, 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hfib' y hy
    _ = 2 * htf.toFinset.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

private theorem ncard_eq_of_partners
    {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (F : Subgroup (X × Y))
    (hX : ∀ x : X, {y : Y | (x, y) ∈ F}.ncard = 2)
    (hY : ∀ y : Y, {x : X | (x, y) ∈ F}.ncard = 2)
    (A : X → Prop) (B : Y → Prop)
    (hAB : ∀ x y, (x, y) ∈ F → (A x ↔ B y)) :
    {x : X | A x}.ncard = {y : Y | B y}.ncard := by
  let S : Set (X × Y) := {p | p ∈ F ∧ A p.1}
  have hS1 : S.ncard = 2 * {x : X | A x}.ncard := by
    apply ncard_eq_two_mul_ncard_of_fiber_two (f := fun p : X × Y => p.1) S {x : X | A x}
    · intro p hp
      exact hp.2
    · intro x hx
      calc (S ∩ (fun p : X × Y => p.1) ⁻¹' {x}).ncard
          = {y : Y | (x, y) ∈ F}.ncard := by
            apply Set.ncard_congr (fun p _ => p.2)
            · rintro p hp
              rcases hp with ⟨hpS, hpx⟩
              have hp1 : p.1 = x := hpx
              have hp_eq : p = (x, p.2) := Prod.ext hp1 rfl
              have hF : p ∈ F := hpS.1
              rwa [hp_eq] at hF
            · rintro p q hp hq hpq
              rcases hp with ⟨-, hpx⟩
              rcases hq with ⟨-, hqx⟩
              have hp1 : p.1 = x := hpx
              have hq1 : q.1 = x := hqx
              apply Prod.ext
              · rw [hp1, hq1]
              · exact hpq
            · rintro y hy
              exact ⟨(x, y), ⟨⟨by simpa using hy, hx⟩, rfl⟩, rfl⟩
        _ = 2 := hX x
  have hS2 : S.ncard = 2 * {y : Y | B y}.ncard := by
    apply ncard_eq_two_mul_ncard_of_fiber_two (f := fun p : X × Y => p.2) S {y : Y | B y}
    · intro p hp
      exact (hAB p.1 p.2 hp.1).mp hp.2
    · intro y hy
      calc (S ∩ (fun p : X × Y => p.2) ⁻¹' {y}).ncard
          = {x : X | (x, y) ∈ F}.ncard := by
            apply Set.ncard_congr (fun p _ => p.1)
            · rintro p hp
              rcases hp with ⟨hpS, hpy⟩
              have hp2 : p.2 = y := hpy
              have hp_eq : p = (p.1, y) := Prod.ext rfl hp2
              have hF : p ∈ F := hpS.1
              rwa [hp_eq] at hF
            · rintro p q hp hq hpq
              rcases hp with ⟨-, hpy⟩
              rcases hq with ⟨-, hqy⟩
              apply Prod.ext
              · exact hpq
              · have hp2 : p.2 = y := hpy
                have hq2 : q.2 = y := hqy
                rw [hp2, hq2]
            · rintro x hx
              exact ⟨(x, y), ⟨⟨by simpa using hx,
                (hAB x y (by simpa using hx)).mpr hy⟩, rfl⟩, rfl⟩
        _ = 2 := hY y
  omega

private theorem ncard_conj_sqrt_eq
    {X : Type} [Group X] [Finite X] (g : X) (C : Subgroup X)
    (hC : ∀ x, x ∈ C ↔ g * x * g⁻¹ ∈ C)
    (P : X → Prop) (hP : ∀ x, P (g * x * g⁻¹) ↔ P x) (w : X) :
    {x : X | x ∈ C ∧ x ^ 2 = w ∧ P x}.ncard =
      {x : X | x ∈ C ∧ x ^ 2 = g * w * g⁻¹ ∧ P x}.ncard := by
  apply Set.ncard_congr (fun x _ => g * x * g⁻¹)
  · rintro x ⟨hxC, hx2, hxP⟩
    exact ⟨(hC x).mp hxC, by
      rw [show (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ from by
        rw [pow_two, pow_two]
        group, hx2], (hP x).mpr hxP⟩
  · rintro x y _ _ hxy
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hxy]
      _ = y := by group
  · intro y hy
    have hgy : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    refine ⟨g⁻¹ * y * g, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (hC (g⁻¹ * y * g)).mpr (by rw [hgy]; exact hy.1)
    · rw [show (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g from by
        rw [pow_two, pow_two]
        group, hy.2.1]
      group
    · exact (hP (g⁻¹ * y * g)).mp (by rw [hgy]; exact hy.2.2)
    · group

private theorem exists_twisted_eq (Fd : FibreData S) (tw : Fd.TwistedSquares)
    {h : S.toSetting.M} {m : Max3.M} (hm : (h, m) ∈ Fd.F)
    (hθ : Fd.θ h ^ 2 = 1) :
    ∃ x : S.toSetting.Q, (x : S.toSetting.M) = h ^ 2 * S.toSetting.zM ^ eps (Fd.θ h) ∧
      Fd.φQ x = (m ^ 2 : Max3.M) := by
  obtain ⟨x, hxG, hxJ⟩ := tw h m hm hθ
  refine ⟨x, ?_, ?_⟩
  · apply Subtype.ext
    change ((x : S.toSetting.M) : G) =
      ((h ^ 2 * S.toSetting.zM ^ eps (Fd.θ h) : S.toSetting.M) : G)
    simpa [S.toSetting.coe_zM, Subgroup.coe_pow, Subgroup.coe_mul] using hxG
  · change ((Fd.φQ x : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) = (m ^ 2 : Max3.M)
    exact Subtype.ext (by simpa [Subgroup.coe_pow] using hxJ)

private theorem nCM_eq_add_eps (w : Max3.M) :
    nCM w = nCMeps w 0 + nCMeps w 1 := by
  rw [nCM, nCMeps, nCMeps]
  let A : Set Max3.M := {m | m ∈ CM ∧ m ^ 2 = w ∧ eps (kap m) = 0}
  let B : Set Max3.M := {m | m ∈ CM ∧ m ^ 2 = w ∧ eps (kap m) = 1}
  have hset : {m : Max3.M | m ∈ CM ∧ m ^ 2 = w} = A ∪ B := by
    ext m
    constructor
    · intro hm
      rcases eps_eq_zero_or_one (kap m) with h | h
      · exact Or.inl ⟨hm.1, hm.2, h⟩
      · exact Or.inr ⟨hm.1, hm.2, h⟩
    · rintro (h | h)
      · exact ⟨h.1, h.2.1⟩
      · exact ⟨h.1, h.2.1⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext m
    simp [A, B]
    intro h0 h1
    omega
  rw [hset, Set.ncard_union_eq hdisj]

private theorem h_sq_z_iff (Fd : FibreData S) (tw : Fd.TwistedSquares)
    (hinv : ∀ n : Max3.M, n * n = 1 →
      (Max3.InvRep.kap n : Equiv.Perm (Fin 9)).cycleType ≠ {2, 2})
    {h : S.toSetting.M} {m : Max3.M} (hm : (h, m) ∈ Fd.F) :
    h ^ 2 = S.toSetting.zM ↔ m ^ 2 = aM ∧ eps (kap m) = 0 := by
  have hkap : kap m = Fd.θ h := ((Fd.mem_F_iff h m).mp hm).1
  have hzM2 : S.toSetting.zM * S.toSetting.zM = 1 := by
    apply Subtype.ext
    change (S.toSetting.zM : G) * (S.toSetting.zM : G) = 1
    rw [S.toSetting.coe_zM]
    exact S.toSetting.z_mul_z
  constructor
  · intro hz
    have hθ : Fd.θ h ^ 2 = 1 := by
      rw [← map_pow, hz]
      rw [← MonoidHom.mem_ker, Fd.θ_ker]
      exact S.toSetting.zM_mem_Q
    obtain ⟨x, hxH, hxM⟩ := exists_twisted_eq Fd tw hm hθ
    have hxH' : (x : S.toSetting.M) = S.toSetting.zM * S.toSetting.zM ^ eps (Fd.θ h) := by
      rw [hxH, hz]
    rcases eps_eq_zero_or_one (Fd.θ h) with he | he
    · have hx_z : (x : S.toSetting.M) = S.toSetting.zM := by
        rw [hxH', he, pow_zero, mul_one]
      have hx_zQ : x = S.toSetting.zQ := by
        apply Subtype.ext
        change (x : S.toSetting.M) = S.toSetting.zM
        exact hx_z
      have hm2 : m ^ 2 = aM := by
        calc m ^ 2 = Fd.φQ x := hxM.symm
          _ = Fd.φQ S.toSetting.zQ := by rw [hx_zQ]
          _ = aM := Subtype.ext Fd.φQ_z
      exact ⟨hm2, by rw [hkap, he]⟩
    · exfalso
      have hx_one : x = 1 := by
        apply Subtype.ext
        change (x : S.toSetting.M) = 1
        rw [hxH', he, pow_one, hzM2]
      have hm2 : m ^ 2 = 1 := by
        calc m ^ 2 = Fd.φQ x := hxM.symm
          _ = Fd.φQ 1 := by rw [hx_one]
          _ = 1 := by rw [map_one]; rfl
      have hcycle : (kap m : Equiv.Perm (Fin 9)).cycleType = {2, 2} :=
        (eps_eq_one_iff (kap m)).mp (by rw [hkap, he])
      exact hinv m (by simpa [pow_two] using hm2) hcycle
  · rintro ⟨hm2, he⟩
    have hθ : Fd.θ h ^ 2 = 1 := by
      rw [← hkap]
      rw [← map_pow, hm2]
      exact (kap_eq_one_iff).mpr Max3.z_mem_Q
    obtain ⟨x, hxH, hxM⟩ := exists_twisted_eq Fd tw hm hθ
    have hx_zQ : x = S.toSetting.zQ := by
      apply Fd.φQ.injective
      apply Subtype.ext
      rw [hxM, hm2]
      apply Subtype.ext
      exact Fd.φQ_z.symm
    have he' : eps (Fd.θ h) = 0 := by rw [← hkap, he]
    calc h ^ 2 = h ^ 2 * S.toSetting.zM ^ eps (Fd.θ h) := by rw [he', pow_zero, mul_one]
      _ = (x : S.toSetting.M) := hxH.symm
      _ = S.toSetting.zM := by rw [hx_zQ]; rfl

private theorem h_sq_h1_iff (Fd : FibreData S) (tw : Fd.TwistedSquares)
    {h1 : S.toSetting.Q} (hphi : Fd.φQ h1 = q0QM)
    {h : S.toSetting.M} {m : Max3.M} (hm : (h, m) ∈ Fd.F) :
    h ^ 2 = (h1 : S.toSetting.M) ↔
      (m ^ 2 = q0M ∧ eps (kap m) = 0) ∨
        (m ^ 2 = q0M * aM ∧ eps (kap m) = 1) := by
  have hkap : kap m = Fd.θ h := ((Fd.mem_F_iff h m).mp hm).1
  constructor
  · intro hz
    have hθ : Fd.θ h ^ 2 = 1 := by
      rw [← map_pow, hz]
      rw [← MonoidHom.mem_ker, Fd.θ_ker]
      exact h1.2
    obtain ⟨x, hxH, hxM⟩ := exists_twisted_eq Fd tw hm hθ
    have hxH' : (x : S.toSetting.M) = (h1 : S.toSetting.M) * S.toSetting.zM ^ eps (Fd.θ h) := by
      rw [hxH, hz]
    rcases eps_eq_zero_or_one (Fd.θ h) with he | he
    · have hx_h1 : x = h1 := by
        apply Subtype.ext
        change (x : S.toSetting.M) = (h1 : S.toSetting.M)
        rw [hxH', he, pow_zero, mul_one]
      have hm2 : m ^ 2 = q0M := by
        calc m ^ 2 = ((Fd.φQ x : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) := hxM.symm
          _ = ((Fd.φQ h1 : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) := by rw [hx_h1]
          _ = (q0QM : Max3.M) := by rw [hphi]
          _ = q0M := rfl
      exact Or.inl ⟨hm2, by rw [hkap, he]⟩
    · have hx_h1z : x = h1 * S.toSetting.zQ := by
        apply Subtype.ext
        change (x : S.toSetting.M) =
          ((h1 * S.toSetting.zQ : S.toSetting.Q) : S.toSetting.M)
        rw [hxH', he, pow_one]
        rw [Subgroup.coe_mul]
        rfl
      have hm2 : m ^ 2 = q0M * aM := by
        calc m ^ 2 = ((Fd.φQ x : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) := hxM.symm
          _ = ((Fd.φQ (h1 * S.toSetting.zQ) : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) := by
              rw [hx_h1z]
          _ = ((Fd.φQ h1 * Fd.φQ S.toSetting.zQ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) := by
              rw [map_mul]
          _ = q0M * aM := by
              rw [Subgroup.coe_mul, hphi,
                show ((Fd.φQ S.toSetting.zQ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) = aM from
                  Subtype.ext Fd.φQ_z]
      exact Or.inr ⟨hm2, by rw [hkap, he]⟩
  · rintro (⟨hm2, he⟩ | ⟨hm2, he⟩)
    · have hθ : Fd.θ h ^ 2 = 1 := by
        rw [← hkap, ← map_pow, hm2]
        exact (kap_eq_one_iff).mpr (Max3.q_mem_Q 0)
      obtain ⟨x, hxH, hxM⟩ := exists_twisted_eq Fd tw hm hθ
      have hx_h1 : x = h1 := by
        apply Fd.φQ.injective
        apply Subtype.ext
        rw [hxM, hm2, hphi]
      have he' : eps (Fd.θ h) = 0 := by rw [← hkap, he]
      calc h ^ 2 = h ^ 2 * S.toSetting.zM ^ eps (Fd.θ h) := by rw [he', pow_zero, mul_one]
        _ = (x : S.toSetting.M) := hxH.symm
        _ = (h1 : S.toSetting.M) := by rw [hx_h1]
    · have hθ : Fd.θ h ^ 2 = 1 := by
        rw [← hkap, ← map_pow, hm2, map_mul]
        rw [show kap q0M = 1 from (kap_eq_one_iff).mpr (Max3.q_mem_Q 0),
          show kap aM = 1 from (kap_eq_one_iff).mpr Max3.z_mem_Q]
        rw [one_mul]
      obtain ⟨x, hxH, hxM⟩ := exists_twisted_eq Fd tw hm hθ
      have hx_h1z : x = h1 * S.toSetting.zQ := by
        apply Fd.φQ.injective
        apply Subtype.ext
        rw [hxM, hm2]
        rw [show ((Fd.φQ (h1 * S.toSetting.zQ) : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) =
            ((Fd.φQ h1 * Fd.φQ S.toSetting.zQ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) from by
              rw [map_mul]]
        rw [Subgroup.coe_mul, hphi,
          show ((Fd.φQ S.toSetting.zQ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) = aM from
            Subtype.ext Fd.φQ_z]
      have he' : eps (Fd.θ h) = 1 := by rw [← hkap, he]
      have hxH' : (x : S.toSetting.M) = h ^ 2 * S.toSetting.zM := by
        rw [hxH, he', pow_one]
      have hxH'' : (x : S.toSetting.M) = (h1 : S.toSetting.M) * S.toSetting.zM := by
        rw [hx_h1z, Subgroup.coe_mul]
        rfl
      exact mul_right_cancel (by rw [← hxH', hxH''])

private theorem nCH_z_eq_nCMeps_a0 (Fd : FibreData S) (tw : Fd.TwistedSquares)
    (hinv : ∀ n : Max3.M, n * n = 1 →
      (Max3.InvRep.kap n : Equiv.Perm (Fin 9)).cycleType ≠ {2, 2})
    (h1 : S.toSetting.Q) (hphi : Fd.φQ h1 = q0QM) :
    nCH h1 S.toSetting.zM = nCMeps aM 0 := by
  rw [nCH_eq_H_ncard]
  change {h : S.toSetting.M | ((h : S.toSetting.M) : G) ∈ CH h1 ∧
      ((h : S.toSetting.M) : G) ^ 2 = (S.toSetting.zM : G)}.ncard =
    {m : Max3.M | m ∈ CM ∧ m ^ 2 = aM ∧ eps (kap m) = 0}.ncard
  have hX : ∀ h : S.toSetting.M, {m : Max3.M | (h, m) ∈ Fd.F}.ncard = 2 := by
    intro h
    obtain ⟨m, hm⟩ := Fd.exists_snd h
    exact fiber_fst_ncard Fd hm
  have hY : ∀ m : Max3.M, {h : S.toSetting.M | (h, m) ∈ Fd.F}.ncard = 2 := by
    intro m
    obtain ⟨h, hm⟩ := Fd.exists_fst m
    exact fiber_snd_ncard Fd hm
  apply ncard_eq_of_partners Fd.F hX hY
    (A := fun h => ((h : S.toSetting.M) : G) ∈ CH h1 ∧
      ((h : S.toSetting.M) : G) ^ 2 = (S.toSetting.zM : G))
    (B := fun m => m ∈ CM ∧ m ^ 2 = aM ∧ eps (kap m) = 0)
  intro h m hm
  constructor
  · rintro ⟨hpCH, hpsq⟩
    have hcommM : h * h1 = h1 * h := (mem_CH_iff h1 h).mp hpCH
    have hcommG : ((h : S.toSetting.M) : G) * ((h1 : S.toSetting.M) : G) =
        ((h1 : S.toSetting.M) : G) * ((h : S.toSetting.M) : G) :=
      congrArg (fun x : S.toSetting.M => (x : G)) hcommM
    have hcommJ := (commute_iff Fd hm h1).mp hcommG
    have hmCH : m ∈ CM := by
      rw [CM, Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hcommJ' := hcommJ
      rw [hphi] at hcommJ'
      simpa [q0QM, q0M] using hcommJ'
    have hpsq' : h ^ 2 = S.toSetting.zM := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow] using hpsq
    exact ⟨hmCH, (h_sq_z_iff Fd tw hinv hm).mp hpsq'⟩
  · rintro ⟨hmCH, hm2, he⟩
    have hmCH' : m ∈ Subgroup.centralizer ({q0M} : Set Max3.M) := by
      simpa [CM] using hmCH
    have hcommM : m * q0M = q0M * m := by
      have := (Subgroup.mem_centralizer_iff.mp hmCH') q0M (by exact Set.mem_singleton _)
      exact this.symm
    have hcommJ : (m : J) *
        (((q0QM : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) =
        (((q0QM : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) * (m : J) := by
      simpa [q0QM, q0M] using congrArg (fun x : Max3.M => (x : J)) hcommM
    have hcommG : ((h : S.toSetting.M) : G) * ((h1 : S.toSetting.M) : G) =
        ((h1 : S.toSetting.M) : G) * ((h : S.toSetting.M) : G) := by
      apply (commute_iff Fd hm h1).mpr
      rw [← hphi] at hcommJ
      simpa using hcommJ
    have hpCH : ((h : S.toSetting.M) : G) ∈ CH h1 :=
      (mem_CH_iff h1 h).mpr (Subtype.ext hcommG)
    have hpsq : ((h : S.toSetting.M) : G) ^ 2 = (S.toSetting.zM : G) := by
      simpa [Subgroup.coe_pow] using
        congrArg (fun x : S.toSetting.M => (x : G))
          ((h_sq_z_iff Fd tw hinv hm).mpr ⟨hm2, he⟩)
    exact ⟨hpCH, hpsq⟩

private theorem nCH_h1_eq (Fd : FibreData S) (tw : Fd.TwistedSquares)
    (h1 : S.toSetting.Q) (hphi : Fd.φQ h1 = q0QM) :
    nCH h1 (h1 : S.toSetting.M) = nCMeps q0M 0 + nCMeps (q0M * aM) 1 := by
  rw [nCH_eq_H_ncard]
  have hX : ∀ h : S.toSetting.M, {m : Max3.M | (h, m) ∈ Fd.F}.ncard = 2 := by
    intro h
    obtain ⟨m, hm⟩ := Fd.exists_snd h
    exact fiber_fst_ncard Fd hm
  have hY : ∀ m : Max3.M, {h : S.toSetting.M | (h, m) ∈ Fd.F}.ncard = 2 := by
    intro m
    obtain ⟨h, hm⟩ := Fd.exists_fst m
    exact fiber_snd_ncard Fd hm
  let U1 : Set Max3.M := {m | m ∈ CM ∧ m ^ 2 = q0M ∧ eps (kap m) = 0}
  let U2 : Set Max3.M := {m | m ∈ CM ∧ m ^ 2 = q0M * aM ∧ eps (kap m) = 1}
  have hAB : ∀ h m, (h, m) ∈ Fd.F →
      ((((h : S.toSetting.M) : G) ∈ CH h1 ∧
        ((h : S.toSetting.M) : G) ^ 2 = ((h1 : S.toSetting.M) : G)) ↔
        (m ∈ U1 ∨ m ∈ U2)) := by
    intro h m hm
    constructor
    · rintro ⟨hpCH, hpsq⟩
      have hcommM : h * h1 = h1 * h := (mem_CH_iff h1 h).mp hpCH
      have hcommG : ((h : S.toSetting.M) : G) * ((h1 : S.toSetting.M) : G) =
          ((h1 : S.toSetting.M) : G) * ((h : S.toSetting.M) : G) :=
        congrArg (fun x : S.toSetting.M => (x : G)) hcommM
      have hcommJ := (commute_iff Fd hm h1).mp hcommG
      have hmCH : m ∈ CM := by
        rw [CM, Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        have hcommJ' := hcommJ
        rw [hphi] at hcommJ'
        simpa [q0QM, q0M] using hcommJ'
      have hpsq' : h ^ 2 = (h1 : S.toSetting.M) := by
        apply Subtype.ext
        exact hpsq
      rcases (h_sq_h1_iff Fd tw hphi hm).mp hpsq' with h | h
      · exact Or.inl ⟨hmCH, h⟩
      · exact Or.inr ⟨hmCH, h⟩
    · rintro (hmU | hmU)
      · have hmCH' : m ∈ Subgroup.centralizer ({q0M} : Set Max3.M) := by
          simpa [CM] using hmU.1
        have hcommM : m * q0M = q0M * m := by
          have := (Subgroup.mem_centralizer_iff.mp hmCH') q0M (by exact Set.mem_singleton _)
          exact this.symm
        have hcommJ : (m : J) *
            (((q0QM : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) =
            (((q0QM : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) * (m : J) := by
          simpa [q0QM, q0M] using congrArg (fun x : Max3.M => (x : J)) hcommM
        have hcommG : ((h : S.toSetting.M) : G) * ((h1 : S.toSetting.M) : G) =
            ((h1 : S.toSetting.M) : G) * ((h : S.toSetting.M) : G) := by
          apply (commute_iff Fd hm h1).mpr
          rw [← hphi] at hcommJ
          simpa using hcommJ
        have hpCH : ((h : S.toSetting.M) : G) ∈ CH h1 :=
          (mem_CH_iff h1 h).mpr (Subtype.ext hcommG)
        have hpsq : ((h : S.toSetting.M) : G) ^ 2 = ((h1 : S.toSetting.M) : G) :=
          congrArg (fun x : S.toSetting.M => (x : G))
            ((h_sq_h1_iff Fd tw hphi hm).mpr (Or.inl ⟨hmU.2.1, hmU.2.2⟩))
        exact ⟨hpCH, hpsq⟩
      · have hmCH' : m ∈ Subgroup.centralizer ({q0M} : Set Max3.M) := by
          simpa [CM] using hmU.1
        have hcommM : m * q0M = q0M * m := by
          have := (Subgroup.mem_centralizer_iff.mp hmCH') q0M (by exact Set.mem_singleton _)
          exact this.symm
        have hcommJ : (m : J) *
            (((q0QM : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) =
            (((q0QM : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) * (m : J) := by
          simpa [q0QM, q0M] using congrArg (fun x : Max3.M => (x : J)) hcommM
        have hcommG : ((h : S.toSetting.M) : G) * ((h1 : S.toSetting.M) : G) =
            ((h1 : S.toSetting.M) : G) * ((h : S.toSetting.M) : G) := by
          apply (commute_iff Fd hm h1).mpr
          rw [← hphi] at hcommJ
          simpa using hcommJ
        have hpCH : ((h : S.toSetting.M) : G) ∈ CH h1 :=
          (mem_CH_iff h1 h).mpr (Subtype.ext hcommG)
        have hpsq : ((h : S.toSetting.M) : G) ^ 2 = ((h1 : S.toSetting.M) : G) :=
          congrArg (fun x : S.toSetting.M => (x : G))
            ((h_sq_h1_iff Fd tw hphi hm).mpr (Or.inr ⟨hmU.2.1, hmU.2.2⟩))
        exact ⟨hpCH, hpsq⟩
  have hmain : {h : S.toSetting.M | ((h : S.toSetting.M) : G) ∈ CH h1 ∧
      ((h : S.toSetting.M) : G) ^ 2 = ((h1 : S.toSetting.M) : G)}.ncard =
      {m : Max3.M | m ∈ U1 ∨ m ∈ U2}.ncard :=
    ncard_eq_of_partners Fd.F hX hY
      (A := fun h => ((h : S.toSetting.M) : G) ∈ CH h1 ∧
        ((h : S.toSetting.M) : G) ^ 2 = ((h1 : S.toSetting.M) : G))
      (B := fun m => m ∈ U1 ∨ m ∈ U2) hAB
  have hdisj : Disjoint U1 U2 := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext m
    constructor
    · intro h
      rw [Set.mem_inter_iff] at h
      obtain ⟨⟨-, hm1, -⟩, ⟨-, hm2, -⟩⟩ := h
      have hq : q0M = q0M * aM := by
        calc q0M = m ^ 2 := hm1.symm
          _ = q0M * aM := hm2
      have ha : aM = 1 := mul_left_cancel (a := q0M) (by simpa using hq.symm)
      exact Max3.z_ne_one (by simpa [aM] using congrArg (fun x : Max3.M => (x : J)) ha)
    · intro h
      simp at h
  have hU : (U1 ∪ U2).ncard = U1.ncard + U2.ncard := Set.ncard_union_eq hdisj
  rw [hmain]
  change (U1 ∪ U2).ncard = nCMeps q0M 0 + nCMeps (q0M * aM) 1
  rw [hU]
  rfl
private theorem nCH_h1_eq_nCH_z (Fd : FibreData S) {h1 : S.toSetting.Q} {g : G}
    (hgz : g * S.z * g⁻¹ = ((h1 : S.toSetting.M) : G))
    (hgh : g * ((h1 : S.toSetting.M) : G) * g⁻¹ = S.z) :
    nCH h1 (h1 : S.toSetting.M) = nCH h1 S.toSetting.zM := by
  have hgz_inv : g⁻¹ * S.z * g = ((h1 : S.toSetting.M) : G) := by rw [← hgh]; group
  have hgh_inv : g⁻¹ * ((h1 : S.toSetting.M) : G) * g = S.z := by rw [← hgz]; group
  have hmap : (CH h1).map (MulAut.conj g).toMonoidHom ≤ CH h1 := by
    have h := Subgroup.map_centralizer_le_centralizer_image
      ({S.z, ((h1 : S.toSetting.M) : G)} : Set G) (MulAut.conj g).toMonoidHom
    have himg : (MulAut.conj g).toMonoidHom ''
        ({S.z, ((h1 : S.toSetting.M) : G)} : Set G) =
        ({S.z, ((h1 : S.toSetting.M) : G)} : Set G) := by
      ext y
      simp [MulAut.conj_apply, hgz, hgh]
      tauto
    rw [himg] at h
    simpa [CH] using h
  have hmap_inv : (CH h1).map (MulAut.conj g⁻¹).toMonoidHom ≤ CH h1 := by
    have h := Subgroup.map_centralizer_le_centralizer_image
      ({S.z, ((h1 : S.toSetting.M) : G)} : Set G) (MulAut.conj g⁻¹).toMonoidHom
    have himg : (MulAut.conj g⁻¹).toMonoidHom ''
        ({S.z, ((h1 : S.toSetting.M) : G)} : Set G) =
        ({S.z, ((h1 : S.toSetting.M) : G)} : Set G) := by
      ext y
      simp [MulAut.conj_apply, hgz_inv, hgh_inv]
      tauto
    rw [himg] at h
    simpa [CH] using h
  have hC : ∀ x : G, x ∈ CH h1 ↔ g * x * g⁻¹ ∈ CH h1 := by
    intro x
    constructor
    · intro hx
      exact hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    · intro hx
      have hx' : g⁻¹ * (g * x * g⁻¹) * g ∈ CH h1 := by
        apply hmap_inv
        exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply]⟩
      have hx'' : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [hx''] at hx'
  have h := ncard_conj_sqrt_eq (X := G) g (CH h1) hC (fun _ => True) (fun _ => Iff.rfl)
    (S.toSetting.zM : G)
  rw [show g * (S.toSetting.zM : G) * g⁻¹ = ((h1 : S.toSetting.M) : G) from by
    simpa [S.toSetting.coe_zM] using hgz] at h
  have h' : {x : G | x ∈ CH h1 ∧ x ^ 2 = S.z}.ncard =
      {x : G | x ∈ CH h1 ∧ x ^ 2 = ((h1 : S.toSetting.M) : G)}.ncard := by
    simpa using h
  simpa [nCH, S.toSetting.coe_zM, S.toSetting_z] using h'.symm

private theorem aM_sq : aM * aM = 1 := by
  apply Subtype.ext
  exact Max3.z_mul_self

private theorem aM_central (m : Max3.M) : m * aM = aM * m :=
  Subgroup.mem_center_iff.mp Max3.z_mem_center_M m

private theorem centralizer_q0a_eq_CM :
    Subgroup.centralizer ({q0M * aM} : Set Max3.M) = CM := by
  ext m
  rw [CM, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc m * q0M = (m * (q0M * aM)) * aM := by
          rw [mul_assoc, mul_assoc, aM_sq, mul_one]
      _ = ((q0M * aM) * m) * aM := by rw [h]
      _ = q0M * (aM * m) * aM := by group
      _ = q0M * (m * aM) * aM := by rw [← aM_central m]
      _ = q0M * ((m * aM) * aM) := by rw [mul_assoc]
      _ = q0M * m := by
          rw [show (m * aM) * aM = m from by rw [mul_assoc, aM_sq, mul_one]]
  · intro h
    calc m * (q0M * aM) = (m * q0M) * aM := by group
      _ = (q0M * m) * aM := by rw [h]
      _ = q0M * (aM * m) := by
          calc q0M * m * aM = q0M * (m * aM) := by group
            _ = q0M * (aM * m) := by rw [aM_central m]
      _ = (q0M * aM) * m := by group

private theorem nCMeps_q0a_eq (hc : ∃ c ∈ Max3.Q,
    c * Max3.q 0 * c⁻¹ = Max3.q 0 * Max3.z) :
    nCMeps (q0M * aM) 1 = nCMeps q0M 1 := by
  obtain ⟨c, hcQ, hcJ⟩ := hc
  let cM : Max3.M := ⟨c, Max3.Q_le_M hcQ⟩
  have hc1 : kap cM = 1 := (kap_eq_one_iff).mpr hcQ
  have hcM : cM * q0M * cM⁻¹ = q0M * aM := by
    apply Subtype.ext
    simpa [cM, q0M, aM, Subgroup.coe_mul, Subgroup.coe_inv] using hcJ
  have hcM_inv : cM⁻¹ * q0M * cM = q0M * aM := by
    have h : (cM⁻¹ * q0M * cM) * aM = q0M := by
      calc (cM⁻¹ * q0M * cM) * aM
          = cM⁻¹ * q0M * (cM * aM) := by group
        _ = cM⁻¹ * q0M * (aM * cM) := by rw [aM_central cM]
        _ = cM⁻¹ * (q0M * aM) * cM := by group
        _ = cM⁻¹ * (cM * q0M * cM⁻¹) * cM := by rw [← hcM]
        _ = q0M := by group
    calc cM⁻¹ * q0M * cM = (cM⁻¹ * q0M * cM) * (aM * aM) := by
          rw [aM_sq, mul_one]
      _ = ((cM⁻¹ * q0M * cM) * aM) * aM := by group
      _ = q0M * aM := by rw [h]
  have hmap : CM.map (MulAut.conj cM).toMonoidHom ≤ CM := by
    have h := Subgroup.map_centralizer_le_centralizer_image ({q0M} : Set Max3.M)
      (MulAut.conj cM).toMonoidHom
    have himg : (MulAut.conj cM).toMonoidHom '' ({q0M} : Set Max3.M) = {q0M * aM} := by
      ext x
      simp [MulAut.conj_apply, hcM]
    rw [himg, centralizer_q0a_eq_CM] at h
    exact h
  have hmap_inv : CM.map (MulAut.conj cM⁻¹).toMonoidHom ≤ CM := by
    have h := Subgroup.map_centralizer_le_centralizer_image ({q0M} : Set Max3.M)
      (MulAut.conj cM⁻¹).toMonoidHom
    have himg : (MulAut.conj cM⁻¹).toMonoidHom '' ({q0M} : Set Max3.M) =
        {q0M * aM} := by
      ext x
      simp [MulAut.conj_apply, hcM_inv]
    rw [himg, centralizer_q0a_eq_CM] at h
    exact h
  have hC : ∀ x : Max3.M, x ∈ CM ↔ cM * x * cM⁻¹ ∈ CM := by
    intro x
    constructor
    · intro hx
      exact hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    · intro hx
      have hx' : cM⁻¹ * (cM * x * cM⁻¹) * cM ∈ CM :=
        hmap_inv (Subgroup.mem_map.mpr ⟨cM * x * cM⁻¹, hx, rfl⟩)
      have hx'' : cM⁻¹ * (cM * x * cM⁻¹) * cM = x := by group
      rwa [hx''] at hx'
  have hP : ∀ x : Max3.M, eps (kap (cM * x * cM⁻¹)) = 1 ↔ eps (kap x) = 1 := by
    intro x
    have hk : kap (cM * x * cM⁻¹) = kap x := by
      rw [map_mul, map_mul, map_inv, hc1]
      group
    rw [hk]
  have h := ncard_conj_sqrt_eq (X := Max3.M) cM CM hC
    (fun m => eps (kap m) = 1) hP q0M
  rw [hcM] at h
  simpa [nCMeps] using h.symm

private theorem conj_M_mem (gJ : J) (hg1 : gJ * Max3.z * gJ⁻¹ = Max3.q 0)
    (hg2 : gJ * Max3.q 0 * gJ⁻¹ = Max3.z)
    (hCM : Subgroup.centralizer ({Max3.z} : Set J) = Max3.M) {m : Max3.M} (hm : m ∈ CM) :
    ∃ hmem : gJ * (m : J) * gJ⁻¹ ∈ Max3.M,
      (⟨gJ * (m : J) * gJ⁻¹, hmem⟩ : Max3.M) ∈ CM := by
  have hm' : m ∈ Subgroup.centralizer ({q0M} : Set Max3.M) := by simpa [CM] using hm
  have hmq : (m : J) * Max3.q 0 = Max3.q 0 * (m : J) := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hm'
    simpa [q0M] using congrArg (fun x : Max3.M => (x : J)) this
  have hma : (m : J) * Max3.z = Max3.z * (m : J) := by
    have := Subgroup.mem_center_iff.mp Max3.z_mem_center_M m
    simpa [aM] using congrArg (fun x : Max3.M => (x : J)) this
  have hgq_inv : gJ⁻¹ * Max3.z * gJ = Max3.q 0 := by
    rw [← hg2]; group
  have hga_inv : gJ⁻¹ * Max3.q 0 * gJ = Max3.z := by
    rw [← hg1]; group
  have hmemC : gJ * (m : J) * gJ⁻¹ ∈
      Subgroup.centralizer ({Max3.z} : Set J) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (gJ * (m : J) * gJ⁻¹) * Max3.z
        = gJ * (m : J) * (gJ⁻¹ * Max3.z * gJ) * gJ⁻¹ := by group
      _ = gJ * (m : J) * Max3.q 0 * gJ⁻¹ := by rw [hgq_inv]
      _ = gJ * ((m : J) * Max3.q 0) * gJ⁻¹ := by group
      _ = gJ * (Max3.q 0 * (m : J)) * gJ⁻¹ := by rw [hmq]
      _ = (gJ * Max3.q 0 * gJ⁻¹) * (gJ * (m : J) * gJ⁻¹) := by group
      _ = Max3.z * (gJ * (m : J) * gJ⁻¹) := by rw [hg2]
  have hmem : gJ * (m : J) * gJ⁻¹ ∈ Max3.M := by
    rw [hCM] at hmemC
    exact hmemC
  refine ⟨hmem, ?_⟩
  change (⟨gJ * (m : J) * gJ⁻¹, hmem⟩ : Max3.M) ∈ CM
  rw [CM, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change (gJ * (m : J) * gJ⁻¹) * Max3.q 0 =
    Max3.q 0 * (gJ * (m : J) * gJ⁻¹)
  calc (gJ * (m : J) * gJ⁻¹) * Max3.q 0
      = gJ * (m : J) * (gJ⁻¹ * Max3.q 0 * gJ) * gJ⁻¹ := by group
    _ = gJ * (m : J) * Max3.z * gJ⁻¹ := by rw [hga_inv]
    _ = gJ * ((m : J) * Max3.z) * gJ⁻¹ := by group
    _ = gJ * (Max3.z * (m : J)) * gJ⁻¹ := by rw [hma]
    _ = (gJ * Max3.z * gJ⁻¹) * (gJ * (m : J) * gJ⁻¹) := by group
    _ = Max3.q 0 * (gJ * (m : J) * gJ⁻¹) := by rw [hg1]

private theorem nCM_q0_eq_nCM_a
    (hsw : ∃ g : J, g * Max3.z * g⁻¹ = Max3.q 0 ∧ g * Max3.q 0 * g⁻¹ = Max3.z)
    (hCM : Subgroup.centralizer ({Max3.z} : Set J) = Max3.M) :
    nCM q0M = nCM aM := by
  obtain ⟨gJ, hg1, hg2⟩ := hsw
  let Uq : Set Max3.M := {m | m ∈ CM ∧ m ^ 2 = q0M}
  let Ua : Set Max3.M := {m | m ∈ CM ∧ m ^ 2 = aM}
  change Uq.ncard = Ua.ncard
  have hgq_inv : gJ⁻¹ * Max3.z * gJ = Max3.q 0 := by rw [← hg2]; group
  have hga_inv : gJ⁻¹ * Max3.q 0 * gJ = Max3.z := by rw [← hg1]; group
  let F : (m : Max3.M) → m ∈ Uq → Max3.M := fun m hm =>
    let h := Classical.choose (conj_M_mem gJ hg1 hg2 hCM hm.1)
    ⟨gJ * (m : J) * gJ⁻¹, h⟩
  have hF_mem : ∀ (m : Max3.M) (hm : m ∈ Uq), F m hm ∈ Ua := by
    intro m hm
    have hmCM : m ∈ CM := hm.1
    have hm2 : m ^ 2 = q0M := hm.2
    have hCH := Classical.choose_spec (conj_M_mem gJ hg1 hg2 hCM hmCM)
    refine ⟨hCH, ?_⟩
    apply Subtype.ext
    change (gJ * (m : J) * gJ⁻¹) ^ 2 = Max3.z
    calc (gJ * (m : J) * gJ⁻¹) ^ 2
        = gJ * ((m : J) ^ 2) * gJ⁻¹ := by
          rw [pow_two, pow_two]
          group
      _ = gJ * Max3.q 0 * gJ⁻¹ := by
          rw [show (m : J) ^ 2 = ((m ^ 2 : Max3.M) : J) from by
            simpa [Subgroup.coe_pow], hm2]
      _ = Max3.z := hg2
  have hF_inj : ∀ (m n : Max3.M) (hm : m ∈ Uq) (hn : n ∈ Uq),
      F m hm = F n hn → m = n := by
    intro m n hm hn hmn
    have h : gJ * (m : J) * gJ⁻¹ = gJ * (n : J) * gJ⁻¹ := by
      simpa [F] using congrArg (fun z : Max3.M => (z : J)) hmn
    apply Subtype.ext
    calc (m : J) = gJ⁻¹ * (gJ * (m : J) * gJ⁻¹) * gJ := by group
      _ = gJ⁻¹ * (gJ * (n : J) * gJ⁻¹) * gJ := by rw [h]
      _ = (n : J) := by group
  have hF_surj : ∀ y ∈ Ua, ∃ m, ∃ hm : m ∈ Uq, F m hm = y := by
    intro y hy
    have hyCM : y ∈ CM := hy.1
    have hy2 : y ^ 2 = aM := hy.2
    let hdata := conj_M_mem (gJ := gJ⁻¹) hgq_inv hga_inv hCM hyCM
    let m : Max3.M := ⟨gJ⁻¹ * (y : J) * gJ, Classical.choose hdata⟩
    have hmCM : m ∈ CM := Classical.choose_spec hdata
    have hm2 : m ^ 2 = q0M := by
      apply Subtype.ext
      change (gJ⁻¹ * (y : J) * gJ) ^ 2 = Max3.q 0
      calc (gJ⁻¹ * (y : J) * gJ) ^ 2
          = gJ⁻¹ * ((y : J) ^ 2) * gJ := by
            rw [pow_two, pow_two]
            group
        _ = gJ⁻¹ * Max3.z * gJ := by
            rw [show (y : J) ^ 2 = ((y ^ 2 : Max3.M) : J) from by
              simpa [Subgroup.coe_pow], hy2]
        _ = Max3.q 0 := hgq_inv
    refine ⟨m, ⟨hmCM, hm2⟩, ?_⟩
    dsimp [F]
    apply Subtype.ext
    change gJ * (m : J) * gJ⁻¹ = (y : J)
    dsimp [m]
    group
  have hcard : Uq.ncard = Ua.ncard := Set.ncard_congr F hF_mem hF_inj hF_surj
  exact hcard
theorem not_twistedSquares_of (Fd : FibreData S)
    (hm₀ : ∃ m : Max3.M, (m : J) * Max3.q 0 = Max3.q 0 * (m : J) ∧
      (m : J) ^ 2 = Max3.z ∧
      (Max3.InvRep.kap m : Equiv.Perm (Fin 9)).cycleType = {2, 2})
    (hinv : ∀ n : Max3.M, n * n = 1 →
      (Max3.InvRep.kap n : Equiv.Perm (Fin 9)).cycleType ≠ {2, 2})
    (hc : ∃ c ∈ Max3.Q, c * Max3.q 0 * c⁻¹ = Max3.q 0 * Max3.z)
    (hsw : ∃ g : J, g * Max3.z * g⁻¹ = Max3.q 0 ∧ g * Max3.q 0 * g⁻¹ = Max3.z)
    (hCM : Subgroup.centralizer ({Max3.z} : Set J) = Max3.M) :
    ¬ Fd.TwistedSquares := by
  intro tw
  obtain ⟨h1, hphiJ, g, hgz, hgh⟩ := Fd.exists_swap
  have hphi : Fd.φQ h1 = q0QM := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [q0QM, q0M] using hphiJ
  have hzcount : nCH h1 S.toSetting.zM = nCMeps aM 0 :=
    nCH_z_eq_nCMeps_a0 Fd tw hinv h1 hphi
  have hh1count : nCH h1 (h1 : S.toSetting.M) =
      nCMeps q0M 0 + nCMeps (q0M * aM) 1 :=
    nCH_h1_eq Fd tw h1 hphi
  have hswap : nCH h1 (h1 : S.toSetting.M) = nCH h1 S.toSetting.zM :=
    nCH_h1_eq_nCH_z Fd hgz hgh
  have hq0a : nCMeps (q0M * aM) 1 = nCMeps q0M 1 :=
    nCMeps_q0a_eq hc
  have hq0a' : nCM q0M = nCM aM := nCM_q0_eq_nCM_a hsw hCM
  have hzplus : nCH h1 S.toSetting.zM + nCMeps aM 1 = nCM aM := by
    rw [hzcount, ← nCM_eq_add_eps aM]
  have hq : nCM aM = nCH h1 S.toSetting.zM := by
    calc nCM aM = nCM q0M := hq0a'.symm
      _ = nCMeps q0M 0 + nCMeps q0M 1 := nCM_eq_add_eps q0M
      _ = nCMeps q0M 0 + nCMeps (q0M * aM) 1 := by rw [hq0a]
      _ = nCH h1 (h1 : S.toSetting.M) := hh1count.symm
      _ = nCH h1 S.toSetting.zM := hswap
  have hX0 : nCMeps aM 1 = 0 := by omega
  obtain ⟨m, hmq, hm2J, hmcyc⟩ := hm₀
  have hmCM : m ∈ CM := by
    rw [CM, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simpa [q0M, Subgroup.coe_mul] using hmq
  have hm2 : m ^ 2 = aM := by
    apply Subtype.ext
    change ((m ^ 2 : Max3.M) : J) = Max3.z
    simpa [Subgroup.coe_pow] using hm2J
  have hme : eps (kap m) = 1 := (eps_eq_one_iff (kap m)).mpr hmcyc
  have hXpos : 0 < nCMeps aM 1 := by
    rw [nCMeps, Set.ncard_pos]
    exact ⟨m, ⟨hmCM, hm2, hme⟩⟩
  omega

theorem exists_mulEquiv_of (Fd : FibreData S)
    (hm₀ : ∃ m : Max3.M, (m : J) * Max3.q 0 = Max3.q 0 * (m : J) ∧
      (m : J) ^ 2 = Max3.z ∧
      (Max3.InvRep.kap m : Equiv.Perm (Fin 9)).cycleType = {2, 2})
    (hinv : ∀ n : Max3.M, n * n = 1 →
      (Max3.InvRep.kap n : Equiv.Perm (Fin 9)).cycleType ≠ {2, 2})
    (hc : ∃ c ∈ Max3.Q, c * Max3.q 0 * c⁻¹ = Max3.q 0 * Max3.z)
    (hsw : ∃ g : J, g * Max3.z * g⁻¹ = Max3.q 0 ∧ g * Max3.q 0 * g⁻¹ = Max3.z)
    (hCM : Subgroup.centralizer ({Max3.z} : Set J) = Max3.M) :
    ∃ e : S.toSetting.M ≃* Max3.M, ∀ h, (h, e h) ∈ Fd.F := by
  rcases Fd.split_or_twisted with h | h
  · exact h
  · exact absurd h (Fd.not_twistedSquares_of hm₀ hinv hc hsw hCM)

end FibreData

end CFSG.Sporadic.Th.Recog
