
module

public import CFSG.Monster.B.TwoA.Amalgam.Data

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open scoped Pointwise

theorem not_mem_N1_inv {a : Dfull} (hn : a ∉ N1) : a⁻¹ ∉ N1 := fun h => hn (by
  simpa using N1.inv_mem h)

theorem mem_N1_of_comm {a : Dfull} (ha : a ∈ Ehat) (h : a * cQ = cQ * a) : a ∈ N1 :=
  ⟨ha, Subgroup.mem_centralizer_singleton_iff.2 h⟩

theorem conj_cQ_of_not_mem
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    a⁻¹ * cQ * a = cQ * xhat := by
  have hn' := not_mem_N1_inv hn
  have hc := Ehat_commutator (Ehat.inv_mem ha) cQ_mem_Ehat
  rw [inv_inv] at hc
  rcases zmod2_cases (bV (psiW ⟨a⁻¹, Ehat.inv_mem ha⟩) (psiW ⟨cQ, cQ_mem_Ehat⟩)) with h | h
  · rw [h] at hc
    change a⁻¹ * cQ * a * cQ⁻¹ = xhat ^ 0 at hc
    rw [pow_zero, mul_inv_eq_one] at hc
    exact absurd (mem_N1_of_comm (Ehat.inv_mem ha) (eq_mul_inv_of_mul_eq hc)) hn'
  · rw [h] at hc
    change a⁻¹ * cQ * a * cQ⁻¹ = xhat ^ 1 at hc
    rw [pow_one, mul_inv_eq_iff_eq_mul] at hc
    rw [hc]
    exact (xhat_comm_of_mem_Jhat (Ehat_le_Jhat cQ_mem_Ehat)).symm

theorem conj_cQ_of_not_mem'
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    a * cQ * a⁻¹ = cQ * xhat := by
  have h := conj_cQ_of_not_mem (Ehat.inv_mem ha) (not_mem_N1_inv hn)
  rwa [inv_inv] at h

theorem mul_self_mem_zpowers_xhat {a : Dfull} (ha : a ∈ Ehat) : a * a ∈ Subgroup.zpowers xhat := by
  have h : psiW (⟨a, ha⟩ * ⟨a, ha⟩) = 0 := by
    rw [psiW_mul, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rcases (psiW_eq_zero_iff _).1 h with h1 | h1
  · rw [show a * a = 1 from congrArg Subtype.val h1]
    exact Subgroup.one_mem _
  · rw [show a * a = xhat from congrArg Subtype.val h1]
    exact Subgroup.mem_zpowers _

theorem zpowers_xhat_le_P1 :
    Subgroup.zpowers xhat ≤ P1 := by
  rw [Subgroup.zpowers_le]
  exact ⟨Ehat_le_Jhat (Vhat_le_Ehat xhat_mem_Vhat), Subgroup.mem_centralizer_singleton_iff.2
    (xhat_comm_of_mem_Jhat (Ehat_le_Jhat cQ_mem_Ehat)).symm⟩

theorem conj_mem_P1
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) {p : Dfull} (hp : p ∈ P1) :
    a⁻¹ * p * a ∈ P1 := by
  have haJ := Ehat_le_Jhat ha
  refine ⟨Jhat.mul_mem (Jhat.mul_mem (Jhat.inv_mem haJ) hp.1) haJ,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hpc : p * cQ = cQ * p := Subgroup.mem_centralizer_singleton_iff.1 hp.2
  have hpx : p * xhat = xhat * p := xhat_comm_of_mem_Jhat hp.1
  have hp' : p * (cQ * xhat) = cQ * xhat * p := by
    rw [← mul_assoc, hpc, mul_assoc, hpx, ← mul_assoc]
  have hac := conj_cQ_of_not_mem' ha hn
  calc a⁻¹ * p * a * cQ = a⁻¹ * (p * (a * cQ * a⁻¹)) * a := by group
    _ = a⁻¹ * (cQ * xhat * p) * a := by rw [hac, hp']
    _ = a⁻¹ * (a * cQ * a⁻¹) * p * a := by rw [hac]; group
    _ = cQ * (a⁻¹ * p * a) := by group

theorem map_conj_P1 {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    P1.map (MulAut.conj a⁻¹).toMonoidHom = P1 := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    show a⁻¹ * p * a⁻¹⁻¹ ∈ P1
    rw [inv_inv]
    exact conj_mem_P1 ha hn hp
  · intro p hp
    refine ⟨a * p * a⁻¹, ?_, ?_⟩
    · have h := conj_mem_P1 (Ehat.inv_mem ha) (not_mem_N1_inv hn) hp
      rwa [inv_inv] at h
    · show a⁻¹ * (a * p * a⁻¹) * a⁻¹⁻¹ = p
      group

theorem mem_conj_iff {a y : Dfull} {H : Subgroup Dfull} :
    y ∈ H.map (MulAut.conj a⁻¹).toMonoidHom ↔ a * y * a⁻¹ ∈ H := by
  constructor
  · rintro ⟨e, he, rfl⟩
    show a * (a⁻¹ * e * a⁻¹⁻¹) * a⁻¹ ∈ H
    rwa [show a * (a⁻¹ * e * a⁻¹⁻¹) * a⁻¹ = e by group]
  · intro h
    exact ⟨a * y * a⁻¹, h, by show a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y; group⟩

theorem tauhat_mem_P2 :
    tauhat ∈ Pc 1 :=
  ⟨tauhat_mem_Ntwo, Subgroup.mem_centralizer_singleton_iff.2 (tauhat_mul_dhat 0 2)⟩

theorem doubleCoset_eq
    {a a' : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) (ha' : a' ∈ Ehat)
    (hn' : a' ∉ N1) :
    DoubleCoset.doubleCoset a' (Eam : Set Dfull) Eam = DoubleCoset.doubleCoset a Eam Eam := by
  apply DoubleCoset.doubleCoset_eq_of_mem
  have hm : a⁻¹ * a' ∈ N1 := by
    refine ⟨Ehat.mul_mem (Ehat.inv_mem ha) ha', Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc a⁻¹ * a' * cQ = a⁻¹ * (a' * cQ * a'⁻¹) * a' := by group
      _ = a⁻¹ * (a * cQ * a⁻¹) * a' := by
          rw [conj_cQ_of_not_mem' ha' hn', conj_cQ_of_not_mem' ha hn]
      _ = cQ * (a⁻¹ * a') := by group
  exact DoubleCoset.mem_doubleCoset.2 ⟨1, Eam.one_mem, a⁻¹ * a', Pc_le_Eam 0 (N1_le_P1 hm),
    by group⟩

theorem doubleCoset_inv
    {a : Dfull} (ha : a ∈ Ehat) :
    (DoubleCoset.doubleCoset a (Eam : Set Dfull) Eam)⁻¹ = DoubleCoset.doubleCoset a Eam Eam := by
  have ha2 : (a * a)⁻¹ ∈ Eam :=
    Eam.inv_mem (Pc_le_Eam 0 (zpowers_xhat_le_P1 (mul_self_mem_zpowers_xhat ha)))
  have hmem : a⁻¹ ∈ DoubleCoset.doubleCoset a (Eam : Set Dfull) Eam :=
    DoubleCoset.mem_doubleCoset.2 ⟨1, Eam.one_mem, (a * a)⁻¹, ha2, by group⟩
  have hinv : (DoubleCoset.doubleCoset a (Eam : Set Dfull) Eam)⁻¹ =
      DoubleCoset.doubleCoset a⁻¹ Eam Eam := by
    ext y
    rw [Set.mem_inv, DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨z⁻¹, Eam.inv_mem hz, x⁻¹, Eam.inv_mem hx, ?_⟩
      rw [← inv_inv y, e]
      group
    · rintro ⟨x, hx, z, hz, rfl⟩
      exact ⟨z⁻¹, Eam.inv_mem hz, x⁻¹, Eam.inv_mem hx, by group⟩
  rw [hinv, DoubleCoset.doubleCoset_eq_of_mem hmem]

end CFSG.Monster.B.TwoA.Amalgam
