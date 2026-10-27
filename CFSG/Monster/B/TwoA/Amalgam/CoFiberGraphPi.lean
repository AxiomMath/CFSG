
module

public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphPiBase

public import CFSG.Monster.B.TwoA.Amalgam.CoFiber
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocal
public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0 wAct_mul wAct_one wAct_inv_apply wAct_apply_inv)

theorem Eam_inf_Jhat :
    Eam ⊓ Jhat = P1 :=
  le_antisymm Eam_inf_Jhat_le fun _ hx => ⟨Pc_le_Eam 0 hx, P1_le_Jhat hx⟩

theorem cvOf_jhatS_eq_iff
    {k k' : Jhat} :
    cvOf (jhatS k) = cvOf (jhatS k') ↔ ((k' * k⁻¹ : Jhat) : Dfull) ∈ P1 := by
  rw [cvOf_eq_iff, ← Eam_inf_Jhat]
  exact ⟨fun h => ⟨h, (k' * k⁻¹).2⟩, fun h => h.1⟩

theorem labE_eq_iff
    {k k' : Jhat} : labE k = labE k' ↔ cvOf (jhatS k) = cvOf (jhatS k') := by
  rw [cvOf_jhatS_eq_iff]
  constructor
  · intro h
    have h' : (k : Dfull)⁻¹ * cQ * k = (k' : Dfull)⁻¹ * cQ * k' := congrArg Subtype.val h
    refine ⟨(k' * k⁻¹).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (k' : Dfull) * (k : Dfull)⁻¹ * cQ
        = k' * ((k : Dfull)⁻¹ * cQ * k) * (k : Dfull)⁻¹ := by group
      _ = k' * ((k' : Dfull)⁻¹ * cQ * k') * (k : Dfull)⁻¹ := by rw [h']
      _ = cQ * (k' * (k : Dfull)⁻¹) := by group
  · intro h
    apply Subtype.ext
    have hc : (k' : Dfull) * (k : Dfull)⁻¹ * cQ = cQ * (k' * (k : Dfull)⁻¹) := by
      have := Subgroup.mem_centralizer_singleton_iff.1 h.2
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    show (k : Dfull)⁻¹ * cQ * k = (k' : Dfull)⁻¹ * cQ * k'
    calc (k : Dfull)⁻¹ * cQ * k
        = (k' : Dfull)⁻¹ * ((k' * (k : Dfull)⁻¹) * cQ) * k := by group
      _ = (k' : Dfull)⁻¹ * (cQ * (k' * (k : Dfull)⁻¹)) * k := by rw [hc]
      _ = (k' : Dfull)⁻¹ * cQ * k' := by group

@[expose] def a0J :
    Jhat := ⟨a0, Ehat_le_Jhat a0_mem_Ehat⟩

theorem cvOf_jhatS_a0J :
    cvOf (jhatS a0J) = cvOf a0S := rfl

theorem labE_a0J_mul
    (k : Jhat) : (labE (a0J * k) : Dfull) = labE k * xhat := by
  have h1 := conj_cQ_of_not_mem a0_mem_Ehat a0_not_mem_N1
  have h2 := xhat_comm_of_mem_Jhat k.2
  show ((a0J * k : Jhat) : Dfull)⁻¹ * cQ * (a0J * k : Jhat) = (k : Dfull)⁻¹ * cQ * k * xhat
  rw [Subgroup.coe_mul]
  calc ((a0J : Dfull) * k)⁻¹ * cQ * (a0J * k) = (k : Dfull)⁻¹ * (a0⁻¹ * cQ * a0) * k := by
        rw [show (a0J : Dfull) = a0 from rfl]
        group
    _ = (k : Dfull)⁻¹ * (cQ * xhat) * k := by rw [h1]
    _ = (k : Dfull)⁻¹ * cQ * (xhat * k) := by group
    _ = (k : Dfull)⁻¹ * cQ * (k * xhat) := by rw [h2]
    _ = (k : Dfull)⁻¹ * cQ * k * xhat := by group

theorem labE_a0J_mul'
    (k : Jhat) : labE (a0J * k) = labE k * xhatE :=
  Subtype.ext (labE_a0J_mul k)

theorem cvOf_jhatS_ne_a0J
    (k : Jhat) : cvOf (jhatS k) ≠ cvOf (jhatS (a0J * k)) := by
  intro h
  have h1 := congrArg Subtype.val (labE_eq_iff.2 h)
  rw [labE_a0J_mul] at h1
  exact xhat_ne_one (mul_eq_left.1 h1.symm)

theorem piPt_eq_iff
    {k k' : Jhat} : piPt k = piPt k' ↔
    cvOf (jhatS k') = cvOf (jhatS k) ∨ cvOf (jhatS k') = cvOf (jhatS (a0J * k)) := by
  constructor
  · intro h
    have h1 : psiW (labE k') = psiW (labE k) := by
      rw [← piPt_eq_psiW, ← piPt_eq_psiW, h]
    rcases fiber_cases h1 with h2 | h2
    · exact Or.inl (labE_eq_iff.1 (Subtype.ext h2))
    · refine Or.inr (labE_eq_iff.1 (Subtype.ext ?_))
      rw [h2, labE_a0J_mul]
  · rintro (h | h)
    · exact (piPt_eq_of h).symm
    · rw [piPt_eq_of h]
      apply Subtype.ext
      rw [piPt_eq_psiW, piPt_eq_psiW, labE_a0J_mul', psiW_mul, psiW_xhatE, add_zero]

theorem exists_swap
    {k : Jhat} (hk : (piPt k : Wv v0) ≠ Unitary.sigmaW) :
    ∃ n : Jhat, (n : Dfull) ∈ N1 ∧ cvOf (jhatS (k * n)) = cvOf (jhatS (a0J * k)) := by
  have hxσ : psiW (labE k) ≠ Unitary.sigmaW := by
    rw [← piPt_eq_psiW]
    exact hk
  have hx0 : psiW (labE k) ≠ 0 := by
    rw [← piPt_eq_psiW, coe_piPt]
    intro h
    apply Unitary.sigmaW_ne_zero
    have h2 := congrArg (wAct v0 (jhatToKv0 k)⁻¹) h
    rwa [wAct_inv_apply, map_zero] at h2
  obtain ⟨w, hw0, hw1⟩ := exists_bilin_eq_zero_eq_one (B := bV)
    (fun z hz => bV_nondegenerate.1 z hz) hx0 hxσ
  obtain ⟨n, rfl⟩ := psiW_surjective w
  have hcn := conj_Ehat cE n
  rw [psiW_cE, hw0, ZMod.val_zero, pow_zero, mul_one] at hcn
  have hcn' : (n : Dfull)⁻¹ * cQ * n = cQ := hcn
  have hnc : (n : Dfull) * cQ = cQ * n := by
    calc (n : Dfull) * cQ = n * ((n : Dfull)⁻¹ * cQ * n) := by rw [hcn']
      _ = cQ * n := by group
  have hnN : (n : Dfull) ∈ N1 := ⟨n.2, Subgroup.mem_centralizer_singleton_iff.2 hnc⟩
  refine ⟨⟨n, Ehat_le_Jhat n.2⟩, hnN, labE_eq_iff.1 (Subtype.ext ?_)⟩
  have hrn := conj_Ehat (labE k) n
  rw [hw1, ZMod.val_one, pow_one] at hrn
  rw [labE_a0J_mul, ← hrn]
  show ((k * ⟨n, Ehat_le_Jhat n.2⟩ : Jhat) : Dfull)⁻¹ * cQ * ((k * ⟨n, Ehat_le_Jhat n.2⟩ : Jhat) :
    Dfull) = (n : Dfull)⁻¹ * ((k : Dfull)⁻¹ * cQ * k) * n
  rw [Subgroup.coe_mul]
  show ((k : Dfull) * n)⁻¹ * cQ * (k * n) = (n : Dfull)⁻¹ * ((k : Dfull)⁻¹ * cQ * k) * n
  group

theorem p1Orb_eq
    {k : Jhat} (hk : (piPt k : Wv v0) ≠ Unitary.sigmaW) :
    p1Orb (cvOf (jhatS k)) = {w | ∃ k' : Jhat, w = cvOf (jhatS k') ∧
      (piPt k' : Wv v0) ∈ Unitary.usigOrbit (piPt k)} := by
  ext w
  simp only [p1Orb, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨k * p1J hp, rfl, jhatToKv0 (p1J hp), jhatToKv0_mem_Usig hp, ?_⟩
    rw [coe_piPt_mul]
  · rintro ⟨k', rfl, u, hu, hku⟩
    obtain ⟨p, hp, rfl⟩ := exists_P1_of_mem_Usig hu
    have hpk : piPt (k * p) = piPt k' := Subtype.ext (by rw [coe_piPt_mul, hku])
    have hne : (piPt (k * p) : Wv v0) ≠ Unitary.sigmaW := by
      rw [coe_piPt_mul]
      intro h
      apply hk
      have h2 := congrArg (wAct v0 (jhatToKv0 p)⁻¹) h
      rw [wAct_inv_apply] at h2
      rw [h2]
      have h3 := Unitary.mem_Usig.1 (jhatToKv0_mem_Usig hp)
      conv_lhs => rw [← h3]
      exact wAct_inv_apply _ _
    rcases piPt_eq_iff.1 hpk with h | h
    · exact ⟨jhatS p, hp, by rw [h]; rfl⟩
    · obtain ⟨n, hn, hn'⟩ := exists_swap hne
      refine ⟨jhatS (p * n), P1.mul_mem hp (N1_le_P1 hn), ?_⟩
      rw [h, ← hn', cvMul_jhatS, mul_assoc]

end CFSG.Monster.B.TwoA.Amalgam
