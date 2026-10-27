module

public import CFSG.Monster.B.GSide.EdgeHom

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam

@[expose] def edgeXhat :
    cEdgeStab := cEdgeIncl (lamV0 * lamW0)

theorem coe_edgeXhat :
    (((edgeXhat : cEdgeStab) : Shat) : Dfull) = xhat := by
  show ((lamV0 : Shat) : Dfull) * ((lamW0 : Shat) : Dfull) = xhat
  rw [coe_lamV0, coe_lamW0, ← mul_assoc, cQ_mul_self, one_mul]

theorem conj_xhat_of_mem_cEdgeStab
    {s : Shat} (hs : s ∈ cEdgeStab) :
    ((s : Dfull))⁻¹ * xhat * s = xhat := by
  have hx : xhat = cQ⁻¹ * (cQ * xhat) := by group
  rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 hs with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have e0 := clabel_cvMul cv0 s
    have e1 := clabel_cvMul cw0 s
    rw [h0, clabel_cv0] at e0
    rw [h1, clabel_cw0] at e1
    calc ((s : Dfull))⁻¹ * xhat * s
        = (((s : Dfull))⁻¹ * cQ * s)⁻¹ * (((s : Dfull))⁻¹ * (cQ * xhat) * s) := by group
      _ = xhat := by rw [← e0, ← e1]; group
  · have e0 := clabel_cvMul cv0 s
    have e1 := clabel_cvMul cw0 s
    rw [h0, clabel_cv0, clabel_cw0] at e0
    rw [h1, clabel_cw0, clabel_cv0] at e1
    calc ((s : Dfull))⁻¹ * xhat * s
        = (((s : Dfull))⁻¹ * cQ * s)⁻¹ * (((s : Dfull))⁻¹ * (cQ * xhat) * s) := by group
      _ = xhat⁻¹ := by rw [← e0, ← e1]; group
      _ = xhat := inv_eq_of_mul_eq_one_right xhat_mul_self

theorem mem_Jhat_of_mem_cEdgeStab
    {s : Shat} (hs : s ∈ cEdgeStab) : (s : Dfull) ∈ Jhat := by
  rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
  have h := conj_xhat_of_mem_cEdgeStab hs
  calc (s : Dfull) * xhat = s * (((s : Dfull))⁻¹ * xhat * s) := by rw [h]
    _ = xhat * s := by group

theorem mul_mem_N1_of_not_mem
    {a b : Dfull} (ha : a ∈ Ehat) (hb : b ∈ Ehat) (han : a ∉ N1)
    (hbn : b ∉ N1) : a * b ∈ N1 := by
  refine mem_N1_of_comm (Ehat.mul_mem ha hb) ?_
  have hca : a * cQ = cQ * xhat * a := by
    rw [← conj_cQ_of_not_mem' ha han]
    group
  have hcb : b * cQ = cQ * xhat * b := by
    rw [← conj_cQ_of_not_mem' hb hbn]
    group
  have hxa : a * xhat = xhat * a := xhat_comm_of_mem_Jhat (Ehat_le_Jhat ha)
  calc a * b * cQ = a * (cQ * xhat * b) := by rw [mul_assoc, hcb]
    _ = a * cQ * xhat * b := by group
    _ = cQ * xhat * (a * xhat) * b := by rw [hca]; group
    _ = cQ * (xhat * xhat) * (a * b) := by rw [hxa]; group
    _ = cQ * (a * b) := by rw [xhat_mul_self, mul_one]

theorem mul_not_mem_N1 {a b : Dfull} (ha : a ∈ N1) (hbn : b ∉ N1) : a * b ∉ N1 := fun h =>
  hbn (by simpa using N1.mul_mem (N1.inv_mem ha) h)

theorem cw0_eq_cvOf :
    cw0 = cvOf (elS a0_mem_Ehat) := by
  rw [cw0, nbr_mk, toS_one, mul_one]

theorem mem_cEdgeStab_of_mem_Ehat
    {e : Dfull} (he : e ∈ Ehat) : elS he ∈ cEdgeStab := by
  rw [mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne, cw0_eq_cvOf, cv0, cvMul_cvOf, cvMul_cvOf,
    one_mul]
  have ha0 : Amalgam.a0 ∈ Ehat := a0_mem_Ehat
  have hn0 : Amalgam.a0 ∉ N1 := a0_not_mem_N1
  by_cases hn : e ∈ N1
  · left
    refine ⟨(cvOf_eq_cv0_iff _).2 (Pc_le_Eam 0 (N1_le_P1 hn)), ?_⟩
    rw [cvOf_eq_iff]
    show Amalgam.a0 * (Amalgam.a0 * e)⁻¹ ∈ Eam
    rw [mul_inv_rev, ← mul_assoc]
    refine Pc_le_Eam 0 (N1_le_P1 (mul_mem_N1_of_not_mem (Ehat.mul_mem ha0 (Ehat.inv_mem he))
      (Ehat.inv_mem ha0) ?_ (not_mem_N1_inv hn0)))
    intro h
    exact hn0 (by simpa using N1.mul_mem h (N1.inv_mem (N1.inv_mem hn)))
  · right
    refine ⟨?_, (cvOf_eq_cv0_iff _).2
      (Pc_le_Eam 0 (N1_le_P1 (mul_mem_N1_of_not_mem ha0 he hn0 hn)))⟩
    rw [cvOf_eq_iff]
    show Amalgam.a0 * e⁻¹ ∈ Eam
    exact Pc_le_Eam 0 (N1_le_P1 (mul_mem_N1_of_not_mem ha0 (Ehat.inv_mem he) hn0
      (not_mem_N1_inv hn)))

@[expose] def edgeQ :
    Subgroup cEdgeStab :=
  (Ehat.comap Shat.subtype).comap cEdgeStab.subtype

theorem mem_edgeQ
    {b : cEdgeStab} : b ∈ edgeQ ↔ ((b : Shat) : Dfull) ∈ Ehat := Iff.rfl

@[expose] def edgeQOf
    {e : Dfull} (he : e ∈ Ehat) : cEdgeStab :=
  ⟨elS he, mem_cEdgeStab_of_mem_Ehat he⟩

theorem coe_edgeQOf
    {e : Dfull} (he : e ∈ Ehat) : (((edgeQOf he : cEdgeStab) : Shat) : Dfull) = e :=
  rfl

theorem edgeQOf_mem
    {e : Dfull} (he : e ∈ Ehat) : edgeQOf he ∈ edgeQ := he

@[expose] def edgeQEquiv :
    edgeQ ≃ Ehat where
  toFun b := ⟨((b : cEdgeStab) : Shat), b.2⟩
  invFun e := ⟨edgeQOf e.2, edgeQOf_mem e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard_edgeQ :
    Nat.card edgeQ = 2 ^ 23 := by
  rw [Nat.card_congr edgeQEquiv, natCard_Ehat]

theorem edgeQ_normal :
    edgeQ.Normal where
  conj_mem q hq b := by
    rw [mem_edgeQ] at hq ⊢
    have hbJ := mem_Jhat_of_mem_cEdgeStab b.2
    have h := conj_mem_Ehat (Jhat.inv_mem hbJ) hq
    rw [inv_inv] at h
    exact h

theorem lamV0_mem_edgeQ :
    cEdgeIncl lamV0 ∈ edgeQ := by
  rw [mem_edgeQ]
  show ((lamV0 : Shat) : Dfull) ∈ Ehat
  rw [coe_lamV0]
  exact cQ_mem_Ehat

theorem edgeXhat_mem_edgeQ :
    edgeXhat ∈ edgeQ := by
  rw [mem_edgeQ, coe_edgeXhat]
  exact xhat_mem_Ehat

theorem edgeXhat_comm
    (b : cEdgeStab) : b * edgeXhat = edgeXhat * b := by
  apply Subtype.ext
  apply Subtype.ext
  show ((b : Shat) : Dfull) * (((edgeXhat : cEdgeStab) : Shat) : Dfull) =
    (((edgeXhat : cEdgeStab) : Shat) : Dfull) * ((b : Shat) : Dfull)
  rw [coe_edgeXhat]
  exact (xhat_comm_of_mem_Jhat (mem_Jhat_of_mem_cEdgeStab b.2))

theorem edgeQ_comm_iff
    {q : cEdgeStab} (hq : q ∈ edgeQ) :
    (∀ q' ∈ edgeQ, q * q' = q' * q) ↔ q = 1 ∨ q = edgeXhat := by
  constructor
  · intro h
    have hz : (⟨_, hq⟩ : Ehat) ∈ Subgroup.center Ehat := by
      rw [Subgroup.mem_center_iff]
      intro e
      apply Subtype.ext
      have h1 := congrArg (fun b : cEdgeStab => ((b : Shat) : Dfull)) (h _ (edgeQOf_mem e.2))
      exact h1.symm
    have hz' : ((q : Shat) : Dfull) ∈ Subgroup.zpowers xhat := by
      rw [← CFSG.Monster.B.TwoA.center_Ehat]
      exact ⟨_, hz, rfl⟩
    rcases (Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xhat).1 hz' with h1 | h1
    · left
      exact Subtype.ext (Subtype.ext h1)
    · right
      exact Subtype.ext (Subtype.ext (h1.trans coe_edgeXhat.symm))
  · rintro (rfl | rfl) q' _
    · rw [one_mul, mul_one]
    · exact (edgeXhat_comm q').symm

theorem edgeQ_hQ1
    (h : vStab cv0)
    (hc : ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → h * cEdgeFixToH a = cEdgeFixToH a * h) :
    h * h = 1 := by
  have hN : ∀ n ∈ N1, ((h : Shat) : Dfull) * n = n * ((h : Shat) : Dfull) := by
    intro n hn
    have hnS : n ∈ Shat := Ehat_le_Shat (N1_le_Ehat hn)
    have hnA : (⟨n, hnS⟩ : Shat) ∈ cEdgeFix := mem_cEdgeFix_iff.2 (N1_le_P1 hn)
    have h1 := hc ⟨⟨n, hnS⟩, hnA⟩ (show n ∈ Ehat from N1_le_Ehat hn)
    exact congrArg (fun z : vStab cv0 => ((z : Shat) : Dfull)) h1
  have hyE : ((h : Shat) : Dfull) ∈ Eam := mem_vStab_cv0.1 h.2
  have hyJ : ((h : Shat) : Dfull) ∈ Jhat := by
    rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
    exact hN xhat xhat_mem_N1
  have hyP : ((h : Shat) : Dfull) ∈ P1 := Subgroup.mem_inf.2 ⟨hyJ, Eam_le_centralizer hyE⟩
  have hcl := mem_closure_of_centralizer_N1 hyP hN
  have hsq : ∀ d : Dfull, (d = 1 ∨ d = cQ ∨ d = cQ * xhat ∨ d = xhat) → d * d = 1 := by
    rintro d (rfl | rfl | rfl | rfl)
    · rw [mul_one]
    · exact cQ_mul_self
    · have hxc : xhat * cQ = cQ * xhat :=
        (xhat_comm_of_mem_Jhat (Ehat_le_Jhat cQ_mem_Ehat)).symm
      calc cQ * xhat * (cQ * xhat) = cQ * (xhat * cQ) * xhat := by group
        _ = cQ * cQ * (xhat * xhat) := by rw [hxc]; group
        _ = 1 := by rw [cQ_mul_self, xhat_mul_self, mul_one]
    · exact xhat_mul_self
  exact Subtype.ext (Subtype.ext (hsq _ (mem_closure_xhat_cQ hcl)))

end CFSG.Monster.B.GSide
