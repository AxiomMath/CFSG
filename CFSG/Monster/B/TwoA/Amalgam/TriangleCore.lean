module

public import CFSG.Monster.B.TwoA.Amalgam.DistTwoCore
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

@[expose] def IsCTriangle
    (a b c : CVert) : Prop :=
  cgraph.Adj a b ∧ cgraph.Adj a c ∧ cgraph.Adj b c

@[expose] def pairStabOrbit
    (a b c : CVert) : Set CVert :=
  {c' | ∃ s : Shat, cvMul a s = a ∧ cvMul b s = b ∧ cvMul c s = c'}

abbrev triType
    (a b c : CVert) : ℕ := (pairStabOrbit a b c).ncard

theorem triType_swap_left
    (a b c : CVert) : triType b a c = triType a b c := by
  have e : pairStabOrbit b a c = pairStabOrbit a b c := by
    ext c'
    exact exists_congr fun s => and_left_comm
  rw [triType, e]

theorem cvMul_inv_eq_of_cvMul_eq
    {v : CVert} {s : Shat} (h : cvMul v s = v) :
    cvMul v s⁻¹ = v := by
  conv_lhs => rw [← h]
  exact cvMul_inv_cancel v s

theorem natCard_stab_eq_mul
    (a b c : CVert) :
    Nat.card {s : Shat // cvMul a s = a ∧ cvMul b s = b} = (pairStabOrbit a b c).ncard *
      Nat.card {s : Shat // cvMul a s = a ∧ cvMul b s = b ∧ cvMul c s = c} := by
  let f : {s : Shat // cvMul a s = a ∧ cvMul b s = b} → pairStabOrbit a b c :=
    fun s => ⟨cvMul c s.1, s.1, s.2.1, s.2.2, rfl⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), ← Nat.card_coe_set_eq]
  refine natCard_sigma_const fun y => ?_
  obtain ⟨_, s₀, h₀a, h₀b, rfl⟩ := y
  have ha' := cvMul_inv_eq_of_cvMul_eq h₀a
  have hb' := cvMul_inv_eq_of_cvMul_eq h₀b
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1 * s₀⁻¹, ?_, ?_, ?_⟩
      invFun := fun t => ⟨⟨t.1 * s₀, ?_, ?_⟩, ?_⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (inv_mul_cancel_right _ _))
      right_inv := fun t => Subtype.ext (mul_inv_cancel_right _ _) }
  · rw [cvMul_mul, x.1.2.1, ha']
  · rw [cvMul_mul, x.1.2.2, hb']
  · have hx : cvMul c x.1.1 = cvMul c s₀ := congrArg Subtype.val x.2
    rw [cvMul_mul, hx, cvMul_inv_cancel]
  · rw [cvMul_mul, t.2.1, h₀a]
  · rw [cvMul_mul, t.2.2.1, h₀b]
  · exact Subtype.ext (by
      show cvMul c (t.1 * s₀) = cvMul c s₀
      rw [cvMul_mul, t.2.2.2])

theorem natCard_stab_cvMul
    (a b : CVert) (s : Shat) :
    Nat.card {t : Shat // cvMul (cvMul a s) t = cvMul a s ∧ cvMul (cvMul b s) t = cvMul b s} =
      Nat.card {t : Shat // cvMul a t = a ∧ cvMul b t = b} := by
  refine Nat.card_congr
    { toFun := fun t => ⟨s * t.1 * s⁻¹, ?_, ?_⟩
      invFun := fun t => ⟨s⁻¹ * t.1 * s, ?_, ?_⟩
      left_inv := fun t => Subtype.ext (by dsimp only; group)
      right_inv := fun t => Subtype.ext (by dsimp only; group) }
  · rw [cvMul_mul, cvMul_mul, t.2.1, cvMul_inv_cancel]
  · rw [cvMul_mul, cvMul_mul, t.2.2, cvMul_inv_cancel]
  · rw [cvMul_mul, cvMul_mul, cvMul_inv_cancel, t.2.1]
  · rw [cvMul_mul, cvMul_mul, cvMul_inv_cancel, t.2.2]

theorem natCard_stab_three_pos
    (a b c : CVert) :
    0 < Nat.card {s : Shat // cvMul a s = a ∧ cvMul b s = b ∧ cvMul c s = c} := by
  have : Nonempty {s : Shat // cvMul a s = a ∧ cvMul b s = b ∧ cvMul c s = c} :=
    ⟨⟨1, cvMul_one a, cvMul_one b, cvMul_one c⟩⟩
  exact Nat.card_pos

theorem triType_swap_right
    {a b c : CVert} (hab : cgraph.Adj a b) (hac : cgraph.Adj a c) :
    triType a c b = triType a b c := by
  obtain ⟨s, hsa, hsb⟩ := cvMul_edge_transitive hab hac
  have h1 := natCard_stab_eq_mul a b c
  have h2 := natCard_stab_eq_mul a c b
  have h3 := natCard_stab_cvMul a b s
  rw [hsa, hsb] at h3
  have h4 : Nat.card {t : Shat // cvMul a t = a ∧ cvMul c t = c ∧ cvMul b t = b} =
      Nat.card {t : Shat // cvMul a t = a ∧ cvMul b t = b ∧ cvMul c t = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_congr_right fun _ => and_comm)
  rw [h3, h1, h4] at h2
  exact (Nat.eq_of_mul_eq_mul_right (natCard_stab_three_pos a b c) h2).symm

namespace RootModel

variable {a : CVert} (M : RootModel a)

theorem triType_eq_orbSize (b c : cgraph.neighborSet a) :
    triType a b c = orbSize (M.pt b) (M.pt c) := by
  rw [triType, ← Nat.card_coe_set_eq]
  exact M.natCard_orbit_eq_orbSize b c

include M in
theorem triType_eq_or_of_adj {b c : cgraph.neighborSet a} (hbc : cgraph.Adj b c) :
    triType a b c = 1782 ∨ triType a b c = 44352 := by
  have hne : b ≠ c := fun e => hbc.ne (congrArg Subtype.val e)
  rw [M.triType_eq_orbSize]
  exact (commute_iff_orbSize (M.pt_mem b) (M.pt_mem c)).1
    ⟨(M.adj_iff_commute hne).1 hbc, fun e => hne (M.pt_injective e)⟩

include M in
theorem exists_triangle (i : Fin 5) (hi : repSize i = 1782 ∨ repSize i = 44352) :
    ∃ b c : CVert, IsCTriangle a b c ∧ triType a b c = repSize i := by
  obtain ⟨b, hb⟩ := M.nonempty_neighborSet
  obtain ⟨q, hq, hqs⟩ := exists_orbSize_eq_repSize (M.pt_mem ⟨b, hb⟩) i
  obtain ⟨c, rfl⟩ := M.exists_pt_eq hq
  have h := (commute_iff_orbSize (M.pt_mem ⟨b, hb⟩) (M.pt_mem c)).2 (by rw [hqs]; exact hi)
  have hne : (⟨b, hb⟩ : cgraph.neighborSet a) ≠ c := fun e => h.2 (congrArg M.pt e)
  exact ⟨b, c, ⟨hb, c.2, (M.adj_iff_commute hne).2 h.1⟩,
    (M.triType_eq_orbSize ⟨b, hb⟩ c).trans hqs⟩

end RootModel

theorem triType_eq_or
    {a b c : CVert} (M : RootModel a) (h : IsCTriangle a b c) :
    triType a b c = 1782 ∨ triType a b c = 44352 :=
  M.triType_eq_or_of_adj (b := ⟨b, h.1⟩) (c := ⟨c, h.2.1⟩) h.2.2

theorem triType_perm
    {a b c : CVert} (h : IsCTriangle a b c) :
    triType a c b = triType a b c ∧ triType b a c = triType a b c ∧
      triType b c a = triType a b c ∧ triType c a b = triType a b c ∧
      triType c b a = triType a b c := by
  obtain ⟨hab, hac, hbc⟩ := h
  have e1 := triType_swap_right hab hac
  have e2 := triType_swap_left a b c
  have e3 := triType_swap_right hab.symm hbc
  have e4 := triType_swap_left a c b
  have e5 := triType_swap_right hac.symm hbc.symm
  exact ⟨e1, e2, e3.trans e2, e4.trans e1, e5.trans (e4.trans e1)⟩

end CFSG.Monster.B.TwoA.Amalgam
