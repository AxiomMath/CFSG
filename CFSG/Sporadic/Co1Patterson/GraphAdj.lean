module

public import CFSG.Sporadic.Co1Patterson.GraphPartition
public import Certificates.Certificate21152
public import CFSG.Sporadic.Co1Patterson.GraphDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native Matrix
open CFSG.Blueprint (NativeSporadic.Co1)

theorem ronan_check1 : ronanCheck1 = true :=
  Certificates.certificate21152

theorem aeCheck_true : aeCheck = true := by
  have h := ronan_check1
  unfold ronanCheck1 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem aeCheck_parts :
    1 ≤ aeIdx ∧ aeIdx ≤ 190 ∧
    conjA (gEl aeIdx) (gElInv aeIdx) = Native.mul iotaARows (repRows 1) ∧
    qPts.contains (Native.mul (Native.mul (repXi 1) iotaARows) (repX 1)) = false := by
  have h := aeCheck_true
  unfold aeCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem comm_of_orderOf_two {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : orderOf (x * y) = 2) : x * y = y * x := by
  have h2 := pow_orderOf_eq_one (x * y)
  rw [h, sq] at h2
  have hinv : (x * y)⁻¹ = y * x := by
    rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hy, inv_eq_of_mul_eq_one_right hx]
  rw [← hinv]
  exact eq_inv_of_mul_eq_one_left h2


noncomputable abbrev vE : Vt := repV 1

theorem rep11V_two : rep11V 2 = vE := rep11V_succ 1

theorem vCode_vA : vCode vA = tableCode 0 := by
  have := vCode_rep11 (i := 0) (by norm_num)
  rwa [rep11V_zero] at this

theorem vCode_vE : vCode vE = tableCode 2 := by
  have := vCode_rep11 (i := 2) (by norm_num)
  rwa [rep11V_two] at this

theorem vE_ne_vA : vE ≠ vA := by
  intro h
  have h2 := vCode_vE
  rw [h, vCode_vA] at h2
  exact absurd h2 (by decide)

theorem aNC_mul_self : aNC * aNC = 1 := by
  have h := pow_orderOf_eq_one aNC
  rw [orderOf_aNC] at h
  rw [← sq]
  exact h

theorem vt_mul_self (v : Vt) : (v : NativeSporadic.Co1) * v = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.1 v.2
  rw [← hg]
  calc g * aNC * g⁻¹ * (g * aNC * g⁻¹) = g * (aNC * aNC) * g⁻¹ := by group
    _ = 1 := by rw [aNC_mul_self, mul_one, mul_inv_cancel]

theorem ncard_fix_aNC :
    {w : Fin 24 → ZMod 2 | matHom aNC *ᵥ w = w}.ncard = 2 ^ 16 := by
  rw [show matHom aNC = rowsMatrix 24 iotaARows from nrep_aNC, ncard_fix,
    twoA_misc_parts.2.2.1]
  norm_num

theorem qOf_aNC :
    qOf aNC = twoAQNC :=
  fStar_centralizer


theorem vCode_parts {v : Vt} {o : ℕ} {q q2 : Bool} {f : ℕ} (h : vCode v = (o, q, q2, f)) :
    ordA v = o ∧ (inQa v ↔ q = true) ∧ (inQa2 v ↔ q2 = true) ∧ fixA v = f := by
  classical
  rw [vCode_eq] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, ?_, ?_, h4⟩
  · rw [← h2]; exact (decide_eq_true_iff).symm
  · rw [← h3]; exact (decide_eq_true_iff).symm

theorem a2_adj_vA_vE : (a2Graph aNC).Adj vA vE := by
  have hc := vCode_vE
  rw [show tableCode 2 = (2, false, true, 2 ^ 16) by decide] at hc
  obtain ⟨ho, hq, -, -⟩ := vCode_parts hc
  have hq' : ¬ inQa vE := fun h => absurd (hq.1 h) (by decide)
  have ho' : orderOf (aNC * (vE : NativeSporadic.Co1)) = 2 := ho
  have hcomm : aNC * (vE : NativeSporadic.Co1) = vE * aNC :=
    comm_of_orderOf_two (G := NativeSporadic.Co1) aNC_mul_self (vt_mul_self vE) ho'
  obtain ⟨h1, h190, hconj, hnq⟩ := aeCheck_parts
  refine ⟨vE_ne_vA.symm, hcomm, ?_, ?_, ?_⟩
  ·
    have hx := nrep_conjA (nrep_gEl (dagOK_parts dagOK_true).1 aeIdx)
      (nrep_gElInv dagOK_true h1 h190)
    have hae' : NRep (Native.mul iotaARows (repRows 1)) (aNC * vE) :=
      nrep_aNC.mul (nrep_repV (by norm_num))
    have heq : gElt aeIdx * aNC * (gElt aeIdx)⁻¹ = aNC * vE := NRep.unique hx (hconj ▸ hae')
    show IsConj aNC (aNC * vE)
    rw [← heq]
    exact isConj_iff.2 ⟨gElt aeIdx, rfl⟩
  · show (vE : NativeSporadic.Co1) ∉ qOf aNC
    rw [qOf_aNC]
    exact hq'
  ·
    show aNC ∉ qOf (gElt (repJ 1) * aNC * (gElt (repJ 1))⁻¹)
    rw [mem_qOf_conj, qOf_aNC]
    have hr : NRep (Native.mul (Native.mul (repXi 1) iotaARows) (repX 1))
        ((gElt (repJ 1))⁻¹ * aNC * gElt (repJ 1)) :=
      ((nrep_repXi dagOK_true (by norm_num)).mul nrep_aNC).mul (nrep_repX dagOK_true 1)
    have hv' : CFSG.Sporadic.Co1.InvNative.validRows
        (Native.mul (Native.mul (repXi 1) iotaARows) (repX 1)) = true := by
      have := dagOK_parts dagOK_true
      exact validRows_mul (validRows_mul (this.2 _ (repJ_mem (by norm_num)).1
        (repJ_mem (by norm_num)).2).2.1 twoA_misc_parts.2.2.2.2.2.1)
        (this.2 _ (repJ_mem (by norm_num)).1 (repJ_mem (by norm_num)).2).1
    rw [mem_twoAQNC_iff_contains hr hv', hnq]
    decide

theorem tableCode_eq_two : ∀ i < 11, (tableCode i).1 = 2 → (tableCode i).2.1 = false →
    (tableCode i).2.2.2 = 2 ^ 16 → i = 2 := by
  decide

open Classical in
theorem a2_adj_vA_iff (v : Vt) : (a2Graph aNC).Adj vA v ↔ v ∈ cOrb vE := by
  constructor
  · rintro ⟨hne, hcomm0, hconj0, hq, -⟩
    have hcomm : aNC * (v : NativeSporadic.Co1) = v * aNC := hcomm0
    have hconj : IsConj aNC (aNC * (v : NativeSporadic.Co1)) := hconj0
    obtain ⟨i, hi, hv⟩ := suborbits_cover v
    have hcode := (vCode_eq_of_mem hv).trans (vCode_rep11 hi)
    have hav : (aNC * (v : NativeSporadic.Co1)) ^ 2 = 1 := by
      rw [sq]
      calc aNC * (v : NativeSporadic.Co1) * (aNC * v) = aNC * (v * aNC) * v := by group
        _ = aNC * (aNC * v) * v := by rw [← hcomm]
        _ = (aNC * aNC) * (v * v) := by group
        _ = 1 := by rw [aNC_mul_self, vt_mul_self, mul_one]
    have hav1 : aNC * (v : NativeSporadic.Co1) ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      show aNC = v
      have := congrArg (aNC * ·) h1
      rw [← mul_assoc, aNC_mul_self, one_mul, mul_one] at this
      exact this.symm
    have hord : ordA v = 2 := orderOf_eq_prime (G := NativeSporadic.Co1) hav hav1
    have hinq : ¬ inQa v := by
      intro h
      apply hq
      show (v : NativeSporadic.Co1) ∈ qOf aNC
      rw [qOf_aNC]
      exact h
    have hfix : fixA v = 2 ^ 16 := by
      obtain ⟨g, hg⟩ := isConj_iff.1 hconj
      unfold fixA
      rw [← hg, ncard_fix_conj, ncard_fix_aNC]
    rw [vCode_eq] at hcode
    have h1 : (tableCode i).1 = 2 := by rw [← hcode, hord]
    have h2 : (tableCode i).2.1 = false := by
      rw [← hcode]
      exact decide_eq_false hinq
    have h3 : (tableCode i).2.2.2 = 2 ^ 16 := by rw [← hcode, hfix]
    have := tableCode_eq_two i hi h1 h2 h3
    subst this
    rwa [rep11V_two] at hv
  · rintro ⟨k, hk, rfl⟩
    have := a2Graph_adj_smul k a2_adj_vA_vE
    rwa [(smul_vA_eq_iff k).2 hk] at this

theorem a2_adj_iff (u v : Vt) : (a2Graph aNC).Adj u v ↔ orbRel vE u v := by
  obtain ⟨x, hx⟩ := isConj_iff.1 u.2
  have hu : u = x • vA := Subtype.ext hx.symm
  subst hu
  rw [orbRel_smul_iff_mem, ← a2_adj_vA_iff, ← a2Graph_adj_smul_iff x⁻¹, inv_smul_smul]

theorem a2_adj_smul_iff (x : NativeSporadic.Co1) (v : Vt) :
    (a2Graph aNC).Adj (x • vA) v ↔ x⁻¹ • v ∈ cOrb vE := by
  rw [a2_adj_iff, orbRel_smul_iff_mem]

theorem adj_iff_contains {X Xi V : Native.Rows} {x : NativeSporadic.Co1} {v : Vt}
    (hX : NRep X x) (hXi : NRep Xi x⁻¹) (hV : NRep V v)
    (hval : CFSG.Sporadic.Co1.InvNative.validRows (Native.mul (Native.mul Xi V) X) = true) :
    (a2Graph aNC).Adj (x • vA) v ↔
      (ptSet orbE).contains (Native.mul (Native.mul Xi V) X) = true := by
  have hr : NRep (Native.mul (Native.mul Xi V) X) ((x⁻¹ • v : Vt) : NativeSporadic.Co1) := by
    rw [coe_smul_conjVert, inv_inv]
    exact (hXi.mul hV).mul hX
  rw [a2_adj_smul_iff, mem_cOrb_iff_of_exactOK exact_orbE vE nrep_eRows, ptSet_contains_iff]
  have hok : orbOK brayArr brayInvArr eRows orbE = true := by
    have := exact_orbE
    unfold exactOK at this
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  constructor
  · rintro ⟨i, hi, hpi⟩
    exact ⟨i, hi, NRep.rows_eq hpi hr ((orbOK_parts hok).2.2.2.2.2.2.2.1 i hi).1 hval⟩
  · rintro ⟨i, hi, hpi⟩
    exact ⟨i, hi, hpi ▸ hr⟩

end CFSG.Sporadic.Co1Patterson
