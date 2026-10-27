
module

public import CFSG.Sporadic.HNOddCore.SylCBase

public import CFSG.Sporadic.HNOddCore.SylB
public import CFSG.Sporadic.HNOddCore.LCheck
public import CFSG.Sporadic.HNOddCore.WCheck
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.LCheckInputs
public meta import CFSG.Sporadic.HNOddCore.XCheck
public meta import CFSG.Sporadic.HNOddCore.PCheck
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.PCheckInputs
public meta import CFSG.Sporadic.HNOddCore.QCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.F5.Native Equiv

@[expose] def gR
    (s : ℕ) : RH := (gC4' s : RH)

theorem lift_parts :
    liftChecksT hnsData.n gTabs (pinvs hnsData.n gTabs) t4Tab InvData.parRecs = true := by
  have h := lift_cert
  unfold liftChecksO liftChecksR liftChecksS at h
  rw [← hRegs_eq, ← hStrongArr_eq, cTab_eq] at h
  exact h

theorem gTabs_size : gTabs.size = 11 := by
  simp [gTabs, genTabs, row4_parts.2.2.2.1]

theorem gTabs_get {j : ℕ} (hj : j < 9) :
    gTabs[j]! = pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.c4Words[j]! := by
  unfold gTabs genTabs
  rw [getElem!_pos _ j (by simp [row4_parts.2.2.2.1]; omega),
    Array.getElem_push_lt (by simp [row4_parts.2.2.2.1]; omega),
    Array.getElem_push_lt (by simp [row4_parts.2.2.2.1]; omega), Array.getElem_map,
    Array.getElem_extract, ← getElem!_pos InvData.c4Words (0 + j)
      (by rw [row4_parts.2.2.2.1]; omega)]
  simp

theorem gTabsA_size :
    ((InvData.c4Words.extract 0 9).map
      (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr))).size = 9 := by
  simp [row4_parts.2.2.2.1]

theorem gTabs_nine : gTabs[9]! = x4Tab := by
  unfold gTabs genTabs
  rw [getElem!_pos _ 9 (by simp [row4_parts.2.2.2.1]),
    Array.getElem_push_lt (by simp [row4_parts.2.2.2.1]),
    Array.getElem_push, dite_eq_right (by rw [gTabsA_size]; omega)]

theorem gTabs_ten : gTabs[10]! = cRec := by
  unfold gTabs genTabs
  rw [getElem!_pos _ 10 (by simp [row4_parts.2.2.2.1]), Array.getElem_push,
    dite_eq_right (by simp [row4_parts.2.2.2.1])]

theorem prep_gTabs
    {j : ℕ} (hj : j < 11) : PRep hnsData.n gTabs[j]! (permR (gR j)) := by
  have hg : gR j = gC j := by
    unfold gR gC4'
    rw [dite_eq_left hj]
    rfl
  rw [hg]
  by_cases h9 : j < 9
  · have e : gC j = jR (c4G j) := by
      rw [gC, ite_eq_left (by omega)]
      exact congrArg jR (ite_eq_left h9)
    rw [e, permR_jR, gTabs_get h9]
    exact prep_c4G h9
  · by_cases h10 : j < 10
    · have hj9 : j = 9 := by omega
      subst hj9
      have e : gC 9 = jR x4J := by
        rw [gC, ite_eq_left (by norm_num)]
        exact congrArg jR (ite_eq_right (by norm_num))
      rw [e, permR_jR, gTabs_nine]
      exact prep_x4
    · have hj10 : j = 10 := by omega
      subst hj10
      have e : gC 10 = cR := ite_eq_right (by norm_num)
      rw [e, gTabs_ten]
      exact prep_cRec

theorem lift_parts' :
    (∀ j < 11, pisInv hnsData.n gTabs[j]! (pinvs hnsData.n gTabs)[j]! = true) ∧
    InvData.witRep.size = 39 ∧ InvData.witKer.size = 39 ∧ InvData.witFix.size = 39 ∧
    (∀ w < 39, InvData.witFix[w]! < hnsData.n ∧
      evalLift gTabs (pinvs hnsData.n gTabs) InvData.parRecs InvData.witRep[w]!
        (if InvData.witKer[w]! = 1 then t4Tab[InvData.witFix[w]!]! else InvData.witFix[w]!) =
        InvData.witFix[w]!) ∧
    (∀ i < InvData.nonRep.size, ∃ p < hnsData.n,
      evalLift gTabs (pinvs hnsData.n gTabs) InvData.parRecs InvData.nonRep[i]!
        (evalLift gTabs (pinvs hnsData.n gTabs) InvData.parRecs InvData.nonRep[i]! p) ≠ p) ∧
    (∀ c < 29, InvData.nonRep.contains pReps[c]! = true ∨ ∃ p < hnsData.n, t4Tab[p]! ≠ p ∧
      evalLift gTabs (pinvs hnsData.n gTabs) InvData.parRecs pReps[c]!
        (evalLift gTabs (pinvs hnsData.n gTabs) InvData.parRecs pReps[c]! p) = p) := by
  have h := lift_parts
  unfold liftChecksT at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨fun j hj => allBelowN_spec h3 hj, h4, h5, h6, fun w hw => ?_, fun i hi => ?_,
    fun c hc => ?_⟩
  · have := allBelowN_spec h7 hw
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
  · have := allBelowN_spec h8 hi
    rw [Bool.not_eq_true', ← Bool.not_eq_true, allBelowN_iff] at this
    push Not at this
    obtain ⟨p, hp, hne⟩ := this
    exact ⟨p, hp, by simpa using hne⟩
  · have := allBelowN_spec h9 hc
    simp only [Bool.or_eq_true] at this
    rcases this with h | h
    · exact Or.inl h
    · right
      rw [Bool.not_eq_true', ← Bool.not_eq_true, allBelowN_iff] at h
      push Not at h
      obtain ⟨p, hp, hne⟩ := h
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hne
      exact ⟨p, hp, hne.1, hne.2⟩

theorem prep_gTabs_inv
    {j : ℕ} (hj : j < 11) :
    PRep hnsData.n (pinvs hnsData.n gTabs)[j]! (permR (gR j))⁻¹ :=
  prep_inv_of_pisInv (prep_gTabs hj) (lift_parts'.1 j hj)

theorem evalWordPt_spec :
    ∀ w : List ℤ, plettersOK 11 w = true → ∀ p : X,
    ((wordVal gR w • p : X) : ℕ) = evalWordPt gTabs (pinvs hnsData.n gTabs) w p
  | [], _, p => by simp [wordVal_nil, evalWordPt]
  | l :: w, hw, p => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hl11⟩, hw⟩ := hw
    have hw' : plettersOK 11 w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    rw [wordVal_cons, mul_smul, evalWordPt, ← evalWordPt_spec w hw' p]
    by_cases hpos : 0 < l
    · rw [ite_eq_left hpos, ite_eq_left hpos, show l.toNat - 1 = l.natAbs - 1 by omega]
      exact (prep_gTabs (by omega) _).symm
    · rw [ite_eq_right hpos, ite_eq_right hpos, show (-l).toNat - 1 = l.natAbs - 1 by omega]
      exact (prep_gTabs_inv (by omega) _).symm

theorem pWords_letters
    (i : ℕ) : plettersOK 11 pWords[i]! = true := by
  by_cases hi : i < 14
  · exact (p_parts.2.2.2.1 i hi).1
  · rw [getElem!_neg _ i (by rw [p_parts.2.2.1]; omega)]
    rfl

theorem gensC_coe
    (i : ℕ) : ((gensC i : C4) : RH) = wordVal gR pWords[i]! := by
  rw [gensC]
  exact map_wordVal C4.subtype gC4' _

theorem liftCF_smul :
    ∀ (f r : ℕ) (p : X),
    (((liftCF f r : C4) : RH) • p : X).val = evalLiftF gTabs (pinvs hnsData.n gTabs)
      InvData.parRecs f r p
  | 0, r, p => by simp [liftCF, evalLiftF]
  | f + 1, r, p => by
    by_cases hr : r = 0
    · subst hr
      simp [liftCF, evalLiftF]
    · rw [liftCF, evalLiftF, ite_eq_right hr, ite_eq_right hr, Subgroup.coe_mul, mul_smul,
        gensC_coe,
        ← liftCF_smul f (pparOf InvData.parRecs r) p]
      exact evalWordPt_spec _ (pWords_letters _) _

theorem liftC_smul
    (r : ℕ) (p : X) :
    (((liftC r : C4) : RH) • p : X).val =
      evalLift gTabs (pinvs hnsData.n gTabs) InvData.parRecs r p :=
  liftCF_smul r r p

end CFSG.Sporadic.HNOddCore
