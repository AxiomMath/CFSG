module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutPt
public import Certificates.Certificate4239

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

section Char


theorem lineChar_parts : lineKleinOK cz.T = true ∧ kleinLineOK cz = true := by
  have h : lineCharOn cz = true := by
    rw [cz_eq]
    exact Certificates.certificate4239
  simpa only [lineCharOn, Bool.and_eq_true] using h

theorem lineKlein_spec {l : ℕ} (hl : l < 2457) :
    mulR cz.T[lnPt l 0]! cz.T[lnPt l 1]! = cz.T[lnPt l 2]! ∧
      mulR cz.T[lnPt l 1]! cz.T[lnPt l 0]! = cz.T[lnPt l 2]! := by
  have h := lineChar_parts.1
  unfold lineKleinOK at h
  have := allLt_spec h hl
  simpa only [Bool.and_eq_true, beq_iff_eq] using this

theorem line_klein (l : Fin 2457) :
    zElt (lpt0 l) * zElt (lpt1 l) = zElt (lpt2 l) ∧
      zElt (lpt1 l) * zElt (lpt0 l) = zElt (lpt2 l) := by
  obtain ⟨h1, h2⟩ := lineKlein_spec l.2
  have e0 : RepE d4E cz.T[lnPt l 0]! (zElt (lpt0 l)) := repE_zElt (lpt0 l)
  have e1 : RepE d4E cz.T[lnPt l 1]! (zElt (lpt1 l)) := repE_zElt (lpt1 l)
  have e2 : RepE d4E cz.T[lnPt l 2]! (zElt (lpt2 l)) := repE_zElt (lpt2 l)
  refine ⟨eq_of_repE d4E_injective ?_ e2, eq_of_repE d4E_injective ?_ e2⟩
  · rw [← h1]
    exact repE_mul e0 e1
  · rw [← h2]
    exact repE_mul e1 e0

theorem kleinLine_spec {q : ℕ} (hq : q < 819) (hq0 : q ≠ 0)
    (hc : mulR cz.T[0]! cz.T[q]! = mulR cz.T[q]! cz.T[0]!)
    (hm : memR cz.T cz.idx (mulR cz.T[0]! cz.T[q]!) = true) :
    ∃ l < 2457, lnPt l 0 = 0 ∧ lnPt l 1 = min q (cz.idx (mulR cz.T[0]! cz.T[q]!)) ∧
      lnPt l 2 = max q (cz.idx (mulR cz.T[0]! cz.T[q]!)) := by
  have h := lineChar_parts.2
  unfold kleinLineOK at h
  have := allLt_spec h hq
  have h0 : (q == 0) = false := by simpa using hq0
  have h1 : (mulR cz.T[0]! cz.T[q]! == mulR cz.T[q]! cz.T[0]!) = true := beq_iff_eq.2 hc
  rw [h0, h1, hm] at this
  simp only [Bool.false_or, Bool.not_true, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨l, hl, ⟨hl0, hl1⟩, hl2⟩ := this
  exact ⟨l, hl, hl0, hl1, hl2⟩

theorem klein_line (a b c : Fin 819) (hab : a ≠ b) (h1 : zElt a * zElt b = zElt c)
    (h2 : zElt b * zElt a = zElt c) : ∃ l : Fin 2457, lineSet l = {a, b, c} := by
  obtain ⟨g, hg⟩ := exists_smul_pt0_eq a
  have hz : ∀ p : Fin 819, zElt (act g⁻¹ p) = g⁻¹ * zElt p * g := fun p => by
    rw [zElt_act, inv_inv]
  have hga : ∀ p : Fin 819, act g (act g⁻¹ p) = p := fun p => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hga' : ∀ p : Fin 819, act g⁻¹ (act g p) = p := fun p => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have ha' : act g⁻¹ a = pt0 := by
    rw [← hg, smul_pt_def, hga']
  have hb' : act g⁻¹ b ≠ pt0 := fun h => hab ((act g⁻¹).injective (h.trans ha'.symm)).symm
  have e1 : zElt pt0 * zElt (act g⁻¹ b) = zElt (act g⁻¹ c) := by
    rw [← ha', hz, hz, hz, ← h1]
    group
  have e2 : zElt (act g⁻¹ b) * zElt pt0 = zElt (act g⁻¹ c) := by
    rw [← ha', hz, hz, hz, ← h2]
    group
  set b' := act g⁻¹ b with hb'def
  set c' := act g⁻¹ c with hc'def
  have hT : ∀ p : Fin 819, RepE d4E cz.T[p.1]! (zElt p) := repE_zElt
  have hv : ∀ p : Fin 819, validR cz.T[p.1]! = true := fun p => validR_cz p.2
  have hsz : ∀ p : Fin 819, cz.T[p.1]!.size = 24 := fun p => size_of_validR (hv p)
  have hP : RepE d4E (mulR cz.T[0]! cz.T[b'.1]!) (zElt pt0 * zElt b') :=
    repE_mul (hT pt0) (hT b')
  have hP' : RepE d4E (mulR cz.T[b'.1]! cz.T[0]!) (zElt b' * zElt pt0) :=
    repE_mul (hT b') (hT pt0)
  have hvP : validR (mulR cz.T[0]! cz.T[b'.1]!) = true := validR_mulR (hsz pt0) (hv b')
  have hvP' : validR (mulR cz.T[b'.1]! cz.T[0]!) = true := validR_mulR (hsz b') (hv pt0)
  have hcomm : mulR cz.T[0]! cz.T[b'.1]! = mulR cz.T[b'.1]! cz.T[0]! :=
    (eq_iff_of_repE hvP hvP' hP hP').2 (e1.trans e2.symm)
  have hPeq : mulR cz.T[0]! cz.T[b'.1]! = cz.T[c'.1]! :=
    (eq_iff_of_repE hvP (hv c') hP (hT c')).2 e1
  have hidx : cz.idx (mulR cz.T[0]! cz.T[b'.1]!) = c'.1 := by
    rw [hPeq]
    exact idx_cz c'.2
  have hmem : memR cz.T cz.idx (mulR cz.T[0]! cz.T[b'.1]!) = true := by
    rw [hPeq]
    unfold memR
    rw [idx_cz c'.2]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_self_eq_true, and_true]
    exact lt_size_cz c'.2
  have hq0 : b'.1 ≠ 0 := fun h => hb' (Fin.ext h)
  obtain ⟨l, hl, hl0, hl1, hl2⟩ := kleinLine_spec b'.2 hq0 hcomm hmem
  rw [hidx] at hl1 hl2
  have hline : lineSet ⟨l, hl⟩ = {pt0, b', c'} := by
    rw [lineSet]
    apply finset3_eq
    simp only [lpt0, lpt1, lpt2, pt0, Fin.ext_iff] at *
    omega
  refine ⟨g • ⟨l, hl⟩, ?_⟩
  rw [lineSet_smul, hline, Finset.image_insert, Finset.image_insert, Finset.image_singleton,
    ← smul_pt_def, hg, hb'def, hc'def, hga, hga]

end Char

section Aut


theorem exists_image_lineSet_aut (α : MulAut D) (l : Fin 2457) :
    ∃ l' : Fin 2457, (lineSet l).image (autPt α) = lineSet l' := by
  obtain ⟨hk1, hk2⟩ := line_klein l
  have hab : lpt0 l ≠ lpt1 l := by
    intro h
    have h1 := (lnPt_asc l.2).1
    have h2 : lnPt l 0 = lnPt l 1 := congrArg Fin.val h
    omega
  have h1 : zElt (autPt α (lpt0 l)) * zElt (autPt α (lpt1 l)) = zElt (autPt α (lpt2 l)) := by
    rw [autPt_apply, autPt_apply, autPt_apply, ← map_mul, hk1]
  have h2 : zElt (autPt α (lpt1 l)) * zElt (autPt α (lpt0 l)) = zElt (autPt α (lpt2 l)) := by
    rw [autPt_apply, autPt_apply, autPt_apply, ← map_mul, hk2]
  obtain ⟨l', hl'⟩ := klein_line _ _ _ ((autPt α).injective.ne hab) h1 h2
  refine ⟨l', ?_⟩
  rw [hl', lineSet, Finset.image_insert, Finset.image_insert, Finset.image_singleton]

@[expose] noncomputable def autLnFun (α : MulAut D) (l : Fin 2457) : Fin 2457 :=
  Classical.choose (exists_image_lineSet_aut α l)

theorem lineSet_autLnFun (α : MulAut D) (l : Fin 2457) :
    lineSet (autLnFun α l) = (lineSet l).image (autPt α) :=
  (Classical.choose_spec (exists_image_lineSet_aut α l)).symm

theorem autLnFun_mul (α β : MulAut D) (l : Fin 2457) :
    autLnFun (α * β) l = autLnFun α (autLnFun β l) := by
  apply lineSet_injective
  rw [lineSet_autLnFun, lineSet_autLnFun, lineSet_autLnFun, map_mul, Equiv.Perm.coe_mul,
    ← Finset.image_image]

theorem autLnFun_one (l : Fin 2457) : autLnFun 1 l = l := by
  apply lineSet_injective
  rw [lineSet_autLnFun]
  simp

@[expose] noncomputable def autLn : MulAut D →* Equiv.Perm (Fin 2457) where
  toFun α :=
    { toFun := autLnFun α
      invFun := autLnFun α⁻¹
      left_inv := fun l => by rw [← autLnFun_mul, inv_mul_cancel, autLnFun_one]
      right_inv := fun l => by rw [← autLnFun_mul, mul_inv_cancel, autLnFun_one] }
  map_one' := Equiv.ext autLnFun_one
  map_mul' α β := Equiv.ext (autLnFun_mul α β)

theorem lineSet_autLn (α : MulAut D) (l : Fin 2457) :
    lineSet (autLn α l) = (lineSet l).image (autPt α) :=
  lineSet_autLnFun α l

theorem autLn_conj (g : D) : autLn (MulAut.conj g) = lineAct g :=
  Equiv.ext fun l => lineSet_injective (by
    rw [lineSet_autLn, autPt_conj]
    exact (lineSet_lineActFun g l).symm)

theorem mem_lineSet_autPt_iff (α : MulAut D) (p : Fin 819) (l : Fin 2457) :
    autPt α p ∈ lineSet (autLn α l) ↔ p ∈ lineSet l := by
  rw [lineSet_autLn, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [← (autPt α).injective hqp]
    exact hq
  · intro hp
    exact ⟨p, hp, rfl⟩

end Aut

end CFSG.Quasithin.D4Hex
