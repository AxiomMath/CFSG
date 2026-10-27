module

public import Certificates.Certificate4181
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Model

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


@[expose] def z1Arr : Array ℕ :=
  compA 1755 (compA 1755 (cArr titsGenArrs gInv) titsZArr)
    (compA 1755 (cArr titsGenArrs gInv) (cArr titsGenArrs gInv))

@[expose] def z2Arr : Array ℕ :=
  compA 1755 (compA 1755 (compA 1755 (cArr titsGenArrs gInv) (cArr titsGenArrs gInv)) titsZArr)
    (cArr titsGenArrs gInv)

theorem locParts :
    locLineOK titsLinePtArr (cArr titsGenArrs gInv) = true ∧
      locVOK titsZArr z1Arr z2Arr = true ∧ wordOK locQWord = true ∧
      locQOK (tArr titsGenArrs gInv) titsZArr z1Arr (wArr titsGenArrs gInv locQWord) = true ∧
      locCollFixed titsLinePtArr (tArr titsGenArrs gInv) = true ∧
      locFixOK titsLinePtArr titsGenArrs gInv titsZArr (tArr titsGenArrs gInv) z1Arr z2Arr =
        true := by
  have h := Certificates.certificate4181
  simp only [twoF4LocCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem cM_cube : cM * (cM * cM) = 1 := by
  have h := cEl_pow.1
  apply Subtype.ext
  show cEl.1 * (cEl.1 * cEl.1) = 1
  simpa [pow_succ, mul_assoc] using h

theorem cM_inv : cM⁻¹ = cM * cM := inv_eq_of_mul_eq_one_right cM_cube

theorem cEl_inv : cEl.1⁻¹ = cEl.1 * cEl.1 := congrArg Subtype.val cM_inv

@[expose] noncomputable def z1M : ↥twoF4M := cM * zM * cM⁻¹

@[expose] noncomputable def z2M : ↥twoF4M := cM⁻¹ * zM * cM

theorem rep_zM : Rep 1755 titsZArr zM.1 := titsZ_rep

theorem rep_z1 : Rep 1755 z1Arr z1M.1 := by
  have h := rep_compA (rep_compA rep_cEl titsZ_rep) (rep_compA rep_cEl rep_cEl)
  have e : z1M.1 = cEl.1 * titsZ * (cEl.1 * cEl.1) := by
    rw [← cEl_inv]
    rfl
  rw [e]
  exact h

theorem rep_z2 : Rep 1755 z2Arr z2M.1 := by
  have h := rep_compA (rep_compA (rep_compA rep_cEl rep_cEl) titsZ_rep) rep_cEl
  have e : z2M.1 = cEl.1 * cEl.1 * titsZ * cEl.1 := by
    rw [← cEl_inv]
    rfl
  rw [e]
  exact h

@[expose] noncomputable def qEl : ↥TA := wEl locQWord

theorem rep_qEl : Rep 1755 (wArr titsGenArrs gInv locQWord) qEl.1 :=
  rep_wEl locParts.2.2.1 invsOK_gInv

@[expose] noncomputable def qM : ↥twoF4M := ⟨qEl.1, mem_twoF4M_of_mem_A qEl.2⟩

theorem V_rels : zM * z1M = z2M ∧ zM * z1M = z1M * zM ∧ zM ≠ z1M := by
  obtain ⟨-, h2, -⟩ := locParts
  simp only [locVOK, Bool.and_eq_true, Bool.not_eq_true'] at h2
  obtain ⟨⟨h21, h22⟩, h23⟩ := h2
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, fun h => ?_⟩
  · exact eq_of_eqA (rep_compA rep_zM rep_z1) rep_z2 h21
  · exact eq_of_eqA (rep_compA rep_zM rep_z1) (rep_compA rep_z1 rep_zM) h22
  · have := (eqA_iff rep_zM rep_z1).2 (congrArg Subtype.val h)
    rw [this] at h23
    exact absurd h23 (by decide)

theorem q_rels : qM * qM = zM ∧ qM * tM = tM * qM ∧ qM * z1M = z1M * qM := by
  obtain ⟨-, -, -, h4, -⟩ := locParts
  simp only [locQOK, Bool.and_eq_true] at h4
  obtain ⟨⟨h41, h42⟩, h43⟩ := h4
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · exact eq_of_eqA (rep_compA rep_qEl rep_qEl) rep_zM h41
  · exact eq_of_eqA (rep_compA rep_qEl rep_tEl) (rep_compA rep_tEl rep_qEl) h42
  · exact eq_of_eqA (rep_compA rep_qEl rep_z1) (rep_compA rep_z1 rep_qEl) h43

theorem locLineOK_spec {pts cA : Array ℕ} (h : locLineOK pts cA = true) :
    onLineP pts 0 0 = true ∧ onLineP pts cA[0]! 0 = true ∧ onLineP pts cA[cA[0]!]! 0 = true ∧
      ∀ k < 3, pts[k]! = 0 ∨ pts[k]! = cA[0]! ∨ pts[k]! = cA[cA[0]!]! := by
  simp only [locLineOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  exact ⟨ha, hb, hc, fun k hk => by simpa [or_assoc] using hd k hk⟩

theorem cEl_apply (p : Fin 1755) :
    ((cEl.1 p : Fin 1755) : ℕ) = (cArr titsGenArrs gInv)[(p : ℕ)]! := (rep_cEl p).symm

theorem cEl_apply_zero : ((cEl.1 0 : Fin 1755) : ℕ) = (cArr titsGenArrs gInv)[0]! := by
  simpa using cEl_apply 0

theorem cEl_apply_cEl_zero : ((cEl.1 (cEl.1 0) : Fin 1755) : ℕ) =
    (cArr titsGenArrs gInv)[(cArr titsGenArrs gInv)[0]!]! := by
  have h := cEl_apply (cEl.1 0)
  rwa [cEl_apply_zero] at h

theorem mem_titsLine_zero_iff (p : Fin 1755) :
    p ∈ titsLine 0 ↔ ∃ k < 3, titsLinePtArr[k]! = (p : ℕ) := by
  rw [mem_titsLine_iff]
  simp

theorem line_zero_points : (0 : Fin 1755) ∈ titsLine 0 ∧ cEl.1 0 ∈ titsLine 0 ∧
    cEl.1 (cEl.1 0) ∈ titsLine 0 ∧
    ∀ p ∈ titsLine 0, p = 0 ∨ p = cEl.1 0 ∨ p = cEl.1 (cEl.1 0) := by
  obtain ⟨ha, hb, hc, hd⟩ := locLineOK_spec locParts.1
  refine ⟨(mem_titsLine_zero_iff _).2 ?_, (mem_titsLine_zero_iff _).2 ?_,
    (mem_titsLine_zero_iff _).2 ?_, fun p hp => ?_⟩
  · simpa using onLineP_iff.1 ha
  · rw [cEl_apply_zero]
    simpa using onLineP_iff.1 hb
  · rw [cEl_apply_cEl_zero]
    simpa using onLineP_iff.1 hc
  · obtain ⟨k, hk, hkp⟩ := (mem_titsLine_zero_iff p).1 hp
    have := hd k hk
    rw [hkp] at this
    rcases this with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext (h.trans cEl_apply_zero.symm)))
    · exact Or.inr (Or.inr (Fin.ext (h.trans cEl_apply_cEl_zero.symm)))

end CFSG.Quasithin.H13.F431.TwoF4
