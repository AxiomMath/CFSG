module

public import CFSG.Sporadic.ONOddCore.LocalAutDataCheck
public import CFSG.Sporadic.ONOddCore.FirstDiscovery
public import CFSG.Sporadic.Schreier.ONCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

@[expose] def piM :
    onM →* Equiv.Perm (Fin 120) := conjU.comp rhoM

@[expose] def RM :
    Subgroup (Equiv.Perm (Fin 120)) := piM.range

@[expose] def gammaAut (d f g : ℕ) : MulAut (LinearFlag.projectiveSL 3 PSL3Four.F4) :=
  LinearFlag.conjAut 3 PSL3Four.F4 (PSL3Four.dGL ^ d) *
    LinearFlag.fieldAut 3 PSL3Four.F4 PSL3Four.frob ^ f * LinearFlag.dualAut 3 PSL3Four.F4 ^ g

@[expose] def sigmaX
    (d f g : ℕ) : MulAut onX := (thetaX.symm.trans (gammaAut d f g)).trans thetaX

@[expose] def hGens :
    List onM := [mGen 0, mGen 1, mGen 2]

@[expose] def liftImgs
    (e : LiftEntry) : List onM := e.words.map (evalPos hGens)

@[expose] def liftFun
    (e : LiftEntry) : onM → onM := substFun hGens (liftImgs e)

@[expose] def qGenPerm (j : ℕ) : Equiv.Perm (Fin 120) :=
  permOfArr 120 (localCert.quotGens.getD j #[])

@[expose] def qGroup : Subgroup (Equiv.Perm (Fin 120)) :=
  Subgroup.closure {g | g ∈ [qGenPerm 0, qGenPerm 1]}

theorem qGenPerm_mem (j : ℕ) (hj : j < 2) : qGenPerm j ∈ qGroup := by
  apply Subgroup.subset_closure
  interval_cases j <;> simp

@[expose] def qGens : List qGroup :=
  [⟨qGenPerm 0, qGenPerm_mem 0 (by norm_num)⟩, ⟨qGenPerm 1, qGenPerm_mem 1 (by norm_num)⟩]

@[expose] def qImgPerm (r : QuotRecord) (j : ℕ) : Equiv.Perm (Fin 120) :=
  permOfArr 120 (r.images.getD j #[])

@[expose] def quotFun (r : QuotRecord) : qGroup → Equiv.Perm (Fin 120) :=
  substFun qGens [qImgPerm r 0, qImgPerm r 1]

theorem hGens_val :
    hGens.map (fun h => (h : Equiv.Perm (Fin N))) = onMgens := by
  have h3 : onMgens.length = 3 := onMgens_length
  apply List.ext_getElem (by simp [hGens, h3])
  intro i hi _
  have hi3 : i < 3 := by simpa [hGens] using hi
  interval_cases i <;> simp [hGens, mGen_val, h3]

theorem r3e_on_local_automorphism_certificate_data :
    localCert.quotGens.length = 2 ∧ (∀ a ∈ localCert.quotGens, permArr120 a = true) ∧
      localCert.records.map (fun r => (r.diag, r.field, r.graph)) = tripleList ∧
      (∀ r ∈ localCert.records, r.images.length = 2 ∧ (∀ a ∈ r.images, permArr120 a = true) ∧
        ∀ e ∈ r.lifts, e.words.length = 3 ∧ (∀ w ∈ e.words, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) ∧
          (e.power = 1 ∨ e.power = 3)) ∧
      (∀ m, piM m = onu * rhoM m * onu⁻¹) ∧ RM = piM.range ∧
      (∀ d f g, gammaAut d f g = LinearFlag.conjAut 3 PSL3Four.F4 (PSL3Four.dGL ^ d) *
        LinearFlag.fieldAut 3 PSL3Four.F4 PSL3Four.frob ^ f *
          LinearFlag.dualAut 3 PSL3Four.F4 ^ g) ∧
      (∀ d f g x, sigmaX d f g x = thetaX (gammaAut d f g (thetaX.symm x))) ∧
      hGens.map (fun h => (h : Equiv.Perm (Fin N))) = onMgens ∧
      (∀ e, liftFun e = substFun hGens (e.words.map (evalPos hGens))) ∧
      ∀ r, quotFun r = substFun qGens [qImgPerm r 0, qImgPerm r 1] := by
  have h := local_form_cert
  simp only [localFormOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h
  refine ⟨h1, h2, h3, fun r hr => ?_, fun _ => rfl, rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    hGens_val, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨⟨hi, ha⟩, hl⟩ := h4 r hr
  refine ⟨hi, ha, fun e he => ?_⟩
  have := hl e he
  simp only [liftFormOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at this
  obtain ⟨⟨h5, h6⟩, h7⟩ := this
  exact ⟨h5, h6, h7⟩

end CFSG.Sporadic.ONOddCore
