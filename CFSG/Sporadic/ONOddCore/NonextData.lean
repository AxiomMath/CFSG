module

public import CFSG.Sporadic.ONOddCore.NonextPayload
public import CFSG.Sporadic.ONOddCore.LocalAutData

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier

@[expose] def betaFun
    (r : ℕ) : onM → onM := liftFun (flatLifts.getD r default)

@[expose] def exclRec (r : ℕ) : ExclRec :=
  (nonextCert.excluded.find? fun x => x.index == r).getD default

@[expose] def innerRec (r : ℕ) : InnerRec :=
  (nonextCert.inner.find? fun y => y.index == r).getD default

@[expose] def dElem
    (r : ℕ) : onM := evalPos hGens (exclRec r).normWord

@[expose] def sIdx (r : ℕ) : ℕ := (exclRec r).second

@[expose] def uElem
    (r : ℕ) : onM := evalPos hGens (exclRec r).conjWord

@[expose] def etaFun
    (r : ℕ) (m : onM) : onM := uElem r * betaFun (sIdx r) m * (uElem r)⁻¹

@[expose] def bElem
    (r : ℕ) : onM := evalPos hGens (innerRec r).conjWord

@[expose] def ambGens :
    List (Equiv.Perm (Fin N)) :=
  [mGen 0, mGen 1, mGen 2, onc * mGen 0 * onc⁻¹, onc * mGen 1 * onc⁻¹, onc * mGen 2 * onc⁻¹]

@[expose] def exclIdx : List ℕ := [2, 3, 4, 6, 9, 10, 12, 13]

@[expose] def innerIdx : List ℕ := [0, 1, 5, 7]

theorem flatLifts_length : flatLifts.length = 16 := by
  have h := local_form_cert
  simp only [localFormOK, Bool.and_eq_true, beq_iff_eq] at h
  rw [flatLifts, List.length_flatMap, h.2]
  rfl

theorem exclRec_index {r : ℕ} (hr : r ∈ exclIdx) : exclRec r ∈ nonextCert.excluded ∧
    (exclRec r).index = r := by
  have hmap : nonextCert.excluded.map ExclRec.index = exclIdx := by decide
  rw [← hmap, List.mem_map] at hr
  obtain ⟨x, hx, hxr⟩ := hr
  cases hf : nonextCert.excluded.find? (fun x => x.index == r) with
  | none =>
    have := List.find?_eq_none.1 hf x hx
    simp [hxr] at this
  | some y =>
    rw [exclRec, hf, Option.getD_some]
    exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

theorem innerRec_index {r : ℕ} (hr : r ∈ innerIdx) : innerRec r ∈ nonextCert.inner ∧
    (innerRec r).index = r := by
  have hmap : nonextCert.inner.map InnerRec.index = innerIdx := by decide
  rw [← hmap, List.mem_map] at hr
  obtain ⟨y, hy, hyr⟩ := hr
  cases hf : nonextCert.inner.find? (fun y => y.index == r) with
  | none =>
    have := List.find?_eq_none.1 hf y hy
    simp [hyr] at this
  | some y' =>
    rw [innerRec, hf, Option.getD_some]
    exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

theorem ctuc_on_local_nonextendability_certificate_data :
    flatLifts = localCert.records.flatMap QuotRecord.lifts ∧ flatLifts.length = 16 ∧
      (∀ r, betaFun r = liftFun (flatLifts.getD r default)) ∧
      nonextCert.excluded.map ExclRec.index = exclIdx ∧
      nonextCert.inner.map InnerRec.index = innerIdx ∧
      (∀ x ∈ nonextCert.excluded, (∀ l ∈ x.normWord, 1 ≤ l ∧ l ≤ 3) ∧
        (∀ l ∈ x.conjWord, 1 ≤ l ∧ l ≤ 3) ∧ x.second < 16) ∧
      (∀ y ∈ nonextCert.inner, ∀ l ∈ y.conjWord, 1 ≤ l ∧ l ≤ 3) ∧
      (∀ l ∈ nonextCert.relationWord, 1 ≤ l ∧ l ≤ 6) ∧
      hGens = [mGen 0, mGen 1, mGen 2] ∧
      ambGens = [(mGen 0 : Equiv.Perm (Fin N)), mGen 1, mGen 2, onc * mGen 0 * onc⁻¹,
        onc * mGen 1 * onc⁻¹, onc * mGen 2 * onc⁻¹] ∧
      (∀ r ∈ exclIdx, exclRec r ∈ nonextCert.excluded ∧ (exclRec r).index = r ∧
        dElem r = evalPos hGens (exclRec r).normWord ∧ sIdx r = (exclRec r).second ∧
        uElem r = evalPos hGens (exclRec r).conjWord ∧
        ∀ m, etaFun r m = uElem r * betaFun (sIdx r) m * (uElem r)⁻¹) ∧
      ∀ r ∈ innerIdx, innerRec r ∈ nonextCert.inner ∧ (innerRec r).index = r ∧
        bElem r = evalPos hGens (innerRec r).conjWord := by
  refine ⟨rfl, flatLifts_length, fun _ => rfl, by decide, by decide, by decide, by decide,
    by decide, rfl, rfl,
    fun r hr => ⟨(exclRec_index hr).1, (exclRec_index hr).2, rfl, rfl, rfl, fun _ => rfl⟩,
    fun r hr => ⟨(innerRec_index hr).1, (innerRec_index hr).2, rfl⟩⟩

end CFSG.Sporadic.ONOddCore
