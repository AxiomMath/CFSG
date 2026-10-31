
module

public import CFSG.Sporadic.J4.QT2LocFixCheck
public import CFSG.Sporadic.J4.QT2LocCntProofBase

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix
open scoped Classical

def Rel (ℓ : ℕ) (p q : Row) : Prop := ∃ g : J, g • w₀ = p ∧ g⁻¹ • q ∈ Dlt ℓ

theorem Dlt_smul_mem {ℓ : ℕ} {h : J} (hh : h ∈ Hj) {v : Row} (hv : v ∈ Dlt ℓ) :
    h • v ∈ Dlt ℓ := by
  obtain ⟨k, hk, rfl⟩ := hv
  exact ⟨h * k, Hj.mul_mem hh hk, (mul_smul h k _).symm⟩

theorem Rel_smul_w₀ (hF : J4Facts) {ℓ : ℕ} {g : J} {q : Row} :
    Rel ℓ (g • w₀) q ↔ g⁻¹ • q ∈ Dlt ℓ := by
  constructor
  · rintro ⟨g', hg', hmem⟩
    have h1 : (g⁻¹ * g') • w₀ = w₀ := by rw [mul_smul, hg', inv_smul_smul]
    have hH : g⁻¹ * g' ∈ Hj := mem_Hj_of_smul_root hF h1
    have := Dlt_smul_mem hH hmem
    rwa [← mul_smul, mul_assoc, mul_inv_cancel, mul_one] at this
  · exact fun h => ⟨g, rfl, h⟩

theorem eta_smul_toRow (hM : MatFacts) (c : ℕ) (v : V2) :
    eta uJ 11 c • toRow v.toVec =
      toRow (frApply (frTable (etaRows (uTab (locMats ()) (locInvs ())) 11 c)) v).toVec := by
  have hinv : (eta uJ 11 c)⁻¹ = eta uJ 11 c :=
    inv_eq_of_mul_eq_one_right (eta_sq (elem_uJ hM) c)
  rw [← ofRow_inj, smul_row, frApply_toVec_eq_vecMul, hinv, ← Mx_eta hM 11 le_rfl c]
  rfl

theorem eta_moves_rep (hM : MatFacts) {ℓ c : ℕ} (hℓ : ℓ < 7)
    (hd : differs (frApply (frTable (etaRows (uTab (locMats ()) (locInvs ())) 11 c))
      (pathVec (repPaths.getD ℓ []))) (pathVec (repPaths.getD ℓ [])) = true) :
    eta uJ 11 c • rep ℓ ≠ rep ℓ := by
  intro h
  rw [rep_toVec hM hℓ, eta_smul_toRow hM] at h
  exact differs_toVec hd h

private theorem rep_zero : rep 0 = w₀ := by
  simp [rep, uElt, repPaths, pathElt]

private theorem smul_rep_form (hM : MatFacts) {ℓ : ℕ} {h h' : J} (hh' : h' ∈ Hj) :
    (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') • w₀ = h • rep ℓ := by
  rw [mul_smul, mul_smul, smul_root_of_mem_Hj hM hh', rep_eq]
  rfl

private theorem fix2B_facts : ∀ l ∈ List.range' 1 4, ∀ c ∈ tMasks,
    differs (frApply (frTable (etaRows (uTab (locMats ()) (locInvs ())) 11 c))
      (pathVec (repPaths.getD l []))) (pathVec (repPaths.getD l [])) = true := by
  have h := chkFix2B_true
  unfold chkFix2B at h
  simp only [List.all_eq_true] at h
  exact h

private theorem fix2A_facts : ∀ l ∈ List.range' 2 2, ∀ c ∈ zMasks,
    differs (frApply (frTable (etaRows (uTab (locMats ()) (locInvs ())) 11 c))
      (pathVec (repPaths.getD l []))) (pathVec (repPaths.getD l [])) = true := by
  have h := chkFix2A_true
  unfold chkFix2A at h
  simp only [List.all_eq_true] at h
  exact h

theorem conj_fix_transfer {g k : J} {x : J} {p : Row} (hfix : (g * x * g⁻¹) • (k • p) = k • p) :
    x • ((g⁻¹ * k) • p) = (g⁻¹ * k) • p := by
  have e : g⁻¹ * (g * x * g⁻¹) = x * g⁻¹ := by group
  calc x • ((g⁻¹ * k) • p) = x • (g⁻¹ • (k • p)) := by rw [mul_smul]
    _ = (x * g⁻¹) • (k • p) := (mul_smul _ _ _).symm
    _ = (g⁻¹ * (g * x * g⁻¹)) • (k • p) := by rw [e]
    _ = g⁻¹ • ((g * x * g⁻¹) • (k • p)) := mul_smul _ _ _
    _ = g⁻¹ • (k • p) := by rw [hfix]
    _ = (g⁻¹ * k) • p := (mul_smul _ _ _).symm

theorem eq_of_inv_smul_eq {g k : J} (h : (g⁻¹ * k) • w₀ = w₀) : k • w₀ = g • w₀ := by
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h

end CFSG.Sporadic.J4.QT2
