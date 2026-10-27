
module

public import CFSG.Sporadic.J4.QT2LocProofBase

public import CFSG.Sporadic.J4.QTOutNorm
public import Certificates.Certificate4008

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.Th Matrix

section Mat

variable (hM : MatFacts)
include hM

end Mat

theorem exists_rep (_hF : J4Facts) (g : J) :
    ∃ ℓ < 7, ∃ h ∈ Hj, ∃ h' ∈ Hj, g = h * (pathElt (repPaths.getD ℓ []))⁻¹ * h' :=
  Certificates.certificate4008.1 g

theorem mem_Hj_of_conj_mem (hF : J4Facts) {g x : J} (hx : x ∈ tSet)
    (hg : g⁻¹ * x * g ∈ Eg uJ 11) : g ∈ Hj := by
  have hM := hF.mat
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := exists_rep hF g
  set u := pathElt (repPaths.getD ℓ []) with hu
  have hx' : h⁻¹ * x * h ∈ tSet := (tSet_conj hM h hh).2 x hx
  have e : (h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h') = h'⁻¹ * (u * (h⁻¹ * x * h) * u⁻¹) * h' := by
    group
  rw [e] at hg
  have hg2 : u * (h⁻¹ * x * h) * u⁻¹ ∈ Eg uJ 11 := by
    have := Hj_normalizes_Eg hM h' hh' _ hg
    simpa [mul_assoc] using this
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    have : u = 1 := by simp [hu, repPaths, pathElt]
    rw [this]
    simpa using Hj.mul_mem hh hh'
  · exact absurd hg2 (not_mem_Eg_conj hM (by omega) (by omega) hx')

theorem centralizer_le_Hj_of_T (hF : J4Facts) {c : ℕ} (hc : c ∈ tMasks) {x : J}
    (hx : x * eta uJ 11 c = eta uJ 11 c * x) : x ∈ Hj := by
  refine mem_Hj_of_conj_mem hF (x := eta uJ 11 c) ⟨c, hc, rfl⟩ ?_
  have : x⁻¹ * eta uJ 11 c * x = eta uJ 11 c := by
    rw [mul_assoc, ← hx, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [this]
  exact eta_mem_Eg 11 le_rfl c

theorem constrained_centralizer_T (hF : J4Facts) {c : ℕ} (hc : c ∈ tMasks) :
    ∃ N : Subgroup J, N ≤ Subgroup.centralizer ({eta uJ 11 c} : Set J) ∧
      (∀ q ∈ Subgroup.centralizer ({eta uJ 11 c} : Set J), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
      IsPGroup 2 ↥N ∧
      ∀ q ∈ Subgroup.centralizer ({eta uJ 11 c} : Set J), (∀ e ∈ N, q * e = e * q) → q ∈ N := by
  have hM := hF.mat
  refine constrained_of_centralizer_le Hj (Eg uJ 11) (eta uJ 11 c) (isPGroup_Eg (elem_uJ hM)) ?_
    (eta_mem_Eg 11 le_rfl c) (Hj_normalizes_Eg hM) (centralizer_Hj hM hF) ?_
  · intro x hx e he
    obtain ⟨c₁, -, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx
    obtain ⟨c₂, -, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 he
    exact eta_comm (elem_uJ hM) c₁ c₂
  · intro q hq
    have h := comm_of_mem_centralizer hq
    exact centralizer_le_Hj_of_T hF hc h

end CFSG.Sporadic.J4.QT2
