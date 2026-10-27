module

public import CFSG.Sporadic.Schreier.ONInvolution
public import CFSG.Sporadic.Schreier.ONIntersection
public import CFSG.Sporadic.Schreier.ONFirstCentralizer

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates
open CFSG.ComponentClassification.OuterAutomorphisms

theorem prep_t :
    PRep N tArr ont := prep_wordArr words_ok.2.2.2.2.2.2.1

theorem ont_mem_M :
    ont ∈ onM := by
  have h := mFacts.mem prep_t (evalS_mem _) qt_cert.2.2.2.2.1
  rwa [onMChain_sub] at h

theorem ont_eq :
    ont = onc * onz * onc⁻¹ :=
  eq_of_peq prep_t (prep_conj prep_onc prep_onc_inv prep_z) qt_cert.2.2.2.2.2.1

theorem ont_ne_z :
    ont ≠ onz := by
  intro h
  have h1 : peq nPts tArr zArr = true := (peq_iff prep_t prep_z).2 h
  rw [qt_cert.2.2.2.2.2.2.1] at h1
  exact absurd h1 (by decide)

theorem orderOf_ont :
    orderOf ont = 2 := by
  have h2 : ont ^ 2 = 1 := by
    rw [ont_eq, sq, show onc * onz * onc⁻¹ * (onc * onz * onc⁻¹) = onc * (onz * onz) * onc⁻¹ by
      group, onz_sq, mul_one, mul_inv_cancel]
  refine orderOf_eq_prime h2 fun h => onz_ne_one ?_
  rw [ont_eq] at h
  calc onz = onc⁻¹ * (onc * onz * onc⁻¹) * onc := by group
    _ = 1 := by rw [h]; group

theorem onc_mem_P :
    onc ∈ Pv := evalS_mem _

theorem onM1_eq_centralizer_t :
    onM1 = Pv ⊓ Subgroup.centralizer {ont} := by
  ext x
  rw [mem_M1_iff, onM_eq_centralizer_z, Subgroup.mem_inf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ont_eq]
  have hc := onc_mem_P
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := mul_mem (mul_mem hc h1) (inv_mem hc)
      rwa [show onc * (onc⁻¹ * x * onc) * onc⁻¹ = x by group] at this
    · calc x * (onc * onz * onc⁻¹) = onc * ((onc⁻¹ * x * onc) * onz) * onc⁻¹ := by group
        _ = onc * (onz * (onc⁻¹ * x * onc)) * onc⁻¹ := by rw [h2]
        _ = onc * onz * onc⁻¹ * x := by group
  · rintro ⟨h1, h2⟩
    refine ⟨mul_mem (mul_mem (inv_mem hc) h1) hc, ?_⟩
    calc onc⁻¹ * x * onc * onz = onc⁻¹ * (x * (onc * onz * onc⁻¹)) * onc := by group
      _ = onc⁻¹ * (onc * onz * onc⁻¹ * x) * onc := by rw [h2]
      _ = onz * (onc⁻¹ * x * onc) := by group

theorem onM1_le_P :
    onM1 ≤ Pv := by
  rw [onM1_eq_centralizer_t]
  exact inf_le_left

theorem onM_sup_M1 :
    onM ⊔ onM1 = Pv :=
  Subgroup.eq_of_le_of_card_ge (sup_le onM_le onM1_le_P) (by rw [card_Pv, card_joint])

theorem onM1_outer_solvable :
    Group.IsSolvable (Outer onM1) :=
  (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism mToM1).2.1
    at_on_first_centralizer_schreier

theorem at_on_two_centralizer_generation :
    ont ∈ onM ∧ orderOf ont = 2 ∧ ont ≠ onz ∧ ont = onc * onz * onc⁻¹ ∧
      onM1 = Pv ⊓ Subgroup.centralizer {ont} ∧ onM ⊔ onM1 = Pv ∧
      Group.IsSolvable (Outer onM1) :=
  ⟨ont_mem_M, orderOf_ont, ont_ne_z, ont_eq, onM1_eq_centralizer_t, onM_sup_M1,
    onM1_outer_solvable⟩

end CFSG.ONSchreier
