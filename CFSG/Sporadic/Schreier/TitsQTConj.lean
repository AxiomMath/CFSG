module

public import CFSG.Sporadic.Schreier.TitsQTCheck
public import CFSG.Sporadic.Schreier.TitsCentral

public noncomputable section

namespace CFSG.Sporadic.Schreier.TitsQT

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits

theorem titsT_zero :
    titsT 0 = titsDGen 0 := titsDerived_perm (by norm_num)

theorem titsT_one :
    titsT 1 = titsDGen 1 := titsDerived_perm (by norm_num)

theorem rep_conjD0 : Rep 1755 conjD0 (titsDGen 0) := by
  have h := titsT_rep (i := 0) (by norm_num)
  rw [titsT_zero] at h
  exact h

theorem rep_conjD1 : Rep 1755 conjD1 (titsDGen 1) := by
  have h := titsT_rep (i := 1) (by norm_num)
  rw [titsT_one] at h
  exact h

theorem isInvA_conjD0 : isInvA 1755 conjD0 conjD0Inv = true :=
  isInvA_of_allPermsOK (j := 0) titsChains_check.2.2.2.2.2.2.1
    (by rw [titsDerivedArrs_size]; norm_num)

theorem isInvA_conjD1 : isInvA 1755 conjD1 conjD1Inv = true :=
  isInvA_of_allPermsOK (j := 1) titsChains_check.2.2.2.2.2.2.1
    (by rw [titsDerivedArrs_size]; norm_num)

theorem rep_conjD0Inv : Rep 1755 conjD0Inv (titsDGen 0)⁻¹ :=
  rep_inv_of_isInvA rep_conjD0 isInvA_conjD0

theorem rep_conjD1Inv : Rep 1755 conjD1Inv (titsDGen 1)⁻¹ :=
  rep_inv_of_isInvA rep_conjD1 isInvA_conjD1

theorem rep_conjG : Rep 1755 conjGArr
    ((titsDGen 1)⁻¹ * titsDGen 0 * (titsDGen 1)⁻¹ * titsDGen 0 * titsDGen 0) :=
  rep_compA (rep_compA (rep_compA (rep_compA rep_conjD1Inv rep_conjD0) rep_conjD1Inv)
    rep_conjD0) rep_conjD0

theorem rep_conjGInv : Rep 1755 conjGInvArr
    ((titsDGen 0)⁻¹ * (titsDGen 0)⁻¹ * titsDGen 1 * (titsDGen 0)⁻¹ * titsDGen 1) :=
  rep_compA (rep_compA (rep_compA (rep_compA rep_conjD0Inv rep_conjD0Inv) rep_conjD1)
    rep_conjD0Inv) rep_conjD1

theorem conjugators_mem_titsD :
    (titsDGen 1)⁻¹ * titsDGen 0 * (titsDGen 1)⁻¹ * titsDGen 0 ^ 2 ∈ titsD ∧
      (titsDGen 0)⁻¹ ∈ titsD :=
  ⟨mul_mem (mul_mem (mul_mem (inv_mem (titsDGen_mem_titsD (by norm_num)))
    (titsDGen_mem_titsD (by norm_num))) (inv_mem (titsDGen_mem_titsD (by norm_num))))
    (pow_mem (titsDGen_mem_titsD (by norm_num)) 2), inv_mem (titsDGen_mem_titsD (by norm_num))⟩

theorem QT_unique_Tits_central_involution_noncommuting_Sylow_conjugates
    (g h : Equiv.Perm (Fin 1755))
    (hg : g = (titsDGen 1)⁻¹ * titsDGen 0 * (titsDGen 1)⁻¹ * titsDGen 0 ^ 2)
    (hh : h = (titsDGen 0)⁻¹) :
    g * titsZ * g⁻¹ ∈ titsS ∧ h * titsZ * h⁻¹ ∈ titsS ∧
      g * titsZ * g⁻¹ * (h * titsZ * h⁻¹) ≠ h * titsZ * h⁻¹ * (g * titsZ * g⁻¹) ∧
      (g * titsZ * g⁻¹ * (h * titsZ * h⁻¹)) 12 = 115 ∧
      (h * titsZ * h⁻¹ * (g * titsZ * g⁻¹)) 12 = 117 := by
  have eX : g * titsZ * g⁻¹ =
      ((titsDGen 1)⁻¹ * titsDGen 0 * (titsDGen 1)⁻¹ * titsDGen 0 * titsDGen 0) * titsZ *
        ((titsDGen 0)⁻¹ * (titsDGen 0)⁻¹ * titsDGen 1 * (titsDGen 0)⁻¹ * titsDGen 1) := by
    subst hg
    simp only [pow_two, mul_inv_rev, inv_inv, mul_assoc]
  have eY : h * titsZ * h⁻¹ = (titsDGen 0)⁻¹ * titsZ * titsDGen 0 := by
    subst hh
    simp only [inv_inv]
  have hX : Rep 1755 conjXArr (g * titsZ * g⁻¹) := by
    rw [eX]
    exact rep_compA (rep_compA rep_conjG titsZ_rep) rep_conjGInv
  have hY : Rep 1755 conjYArr (h * titsZ * h⁻¹) := by
    rw [eY]
    exact rep_compA (rep_compA rep_conjD0Inv titsZ_rep) rep_conjD0
  obtain ⟨hsx, hsy, h115, h117⟩ := titsQT_check
  have h1 := (rep_compA hX hY).apply (show 12 < 1755 by norm_num)
  have h2 := (rep_compA hY hX).apply (show 12 < 1755 by norm_num)
  rw [h115] at h1
  rw [h117] at h2
  refine ⟨mem_titsS_of_sift hX hsx, mem_titsS_of_sift hY hsy, ?_, Fin.ext h1.symm,
    Fin.ext h2.symm⟩
  intro hxy
  rw [hxy] at h1
  omega

end CFSG.Sporadic.Schreier.TitsQT
