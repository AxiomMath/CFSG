module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Forest
public import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false

theorem card_fix_conj {n : ℕ} (g σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun p => (σ * g * σ⁻¹) p = p).card =
      (Finset.univ.filter fun p => g p = p).card := by
  refine Finset.card_bij (fun p _ => σ.symm p) ?_ ?_ ?_
  · intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have h1 : σ (g (σ.symm p)) = p := by
      simpa [Equiv.Perm.mul_apply, Equiv.Perm.inv_def] using hp'
    have := congrArg σ.symm h1
    simpa using this
  · intro p _ q _ h
    exact σ.symm.injective h
  · intro q hq
    have hq' := (Finset.mem_filter.1 hq).2
    refine ⟨σ q, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, hq']

theorem not_conj_model : ¬ IsConj zM tM := by
  rintro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hc' : c.1 * titsZ * c.1⁻¹ = tEl.1 := congrArg Subtype.val hc
  obtain ⟨⟨-, -, -, -, h27, h91⟩, -⟩ := Certificates.certificate4180
  rw [← tEl_eq] at h27
  have := card_fix_conj titsZ c.1
  rw [hc', h91, h27] at this
  exact absurd this (by norm_num)

theorem twoF4H_le_centralizer_z :
    twoF4H ≤ Subgroup.centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755))) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hx with hx | hx
  · exact Subgroup.mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hx)
  · have h1 := Subgroup.mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hx)
    calc x * titsZ = ((x * tπ⁻¹) * tπ) * titsZ := by group
      _ = (x * tπ⁻¹) * (tπ * titsZ) := by group
      _ = (x * tπ⁻¹) * (titsZ * tπ) := by rw [tπ_comm_titsZ]
      _ = ((x * tπ⁻¹) * titsZ) * tπ := by group
      _ = (titsZ * (x * tπ⁻¹)) * tπ := by rw [h1]
      _ = titsZ * x := by group

theorem twoF4S_center {x : Equiv.Perm (Fin 1755)} (hx : x ∈ twoF4S)
    (hc : ∀ y ∈ twoF4S, y * x = x * y) : x = 1 ∨ x = titsZ := by
  have hxc : x ∈ Subgroup.centralizer (titsS : Set (Equiv.Perm (Fin 1755))) :=
    Subgroup.mem_centralizer_iff.2 fun s hs => hc s (le_extSub hs)
  rcases hx with hxS | hxS
  · have hmem : x ∈ ((Subgroup.center titsS).map titsS.subtype :
        Set (Equiv.Perm (Fin 1755))) := by
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g.1 g.2)
    rw [titsS_center] at hmem
    exact hmem
  · exfalso
    have h := mul_pi_not_mem_centralizer_S hxS
    rw [inv_mul_cancel_right] at h
    exact h hxc

end CFSG.Quasithin.H13.F431.TwoF4
