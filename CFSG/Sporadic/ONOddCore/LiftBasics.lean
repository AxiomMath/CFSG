module

public import CFSG.Sporadic.Schreier.ONR3E
public import CFSG.Sporadic.ONOddCore.QuotBasics

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier

@[expose] def piR :
    onM →* RM := piM.rangeRestrict

theorem piR_val
    (m : onM) : (piR m : Equiv.Perm (Fin 120)) = piM m := rfl

theorem piR_surjective :
    Function.Surjective piR := MonoidHom.rangeRestrict_surjective _

theorem ker_piM :
    piM.ker = onQ.subgroupOf onM := by
  rw [← rhoM_ker]
  ext m
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, piM, MonoidHom.comp_apply]
  exact map_eq_one_iff _ (MulAut.conj onu).injective

theorem ker_piR :
    piR.ker = onQ.subgroupOf onM := by
  rw [← ker_piM]
  ext m
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← piR_val]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

theorem eq_qM_pow_of_piR
    {m : onM} (hm : piR m = 1) : ∃ a < 4, m = qM ^ a := by
  have h : m ∈ piR.ker := hm
  rw [ker_piR, Subgroup.mem_subgroupOf] at h
  rcases q_cases h with h | h | h | h
  · exact ⟨0, by norm_num, Subtype.ext (by rw [h, pow_zero]; rfl)⟩
  · exact ⟨1, by norm_num, Subtype.ext (by rw [h, pow_one]; rfl)⟩
  · exact ⟨2, by norm_num, Subtype.ext (by rw [h, Subgroup.coe_pow]; rfl)⟩
  · exact ⟨3, by norm_num, Subtype.ext (by rw [h, Subgroup.coe_pow]; rfl)⟩

abbrev LM :
    Subgroup onM := onL.subgroupOf onM

theorem LM_characteristic :
    LM.Characteristic := by
  rw [LM, ← commutator_top_M]
  infer_instance

theorem mem_Q_iff
    (m : onM) : m ∈ onQ.subgroupOf onM ↔ m ∈ LM ∧ ∀ n ∈ LM, n * m = m * n := by
  rw [Subgroup.mem_subgroupOf, ← onL_centerIn, CFSG.centerIn, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun n hn => Subtype.ext (h2 n (Subgroup.mem_subgroupOf.1 hn))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun n hn => ?_⟩
    have := h2 ⟨n, onL_le_M hn⟩ (Subgroup.mem_subgroupOf.2 hn)
    exact congrArg Subtype.val this

theorem Q_characteristic :
    (onQ.subgroupOf onM).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ m hm
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mem_Q_iff] at *
  obtain ⟨h1, h2⟩ := hm
  have hc := Subgroup.characteristic_iff_comap_eq.1 LM_characteristic φ
  have hL : ∀ x, x ∈ LM ↔ φ x ∈ LM := fun x => by
    conv_lhs => rw [← hc]
    rfl
  refine ⟨(hL m).1 h1, fun n hn => ?_⟩
  have hn' : φ.symm n ∈ LM := by
    rw [hL]
    simpa using hn
  have := congrArg φ (h2 _ hn')
  simpa using this

theorem map_ker_piR
    (α : MulAut onM) : piR.ker.map (α : onM →* onM) = piR.ker := by
  rw [ker_piR]
  exact Subgroup.characteristic_iff_map_eq.1 Q_characteristic α

@[expose] def quotRM :
    onM ⧸ piR.ker ≃* RM :=
  QuotientGroup.quotientKerEquivOfSurjective piR piR_surjective

@[expose] def descendAut
    (α : MulAut onM) : MulAut RM :=
  (quotRM.symm.trans (QuotientGroup.congr piR.ker piR.ker α (map_ker_piR α))).trans quotRM

theorem descendAut_piR
    (α : MulAut onM) (m : onM) : descendAut α (piR m) = piR (α m) := by
  rw [descendAut, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have e : quotRM.symm (piR m) = (m : onM ⧸ piR.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [e, QuotientGroup.congr_apply]
  rfl

theorem descendAut_mul
    (α β : MulAut onM) : descendAut (α * β) = descendAut α * descendAut β := by
  refine MulEquiv.ext fun r => ?_
  obtain ⟨m, rfl⟩ := piR_surjective r
  rw [MulAut.mul_apply, descendAut_piR, descendAut_piR, descendAut_piR, MulAut.mul_apply]

theorem descendAut_one :
    descendAut 1 = 1 := by
  refine MulEquiv.ext fun r => ?_
  obtain ⟨m, rfl⟩ := piR_surjective r
  rw [descendAut_piR]
  rfl

theorem descendAut_inv
    (α : MulAut onM) : descendAut α⁻¹ = (descendAut α)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← descendAut_mul, inv_mul_cancel, descendAut_one]

theorem descendAut_conj
    (m : onM) : descendAut (MulAut.conj m) = MulAut.conj (piR m) := by
  refine MulEquiv.ext fun r => ?_
  obtain ⟨n, rfl⟩ := piR_surjective r
  rw [descendAut_piR, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

end CFSG.Sporadic.ONOddCore
