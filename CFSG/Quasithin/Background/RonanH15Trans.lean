module

public import CFSG.Quasithin.Background.HMathieuStd

public section

namespace CFSG.Quasithin.RonanH15

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

private theorem exists_fourth_point (a b j : Fin 24) :
    ∃ z : Fin 24, z ≠ a ∧ z ≠ b ∧ z ≠ j := by
  by_contra hc
  push Not at hc
  have hall : ∀ z : Fin 24, z ∈ ({a, b, j} : Finset (Fin 24)) := fun z => by
    by_cases h1 : z = a
    · simp [h1]
    · by_cases h2 : z = b
      · simp [h2]
      · simp [hc z h1 h2]
  have hcard : (Finset.univ : Finset (Fin 24)).card ≤ ({a, b, j} : Finset (Fin 24)).card :=
    Finset.card_le_card fun z _ => hall z
  have := hcard.trans Finset.card_le_three
  simp at this

theorem exists_maps_three {a b j : Fin 24} (hab : a ≠ b)
    (hja : j ≠ a) (hjb : j ≠ b) : ∃ τ ∈ AutPerm, τ 0 = a ∧ τ 1 = b ∧ τ 2 = j := by
  obtain ⟨z, hza, hzb, hzj⟩ := exists_fourth_point a b j
  obtain ⟨τ, hτ, h0, h1, h2, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_four a b j z hab
    (Ne.symm hja) (Ne.symm hza) (Ne.symm hjb) (Ne.symm hzb) (Ne.symm hzj)
  exact ⟨τ, hτ, h0, h1, h2⟩

theorem exists_mem_stab_maps {a j j' : Fin 24} (hja : j ≠ a)
    (hj'a : j' ≠ a) : ∃ g ∈ AutPerm ⊓ stab a, g j = j' := by
  obtain ⟨p, hp, p0, p1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a j (Ne.symm hja)
  obtain ⟨q, hq, q0, q1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a j' (Ne.symm hj'a)
  have hpa : p⁻¹ a = 0 := by rw [← p0]; exact Equiv.symm_apply_apply p 0
  have hpj : p⁻¹ j = 1 := by rw [← p1]; exact Equiv.symm_apply_apply p 1
  refine ⟨q * p⁻¹, Subgroup.mem_inf.2 ⟨AutPerm.mul_mem hq (AutPerm.inv_mem hp), ?_⟩, ?_⟩
  · rw [mem_stab_iff, Equiv.Perm.mul_apply, hpa, q0]
  · rw [Equiv.Perm.mul_apply, hpj, q1]

theorem exists_mem_stab_stab_maps {a b j j' : Fin 24}
    (hab : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b) (hj'a : j' ≠ a) (hj'b : j' ≠ b) :
    ∃ g ∈ AutPerm ⊓ stab a ⊓ stab b, g j = j' := by
  obtain ⟨p, hp, p0, p1, p2⟩ := exists_maps_three hab hja hjb
  obtain ⟨q, hq, q0, q1, q2⟩ := exists_maps_three hab hj'a hj'b
  have hpa : p⁻¹ a = 0 := by rw [← p0]; exact Equiv.symm_apply_apply p 0
  have hpb : p⁻¹ b = 1 := by rw [← p1]; exact Equiv.symm_apply_apply p 1
  have hpj : p⁻¹ j = 2 := by rw [← p2]; exact Equiv.symm_apply_apply p 2
  refine ⟨q * p⁻¹, Subgroup.mem_inf.2
    ⟨Subgroup.mem_inf.2 ⟨AutPerm.mul_mem hq (AutPerm.inv_mem hp), ?_⟩, ?_⟩, ?_⟩
  · rw [mem_stab_iff, Equiv.Perm.mul_apply, hpa, q0]
  · rw [mem_stab_iff, Equiv.Perm.mul_apply, hpb, q1]
  · rw [Equiv.Perm.mul_apply, hpj, q2]

end CFSG.Quasithin.RonanH15
