module

public import CFSG.Quasithin.AppendixH.Common.OctadFlag

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

theorem exists_octad_enum {O : Finset (Fin 24)} {a b : Fin 24}
    (hO : IsOctad O) (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b) :
    ∃ o : Fin 8 → Fin 24, Function.Injective o ∧ (∀ x, x ∈ O ↔ ∃ p, o p = x) ∧ o 0 = a ∧
      o 1 = b := by
  have h8 : 8 ≤ 24 := by norm_num
  obtain ⟨τ, _hτM, hτO, hτ0, hτ1⟩ := exists_flag_pair hO ha hb hab
  let o : Fin 8 → Fin 24 := fun p => τ (Fin.castLE h8 p)
  refine ⟨o, ?_, ?_, ?_, ?_⟩
  · intro p q hpq
    exact Fin.castLE_injective h8 (τ.injective hpq)
  · intro x
    constructor
    · intro hx
      have hx' : x ∈ octad0.map τ.toEmbedding := by
        rw [← smul_finset_eq_map, hτO]; exact hx
      rw [Finset.mem_map_equiv, mem_octad0_iff] at hx'
      refine ⟨⟨(τ.symm x).val, hx'⟩, ?_⟩
      change τ (Fin.castLE h8 ⟨(τ.symm x).val, hx'⟩) = x
      rw [show Fin.castLE h8 ⟨(τ.symm x).val, hx'⟩ = τ.symm x from Fin.ext rfl]
      exact Equiv.apply_symm_apply τ x
    · rintro ⟨p, rfl⟩
      show τ (Fin.castLE h8 p) ∈ O
      rw [← hτO, smul_finset_eq_map, Finset.mem_map_equiv, Equiv.symm_apply_apply,
        mem_octad0_iff]
      exact p.isLt
  · change τ (Fin.castLE h8 (0 : Fin 8)) = a
    rw [show Fin.castLE h8 (0 : Fin 8) = (0 : Fin 24) from Fin.ext rfl, hτ0]
  · change τ (Fin.castLE h8 (1 : Fin 8)) = b
    rw [show Fin.castLE h8 (1 : Fin 8) = (1 : Fin 24) from Fin.ext rfl, hτ1]

end CFSG.ASVolI.AppH
