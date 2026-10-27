module

public import CFSG.Sporadic.Schreier.Co1SplitLocal

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (rowsMatrix)
open ElemThree Matrix CFSG.Blueprint
open scoped Pointwise

theorem elementary_three_split_local_subgroup :
    (∀ i : Fin 3, ((g i : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      rowsMatrix 24 (Data.liftRows.getD i.val []).toArray) ∧
    (∀ i : Fin 3, g i ∈ Subgroup.normalizer (E : Set GL24)) ∧
    orderOf r = 2 ∧ (∀ x ∈ E, r * x * r⁻¹ = x⁻¹) ∧
    (∃ c : Fin 12 → ZMod 3, ∀ j (e : ZMod 3),
      ((r : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (zM ^ e.val *ᵥ q j) =
        zM ^ (c j + 2 * e).val *ᵥ q j) ∧
    d 0 ∈ E ∧ d 1 ∈ E ∧ d 0 = eProd ![1, 1, 0, 2, 0, 0] ∧ d 1 = eProd ![2, 2, 1, 0, 2, 0] ∧
    ∃ π : A →* GL (Fin 12) (ZMod 3),
      (∀ x : A, ∃ (p : Fin 12 → Fin 12) (u ε : Fin 12 → ZMod 3), (∀ j, ε j ≠ 0) ∧
        ((π x : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) = signedMatrix p ε ∧
        ∀ j (e : ZMod 3), ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (zM ^ e.val *ᵥ q j) =
          zM ^ (u j + ε j * e).val *ᵥ q (p j)) ∧
      (∃ φ : C ≃* Q, ∀ (x : C) (hx : (x : GL24) ∈ A), (φ x : GL (Fin 12) (ZMod 3)) = π ⟨x, hx⟩) ∧
      E ≤ A ∧ C ≤ A ∧ (E.subgroupOf A).Normal ∧ E ⊓ C = ⊥ ∧
      (A : Set GL24) = (E : Set GL24) * (C : Set GL24) ∧
      Nat.card A = 3 ^ 6 * 190080 ∧ Nat.card A = 138568320 ∧
      commutator C = ⊤ ∧
      (∃ ρ : C →* Equiv.Perm (Fin 12),
        ρ.range = NativeSporadic.M12.map (MulAut.conj coordBij).toMonoidHom ∧
        Nat.card ρ.ker = 2 ∧ ρ.ker ≤ Subgroup.center C ∧ ¬ ∃ s : ρ.range →* C, ∀ y, ρ (s y) = y) ∧
      A ≤ GA := by
  have hd : ∀ i, d i ∈ E := fun i => by rw [d_eq]; exact eProd_mem _
  have hr := (msData_spec (A_isMS _ r_mem_A)).2
  rw [msData_r.1, msData_r.2] at hr
  refine ⟨g_eq_lift, g_mem_normalizer, orderOf_eq_prime r_sq r_ne_one, fun x hx => ?_,
    ⟨_, hr⟩, hd 0, hd 1, ?_, ?_, proj, fun x => ?_, ⟨cEquiv, cEquiv_apply⟩, E_le_A, C_le_A,
    E_normal_A, E_inf_C, A_eq_mul, by rw [card_A]; norm_num, card_A, commutator_C,
    ⟨cPerm, cPerm_range, card_ker_cPerm, ker_cPerm_le_center, not_exists_section_C⟩, A_le_GA⟩
  · have h := congrArg Subtype.val
      (r_inv_ker ⟨x, E_le_A hx⟩ (EA_le_ker ((Subgroup.mem_subgroupOf).mpr hx)))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv] at h
    exact h
  · rw [d_eq]
    exact congrArg eProd corrExps_eq.1
  · rw [d_eq]
    exact congrArg eProd corrExps_eq.2
  · obtain ⟨hs, hx⟩ := msData_spec (A_isMS x x.2)
    exact ⟨_, _, _, hs, rfl, hx⟩

end CFSG.Sporadic.Co1Schreier
