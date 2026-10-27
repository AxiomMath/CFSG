module

public import CFSG.CharacterTheory.PSL2Table.Tori

public section

namespace CFSG.Quasithin.F7Two

open CFSG.PSL2Table Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem weyl_conj_unip (t : K) :
    weyl * unip t * weyl⁻¹ =
      SpecialLinearGroup.transvection (Fin.zero_lt_one.ne' : (1 : Fin 2) ≠ 0) (-t) := by
  apply SL_ext <;> simp [mul_apply_SL, Matrix.adjugate_fin_two, SpecialLinearGroup.transvection_coe]

theorem transvection_zero_one (c : K) :
    SpecialLinearGroup.transvection (Fin.zero_lt_one.ne : (0 : Fin 2) ≠ 1) c = unip c := by
  apply SL_ext <;> simp [SpecialLinearGroup.transvection_coe]

theorem mem_unipotent_iff_exists_unip {x : PSL(2, K)} :
    x ∈ unipotent K ↔ ∃ t : K, x = mk (unip t) := by
  constructor
  · rintro ⟨A, ⟨h10, h00, h11⟩, rfl⟩
    refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 1, ?_⟩
    congr 1
    apply SL_ext <;> simp [h10, h00, h11]
  · rintro ⟨t, rfl⟩
    exact mk_unip_mem_unipotent t

theorem unipotent_sup_conj_weyl_eq_top (K : Type) [Field K] :
    unipotent K ⊔ (unipotent K).map (MulAut.conj (splitWeyl K)).toMonoidHom = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨M, rfl⟩ := exists_mk_eq g
  refine SL2.transvection_induction
    (fun A : SL(2, K) => mk A ∈ unipotent K ⊔
      (unipotent K).map (MulAut.conj (splitWeyl K)).toMonoidHom) ?_ ?_ M
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [transvection_zero_one]
      exact Subgroup.mem_sup_left (mk_unip_mem_unipotent c)
    · refine Subgroup.mem_sup_right ⟨mk (unip (-c)), mk_unip_mem_unipotent (-c), ?_⟩
      have h : weyl * unip (-c) * weyl⁻¹ = SpecialLinearGroup.transvection hij c := by
        rw [weyl_conj_unip, neg_neg]
      change splitWeyl K * mk (unip (-c)) * (splitWeyl K)⁻¹ = _
      rw [splitWeyl, mk_conj, h]
    · exact absurd rfl hij
  · intro A B hA hB
    rw [map_mul]
    exact Subgroup.mul_mem _ hA hB

theorem odd_natCard_unipotent [Finite K] (h2 : (2 : K) ≠ 0) : Odd (Nat.card (unipotent K)) := by
  have := Fintype.ofFinite K
  have hc : ringChar K ≠ 2 := by
    intro h
    apply h2
    have h0 : ((2 : ℕ) : K) = 0 := (ringChar.spec K 2).mpr (by rw [h])
    simpa using h0
  rw [card_unipotent h2, ← Nat.card_eq_fintype_card]
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hc)

theorem psl2_nonabelian : ∃ x y : PSL(2, K), x * y ≠ y * x := by
  refine ⟨mk (unip 1), splitWeyl K, fun h => ?_⟩
  rw [splitWeyl, ← map_mul, ← map_mul, mk_eq_mk_iff] at h
  rcases h with h | h
  · have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [mul_apply_SL] at this
  · have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [mul_apply_SL, neg_apply_SL] at this

end CFSG.Quasithin.F7Two
