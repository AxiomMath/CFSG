module

public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutNatLin
public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutNatFour

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatCore

theorem tvM_sq {F : Type} [Field F] [CharP F 2] {φ v : Fin 3 → F} (h : φ ⬝ᵥ v = 0) :
    NatI.tvM φ v * NatI.tvM φ v = 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  refine NatE.matrix_eq_of_mulVec_aux (fun u => ?_)
  rw [← Matrix.mulVec_mulVec, NatI.tvM_mulVec, NatI.tvM_mulVec, Matrix.one_mulVec]
  rw [dotProduct_add, dotProduct_smul, h, smul_zero, add_zero, add_assoc, ← add_smul]
  have : (φ ⬝ᵥ u + φ ⬝ᵥ u : F) = 0 := by
    calc (φ ⬝ᵥ u + φ ⬝ᵥ u : F) = 2 * (φ ⬝ᵥ u) := by ring
      _ = 0 := by rw [h2, zero_mul]
  rw [this, zero_smul, add_zero]

theorem eq_id_of_ge8 {F : Type} [Field F] [Fintype F] [CharP F 2] (hF : 8 ≤ Fintype.card F)
    {a : (Fin 3 → F) ≃+ (Fin 3 → F)} (ha : ∀ u, a (a u) = u)
    (hnorm : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F,
      ∃ s' : Matrix.SpecialLinearGroup (Fin 3) F,
        ∀ u, a ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ u) = (s' : Matrix (Fin 3) (Fin 3) F) *ᵥ a u)
    (hrank : (Set.range fun u => a u - u).ncard ≤ 4) : ∀ u, a u = u := by
  refine NatB.eq_id_of_lines_fixed a ha (NatB.lines_fixed_of_flag a ?_)
  intro v φ hv hφ hφv
  let s : Matrix.SpecialLinearGroup (Fin 3) F := ⟨NatI.tvM φ v, NatI.det_tvM hφv⟩
  obtain ⟨s', hs'⟩ := hnorm s
  have hsval : (s : Matrix (Fin 3) (Fin 3) F) = NatI.tvM φ v := rfl
  have hs'sq : (s' : Matrix (Fin 3) (Fin 3) F) * (s' : Matrix (Fin 3) (Fin 3) F) = 1 :=
    NatI.sq_eq_one_of_conj ha (tvM_sq hφv) (fun u => by rw [← hsval]; exact hs' u)
  have hs'1 : (s' : Matrix (Fin 3) (Fin 3) F) ≠ 1 :=
    NatI.ne_one_of_conj ha (NatI.tvM_ne_one hφ hv) (fun u => by rw [← hsval]; exact hs' u)
  obtain ⟨v', φ', hv', hφ', hφv', hs'u⟩ := NatI.exists_transvection_of_sq_eq_one hs'sq hs'1
  have hconj : ∀ u, a (u + (φ ⬝ᵥ u) • v) = a u + (φ' ⬝ᵥ a u) • v' := fun u => by
    have h1 := hs' u
    rw [hsval, NatI.tvM_mulVec, hs'u] at h1
    exact h1
  obtain ⟨hl1, -, hk1, -⟩ := NatA.line_image_of_conj ha hv hφ hv' hφ' hφv hφv' hconj
  rcases NatA.parallel_of_ncard_le hF ha hrank hv hφ hv' hφ' hφv hφv' hconj with
    ⟨c0, hc0⟩ | ⟨c0, hc0⟩
  · left
    intro c
    obtain ⟨c', hc'⟩ := hl1 c
    exact ⟨c' * c0, by rw [hc', hc0, smul_smul]⟩
  · right
    intro u hu
    have h1 := hk1 u hu
    rw [hc0, smul_dotProduct, smul_eq_mul] at h1
    have hc0ne : c0 ≠ 0 := by
      rintro rfl
      exact hφ' (by rw [hc0, zero_smul])
    exact (mul_eq_zero.mp h1).resolve_left hc0ne

theorem eq_matrix_of_natural_offender {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
    (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f) {a : (Fin 3 → F) ≃+ (Fin 3 → F)}
    (ha : ∀ u, a (a u) = u)
    (hnorm : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F,
      ∃ s' : Matrix.SpecialLinearGroup (Fin 3) F,
        ∀ u, a ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ u) = (s' : Matrix (Fin 3) (Fin 3) F) *ᵥ a u)
    (hrank : (Set.range fun u => a u - u).ncard ≤ 4) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 3) F,
      ∀ u, a u = (M : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
  rcases Nat.lt_or_ge f 3 with h | h
  · have hf2 : f = 2 := by omega
    subst hf2
    exact NatE.eq_matrix_of_card_four (by rw [hF]; norm_num) ha hnorm hrank
  · refine ⟨1, fun u => ?_⟩
    have h8 : 8 ≤ Fintype.card F := by
      rw [hF]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
    rw [eq_id_of_ge8 h8 ha hnorm hrank u]
    simp

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatCore
