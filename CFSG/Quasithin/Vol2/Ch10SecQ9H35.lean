module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H21
public import CFSG.Quasithin.Vol2.Ch10SecQ9H28

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

@[expose] def utSL (B : Matrix (Fin m) (Fin k) (ZMod 2)) :
    Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2) :=
  ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 B 0 1), by
    rw [det_reindex_self, det_fromBlocks_zero₂₁, det_one, det_one, one_mul]⟩

variable (B : Matrix (Fin m) (Fin k) (ZMod 2))

theorem utSL_cc (a c : Fin m) :
    (utSL B : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) (Fin.castAdd k a) (Fin.castAdd k c) =
      (1 : Matrix (Fin m) (Fin m) (ZMod 2)) a c := by
  simp [utSL, reindex_apply]

theorem utSL_cn (a : Fin m) (d : Fin k) :
    (utSL B : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) (Fin.castAdd k a) (Fin.natAdd m d) =
      B a d := by
  simp [utSL, reindex_apply]

theorem utSL_nc (b : Fin k) (c : Fin m) :
    (utSL B : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) (Fin.natAdd m b) (Fin.castAdd k c) =
      0 := by
  simp [utSL, reindex_apply]

theorem utSL_nn (b d : Fin k) :
    (utSL B : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) (Fin.natAdd m b) (Fin.natAdd m d) =
      (1 : Matrix (Fin k) (Fin k) (ZMod 2)) b d := by
  simp [utSL, reindex_apply]

theorem utSL_mem_uniSL : utSL B ∈ uniSL (m + k) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;>
      rcases fin_add_cases j with ⟨c, rfl⟩ | ⟨d, rfl⟩
    · rw [utSL_cc, Matrix.one_apply_ne]
      intro h
      rw [h] at hij
      exact lt_irrefl _ hij
    · have h : (Fin.natAdd m d : ℕ) < Fin.castAdd k a := hij
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h
      omega
    · exact utSL_nc B b c
    · rw [utSL_nn, Matrix.one_apply_ne]
      intro h
      rw [h] at hij
      exact lt_irrefl _ hij
  · rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [utSL_cc, Matrix.one_apply_eq]
    · rw [utSL_nn, Matrix.one_apply_eq]

theorem utSL_smul (v : Fin (m + k) → ZMod 2) :
    utSL B • v = v + Fin.append (B *ᵥ fun j => v (Fin.natAdd m j)) 0 := by
  rw [smul_eq_mulVec']
  funext i
  rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · simp only [mulVec, dotProduct, Fin.sum_univ_add, utSL_cc, utSL_cn, Pi.add_apply,
      Fin.append_left]
    congr 1
    simp [Matrix.one_apply]
  · simp only [mulVec, dotProduct, Fin.sum_univ_add, utSL_nc, utSL_nn, Pi.add_apply,
      Fin.append_right, zero_mul, Finset.sum_const_zero, zero_add, Pi.zero_apply, add_zero]
    simp [Matrix.one_apply]

theorem utSL_mul_self : utSL B * utSL B = 1 := by
  apply ext_mulVec
  intro v
  rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← smul_eq_mulVec', ← smul_eq_mulVec',
    utSL_smul, utSL_smul, Matrix.SpecialLinearGroup.coe_one, one_mulVec]
  have hb : (fun j => (v + Fin.append (B *ᵥ fun j => v (Fin.natAdd m j)) 0 :
      Fin (m + k) → ZMod 2) (Fin.natAdd m j)) = fun j => v (Fin.natAdd m j) := by
    funext j
    simp
  rw [hb, add_assoc, add_self_vec, add_zero]

theorem smul_append_zero {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hg : PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2))) (w : Fin m → ZMod 2) :
    g • (Fin.append w 0 : Fin (m + k) → ZMod 2) =
      Fin.append (topB (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) *ᵥ w) 0 := by
  have hw : (Fin.append w 0 : Fin (m + k) → ZMod 2) ∈ stdE (m + k) m := by
    intro i hi
    obtain ⟨b, rfl⟩ : ∃ b : Fin k, i = Fin.natAdd m b :=
      ⟨⟨(i : ℕ) - m, by omega⟩, Fin.ext (by simp; omega)⟩
    simp
  funext i
  rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [top_smul_of_mem hw, Fin.append_left]
    congr 2
    funext j
    simp
  · rw [bot_smul hg, Fin.append_right]
    have h0 : (fun j : Fin k => (Fin.append w 0 : Fin (m + k) → ZMod 2) (Fin.natAdd m j)) = 0 := by
      funext j
      simp
    rw [h0, mulVec_zero]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
