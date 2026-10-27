module

public import Certificates.Data.CFSGNative.ExcCensus.Core
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

variable {T : Chk.Tabs} {r : ℕ} {w : Chk.LinW}

@[expose] def coxOf (tc n : ℕ) : CoxeterMatrix (Fin (Chk.rkN tc n)) :=
  match tc with
  | 0 => CoxeterMatrix.A n
  | 1 => CoxeterMatrix.B n
  | 2 => CoxeterMatrix.B n
  | 3 => ggCoxeterMatrixD n
  | 4 => CoxeterMatrix.E₆
  | 5 => CoxeterMatrix.E₇
  | 6 => CoxeterMatrix.E₈
  | 7 => CoxeterMatrix.F₄
  | 8 => CoxeterMatrix.G₂
  | _ => CoxeterMatrix.A _

@[expose] def cartanOf (tc n : ℕ) : Matrix (Fin (Chk.rkN tc n)) (Fin (Chk.rkN tc n)) ℤ :=
  fun i j => Chk.cartanN tc n i j

theorem ggIsWeylMatrix_coxOf {tc n : ℕ} (h : Chk.validN tc n = true) :
    GGIsWeylMatrix (coxOf tc n) := by
  rcases tc with _ | _ | _ | _ | _ | _ | _ | _ | _ | tc
  · have hn : 1 ≤ n := by simpa [Chk.validN] using h
    exact Or.inl ⟨n, Equiv.refl _, hn, Or.inl rfl⟩
  · have hn : 2 ≤ n := by simpa [Chk.validN] using h
    exact Or.inl ⟨n, Equiv.refl _, by omega, Or.inr (Or.inl ⟨hn, rfl⟩)⟩
  · have hn : 3 ≤ n := by simpa [Chk.validN] using h
    exact Or.inl ⟨n, Equiv.refl _, by omega, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩
  · have hn : 4 ≤ n := by simpa [Chk.validN] using h
    exact Or.inl ⟨n, Equiv.refl _, by omega, Or.inr (Or.inr ⟨hn, rfl⟩)⟩
  · exact Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Equiv.refl _, rfl⟩))))
  · simp [Chk.validN] at h

private theorem cartanOf_eq_A (n : ℕ) : cartanOf 0 n = CartanMatrix.A n := by
  ext i j
  have h : Chk.rkN 0 n = n := rfl
  show Chk.cartanN 0 n (i : ℕ) (j : ℕ) =
    CartanMatrix.A n (Fin.cast h i) (Fin.cast h j)
  simp only [Chk.cartanN, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_cast]

private theorem cartanOf_eq_B (n : ℕ) : cartanOf 1 n = CartanMatrix.B n := by
  ext i j
  have h : Chk.rkN 1 n = n := rfl
  show Chk.cartanN 1 n (i : ℕ) (j : ℕ) =
    CartanMatrix.B n (Fin.cast h i) (Fin.cast h j)
  simp only [Chk.cartanN, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_cast]

private theorem cartanOf_eq_C (n : ℕ) : cartanOf 2 n = CartanMatrix.C n := by
  ext i j
  have h : Chk.rkN 2 n = n := rfl
  show Chk.cartanN 2 n (i : ℕ) (j : ℕ) =
    CartanMatrix.C n (Fin.cast h i) (Fin.cast h j)
  simp only [Chk.cartanN, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_cast]

private theorem cartanOf_eq_D (n : ℕ) : cartanOf 3 n = CartanMatrix.D n := by
  ext i j
  have h : Chk.rkN 3 n = n := rfl
  show Chk.cartanN 3 n (i : ℕ) (j : ℕ) =
    CartanMatrix.D n (Fin.cast h i) (Fin.cast h j)
  simp only [Chk.cartanN, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_cast]

private theorem cartanOf_eq_E6 (n : ℕ) : cartanOf 4 n = CartanMatrix.E 6 := by
  ext i j
  have h : Chk.rkN 4 n = 6 := rfl
  show Chk.cartanN 4 n (i : ℕ) (j : ℕ) =
    CartanMatrix.E 6 (Fin.cast h i) (Fin.cast h j)
  simp only [Chk.cartanN, CartanMatrix.E, Matrix.of_apply, Fin.ext_iff, Fin.val_cast]

private theorem cartanOf_eq_E7 (n : ℕ) : cartanOf 5 n = CartanMatrix.E 7 := by
  ext i j
  have h : Chk.rkN 5 n = 7 := rfl
  show Chk.cartanN 5 n (i : ℕ) (j : ℕ) =
    CartanMatrix.E 7 (Fin.cast h i) (Fin.cast h j)
  simp only [Chk.cartanN, CartanMatrix.E, Matrix.of_apply, Fin.ext_iff, Fin.val_cast]

private theorem cartanOf_eq_E8 (n : ℕ) : cartanOf 6 n = CartanMatrix.E 8 := by
  ext i j
  have h : Chk.rkN 6 n = 8 := rfl
  show Chk.cartanN 6 n (i : ℕ) (j : ℕ) =
    CartanMatrix.E 8 (Fin.cast h i) (Fin.cast h j)
  simp only [Chk.cartanN, CartanMatrix.E, Matrix.of_apply, Fin.ext_iff, Fin.val_cast]

private theorem cartanOf_eq_F4 (n : ℕ) : cartanOf 7 n = CartanMatrix.F₄ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem cartanOf_eq_G2 (n : ℕ) : cartanOf 8 n = CartanMatrix.G₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem ggIntCartan_coxOf {tc n : ℕ} (h : Chk.validN tc n = true) :
    GGIntCartan (coxOf tc n) (cartanOf tc n) := by
  rcases tc with _ | _ | _ | _ | _ | _ | _ | _ | _ | tc
  · rw [cartanOf_eq_A]; exact ggIntCartan_A n
  · rw [cartanOf_eq_B]; exact ggIntCartan_B n
  · rw [cartanOf_eq_C]; exact ggIntCartan_C n
  · rw [cartanOf_eq_D]; exact ggIntCartan_D n
  · rw [cartanOf_eq_E6]; exact ggIntCartan_E₆
  · rw [cartanOf_eq_E7]; exact ggIntCartan_E₇
  · rw [cartanOf_eq_E8]; exact ggIntCartan_E₈
  · rw [cartanOf_eq_F4]; exact ggIntCartan_F₄
  · rw [cartanOf_eq_G2]; exact ggIntCartan_G₂
  · simp [Chk.validN] at h

theorem cartanOf_D (n : ℕ) (i j : Fin n) : cartanOf 3 n i j = CartanMatrix.D n i j := by
  simp only [cartanOf, Chk.cartanN, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]

theorem cartanOf_E (n : ℕ) (i j : Fin 6) : cartanOf 4 n i j = CartanMatrix.E 6 i j := by
  simp only [cartanOf, Chk.cartanN, CartanMatrix.E, Matrix.of_apply, Fin.ext_iff]

theorem typeOK_validN (h : Chk.typeOK T r w = true) : Chk.validN w.tc w.n = true := by
  simp only [Chk.typeOK, Bool.and_eq_true] at h
  exact h.1.1.1

theorem typeOK_node_lt (h : Chk.typeOK T r w = true) (i : Fin (Chk.rkN w.tc w.n)) :
    Chk.nodeN w i < r := by
  simp only [Chk.typeOK, Bool.and_eq_true, beq_iff_eq] at h
  have hlen : w.nodes.length = Chk.rkN w.tc w.n := h.1.1.2
  have hall : ∀ t ∈ w.nodes, t < r := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using h.1.2
  have hi : (i : ℕ) < w.nodes.length := by rw [hlen]; exact i.isLt
  simp only [Chk.nodeN, List.getD_eq_getElem w.nodes 0 hi]
  exact hall _ (List.getElem_mem hi)

theorem linOK_typeOK (h : Chk.linOK T r w = true) : Chk.typeOK T r w = true := by
  simp only [Chk.linOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
  exact h.1.1.1.1

theorem linOK_a_lt (h : Chk.linOK T r w = true) : w.a < Chk.rkN w.tc w.n := by
  simp only [Chk.linOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
  exact h.1.1.1.2

theorem linOK_b_lt (h : Chk.linOK T r w = true) : w.b < Chk.rkN w.tc w.n := by
  simp only [Chk.linOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
  exact h.1.1.2

theorem linOK_a_ne_b (h : Chk.linOK T r w = true) : w.a ≠ w.b := by
  simp only [Chk.linOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
  exact h.1.2

theorem leafN_existsUnique {tc n b : ℕ} (hb : b < Chk.rkN tc n) (h : Chk.leafN tc n b = true) :
    ∃! c : Fin (Chk.rkN tc n), c ≠ ⟨b, hb⟩ ∧ cartanOf tc n ⟨b, hb⟩ c ≠ 0 := by
  simp only [Chk.leafN, beq_iff_eq] at h
  obtain ⟨c₀, hc₀⟩ := List.length_eq_one_iff.mp h
  have hmem : c₀ ∈ (List.range (Chk.rkN tc n)).filter
      (fun c => c != b && Chk.cartanN tc n b c != 0) := by
    rw [hc₀]; exact List.mem_singleton_self _
  rw [List.mem_filter] at hmem
  obtain ⟨hrange, hprop⟩ := hmem
  simp only [Bool.and_eq_true, bne_iff_ne] at hprop
  obtain ⟨hne, hcar⟩ := hprop
  have hlt : c₀ < Chk.rkN tc n := List.mem_range.mp hrange
  refine ⟨⟨c₀, hlt⟩, ⟨?_, ?_⟩, ?_⟩
  · intro heq
    exact hne (congrArg Fin.val heq)
  · simpa only [cartanOf] using hcar
  · intro c hc
    obtain ⟨hcne, hccar⟩ := hc
    have hmemc : (c : ℕ) ∈ (List.range (Chk.rkN tc n)).filter
        (fun c => c != b && Chk.cartanN tc n b c != 0) := by
      rw [List.mem_filter]
      refine ⟨List.mem_range.mpr c.isLt, ?_⟩
      simp only [Bool.and_eq_true, bne_iff_ne]
      exact ⟨fun hcb => hcne (Fin.ext hcb), by simpa only [cartanOf] using hccar⟩
    rw [hc₀] at hmemc
    simpa [Fin.ext_iff] using hmemc

theorem linOK_a_leaf (h : Chk.linOK T r w = true) :
    ∃! c : Fin (Chk.rkN w.tc w.n),
      c ≠ ⟨w.a, linOK_a_lt h⟩ ∧ cartanOf w.tc w.n ⟨w.a, linOK_a_lt h⟩ c ≠ 0 := by
  have h' := h
  simp only [Chk.linOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h'
  exact leafN_existsUnique (linOK_a_lt h) h'.2

theorem nbrOK_linOK {m : Fin 6} {cz k : ℕ} {L : List (ℕ × ℕ)} {B : Array (Array ℤ)}
    (h : Chk.nbrOK T m cz k w L B = true) : Chk.linOK T (nroots m) w = true := by
  simp only [Chk.nbrOK, Bool.and_eq_true] at h
  exact h.1.1.1

theorem ambOK_linOK {m : Fin 6} {cv cz ℓ k : ℕ} {W : Chk.AmbW}
    (h : Chk.ambOK T m cv cz ℓ k W = true) : Chk.linOK T (nroots m) W.w = true := by
  simp only [Chk.ambOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
