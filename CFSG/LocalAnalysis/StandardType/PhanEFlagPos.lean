module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagAdapt

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n : ℕ}

theorem hasPos_of_isAdapted {b : Fin n → (Fin n → K)} {σ : Equiv.Perm (Fin n)}
    {E F : FlagK K n} (h : IsAdapted b σ E F) : HasPos E F σ := by
  obtain ⟨hb, hE, hF⟩ := h
  intro i j hi hj
  unfold rk permRk
  rw [hE i hi, hF j hj]
  rw [show {k : Fin n | k.val < i} =
      ↑(Finset.univ.filter fun k : Fin n => k.val < i) by ext k; simp,
    show {k : Fin n | (σ k).val < j} =
      ↑(Finset.univ.filter fun k : Fin n => (σ k).val < j) by ext k; simp]
  rw [q2cFP_finrank_span_inter b hb]
  rw [← Finset.filter_and]

private lemma q2cFP_permRk_succ (σ : Equiv.Perm (Fin n)) (k : Fin n) (j : ℕ) :
    permRk σ (k.val + 1) j = permRk σ k.val j + if (σ k).val < j then 1 else 0 := by
  classical
  unfold permRk
  by_cases h : (σ k).val < j
  · rw [if_pos h]
    rw [show (Finset.univ.filter fun a : Fin n => a.val < k.val + 1 ∧ (σ a).val < j) =
        insert k (Finset.univ.filter fun a : Fin n => a.val < k.val ∧ (σ a).val < j) by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases ha : a = k
      · subst ha
        simp [h]
      · have hv : a.val ≠ k.val := fun hv => ha (Fin.ext hv)
        have hlt : a.val < k.val + 1 ↔ a.val < k.val := by omega
        simp [ha, hlt]]
    rw [Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h]
    rw [show (Finset.univ.filter fun a : Fin n => a.val < k.val + 1 ∧ (σ a).val < j) =
        (Finset.univ.filter fun a : Fin n => a.val < k.val ∧ (σ a).val < j) by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases ha : a = k
      · subst ha
        simp [h]
      · have hv : a.val ≠ k.val := fun hv => ha (Fin.ext hv)
        have hlt : a.val < k.val + 1 ↔ a.val < k.val := by omega
        simp [ha, hlt]]
    omega

theorem hasPos_unique {E F : FlagK K n} {σ τ : Equiv.Perm (Fin n)} (hσ : HasPos E F σ)
    (hτ : HasPos E F τ) : σ = τ := by
  have hperm : ∀ i j : ℕ, i ≤ n → j ≤ n → permRk σ i j = permRk τ i j := by
    intro i j hi hj
    rw [← hσ i j hi hj, hτ i j hi hj]
  apply Equiv.ext
  intro k
  apply Fin.ext
  have hlt1 : ¬ (σ k).val < (τ k).val := by
    intro h
    have hk := hperm (k.val + 1) ((τ k).val) (by omega) (by omega)
    have hk0 := hperm k.val ((τ k).val) (by omega) (by omega)
    rw [q2cFP_permRk_succ σ k ((τ k).val),
      q2cFP_permRk_succ τ k ((τ k).val), hk0,
      if_pos h, if_neg (lt_irrefl _)] at hk
    omega
  have hlt2 : ¬ (τ k).val < (σ k).val := by
    intro h
    have hk := hperm (k.val + 1) ((σ k).val) (by omega) (by omega)
    have hk0 := hperm k.val ((σ k).val) (by omega) (by omega)
    rw [q2cFP_permRk_succ σ k ((σ k).val),
      q2cFP_permRk_succ τ k ((σ k).val), hk0,
      if_neg (lt_irrefl _), if_pos h] at hk
    omega
  omega

theorem exists_hasPos (E F : FlagK K n) : ∃ σ, HasPos E F σ := by
  obtain ⟨b, σ, h⟩ := exists_adapted E F
  exact ⟨σ, hasPos_of_isAdapted h⟩

@[expose] noncomputable def relPos (E F : FlagK K n) : Equiv.Perm (Fin n) :=
  Classical.choose (exists_hasPos E F)

theorem hasPos_relPos (E F : FlagK K n) : HasPos E F (relPos E F) :=
  Classical.choose_spec (exists_hasPos E F)

theorem hasPos_iff {E F : FlagK K n} {σ : Equiv.Perm (Fin n)} :
    HasPos E F σ ↔ relPos E F = σ :=
  ⟨fun h => hasPos_unique (hasPos_relPos E F) h, fun h => h ▸ hasPos_relPos E F⟩

private lemma q2cFP_permRk_inv (σ : Equiv.Perm (Fin n)) (i j : ℕ) :
    permRk σ⁻¹ j i = permRk σ i j := by
  unfold permRk
  apply Finset.card_bij (fun k _ => σ⁻¹ k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨by simpa using hk.2, by simpa using hk.1⟩
  · intro a _ b _ hab
    exact σ⁻¹.injective hab
  · intro l hl
    refine ⟨σ l, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact ⟨by simpa using hl.2, by simpa using hl.1⟩

theorem relPos_symm (E F : FlagK K n) : relPos F E = (relPos E F)⁻¹ := by
  rw [← hasPos_iff]
  intro i j hi hj
  unfold rk
  rw [inf_comm]
  have hpos := hasPos_relPos E F j i hj hi
  unfold rk at hpos
  rw [hpos]
  exact (q2cFP_permRk_inv (relPos E F) j i).symm

private lemma q2cFP_card_filter_fin_lt {m : ℕ} (hm : m ≤ n) :
    (Finset.univ.filter fun k : Fin n => k.val < m).card = m := by
  have himage : (Finset.univ.filter fun k : Fin n => k.val < m) =
      Finset.univ.image (fun r : Fin m => (⟨r.val, lt_of_lt_of_le r.isLt hm⟩ : Fin n)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hk
      exact ⟨⟨k.val, hk⟩, rfl⟩
    · rintro ⟨r, -, rfl⟩
      exact r.isLt
  rw [himage, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Fin.ext (by simpa using congrArg Fin.val h)

private lemma q2cFP_permRk_one (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    permRk (1 : Equiv.Perm (Fin n)) i j = min i j := by
  unfold permRk
  rw [show (Finset.univ.filter fun k : Fin n => k.val < i ∧
      ((1 : Equiv.Perm (Fin n)) k).val < j) =
      (Finset.univ.filter fun k : Fin n => k.val < min i j) by
    apply Finset.filter_congr
    intro k _
    simp only [Equiv.Perm.one_apply]
    omega]
  exact q2cFP_card_filter_fin_lt (by omega : min i j ≤ n)

theorem relPos_self (E : FlagK K n) : relPos E E = 1 := by
  rw [← hasPos_iff]
  intro i j hi hj
  unfold rk
  have hmin : E.E i ⊓ E.E j = E.E (min i j) := by
    rcases le_total i j with h | h
    · rw [min_eq_left h, inf_eq_left.mpr (E.mono h)]
    · rw [min_eq_right h, inf_eq_right.mpr (E.mono h)]
  rw [hmin, E.dim (min i j) (le_trans (min_le_left i j) hi),
    q2cFP_permRk_one i j hi hj]

theorem relPos_eq_one_iff (E F : FlagK K n) : relPos E F = 1 ↔ E = F := by
  constructor
  · intro h
    have hpos : HasPos E F 1 := hasPos_iff.mpr h
    apply FlagK.ext
    intro i
    by_cases hi : i ≤ n
    · have hii := hpos i i hi hi
      unfold rk at hii
      have hperm : permRk (1 : Equiv.Perm (Fin n)) i i = i := by
        rw [q2cFP_permRk_one i i hi hi, min_self]
      rw [hperm] at hii
      have hEF : E.E i ⊓ F.E i = E.E i := by
        apply Submodule.eq_of_le_of_finrank_eq inf_le_left
        rw [hii, E.dim i hi]
      have hle : E.E i ≤ F.E i := by
        rw [← hEF]
        exact inf_le_right
      exact Submodule.eq_of_le_of_finrank_eq hle (by rw [E.dim i hi, F.dim i hi])
    · have hni : n ≤ i := by omega
      rw [E.top i hni, F.top i hni]
  · rintro rfl
    exact relPos_self E

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
