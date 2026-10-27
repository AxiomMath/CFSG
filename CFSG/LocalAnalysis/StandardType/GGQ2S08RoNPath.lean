module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegFramePath
public import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.StandardType

theorem ggQ2s08rN_path {n : ℕ} {τ : Fin n → Equiv.Perm (Fin (n + 1))} (hswap : ∀ i, (τ i).IsSwap)
    (hadj : ∀ i j : Fin n, (i : ℕ) + 1 = j → τ i * τ j ≠ τ j * τ i)
    (hfar : ∀ i j : Fin n, i ≠ j → (i : ℕ) + 1 ≠ j → (j : ℕ) + 1 ≠ i →
      τ i * τ j = τ j * τ i ∧ τ i ≠ τ j) :
    ∃ a : Fin (n + 1) ≃ Fin (n + 1), ∀ i : Fin n, τ i = Equiv.swap (a i.castSucc) (a i.succ) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Equiv.refl (Fin 1), fun i => i.elim0⟩
  · have hn1 : 1 ≤ n := by omega
    let t : ℕ → Equiv.Perm (Fin (n + 1)) := fun i => if h : i < n then τ ⟨i, h⟩ else 1
    have ht : ∀ i (h : i < n), t i = τ ⟨i, h⟩ := fun i h => by simp [t, h]
    have hswap' : ∀ i < n, (t i).IsSwap := by
      intro i hi
      rw [ht i hi]
      exact hswap ⟨i, hi⟩
    have hadj' : ∀ i, i + 1 < n → ¬ Commute (t i) (t (i + 1)) := by
      intro i hi
      rw [ht i (by omega), ht (i + 1) hi]
      intro hc
      exact hadj ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp) ((commute_iff_eq _ _).mp hc)
    have hfar' : ∀ i j, i + 2 ≤ j → j < n → Commute (t i) (t j) ∧ t i ≠ t j := by
      intro i j hij hj
      have hi : i < n := by omega
      rw [ht i hi, ht j hj]
      have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
        intro h
        have hv : i = j := by simpa using congrArg Fin.val h
        omega
      have hne1 : (i : ℕ) + 1 ≠ j := by omega
      have hne2 : (j : ℕ) + 1 ≠ i := by omega
      obtain ⟨hc, hne'⟩ := hfar ⟨i, hi⟩ ⟨j, hj⟩ hne hne1 hne2
      exact ⟨(commute_iff_eq _ _).mpr hc, hne'⟩
    obtain ⟨p, hpdist, hpt⟩ :=
      CFSG.StandardType.QTwo.qTwoDegFrame_path_labelling hn1 t hswap' hadj' hfar'
    let f : Fin (n + 1) → Fin (n + 1) := fun i => p i.val
    have hf : Function.Injective f := by
      intro i j hij
      have hij' : p i.val = p j.val := by simpa [f] using hij
      exact Fin.ext (hpdist i.val (by omega) j.val (by omega) hij')
    let a : Fin (n + 1) ≃ Fin (n + 1) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    refine ⟨a, ?_⟩
    intro i
    have hi : i.val < n := i.isLt
    have h := hpt i.val hi
    rw [ht i.val hi] at h
    rw [h]
    rfl

end CFSG.StandardType

end
