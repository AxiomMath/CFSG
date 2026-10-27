module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofChain

public section

namespace CFSG.StandardType

section End

variable {β : Type*} [DecidableEq β]

theorem chain_end_commute {n : ℕ} (hn : 3 ≤ n) (w : ℕ → β)
    (hw : ∀ c d, c ≤ n → d ≤ n → w c = w d → c = d) {σ : Equiv.Perm β} (hσ : σ.IsSwap)
    (hne : ∀ c, 1 ≤ c → c < n → σ ≠ Equiv.swap (w c) (w (c + 1)))
    (hcomm : ∀ c, 1 ≤ c → c + 2 ≤ n →
      σ * Equiv.swap (w c) (w (c + 1)) = Equiv.swap (w c) (w (c + 1)) * σ)
    (hbr : (σ * Equiv.swap (w (n - 1)) (w n)) ^ 3 = 1) (hloop : σ ≠ Equiv.swap (w 0) (w n)) :
    σ * Equiv.swap (w 0) (w 1) = Equiv.swap (w 0) (w 1) * σ := by
  have hw_ne : ∀ c d, c ≤ n → d ≤ n → c ≠ d → w c ≠ w d :=
    fun c d hc hd hcd h => hcd (hw c d hc hd h)
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have huv : w (n - 1) ≠ w n := by
    have h := hw_ne (n - 1) (n - 1 + 1) (by omega) (by omega) (by omega)
    rwa [hsub] at h
  have hne_nm1 : σ ≠ Equiv.swap (w (n - 1)) (w n) := by
    have h := hne (n - 1) (by omega) (by omega)
    rwa [hsub] at h
  obtain ⟨z, hzu, hzv, hzcase⟩ := swap_share_of_braid huv hσ hne_nm1 hbr
  have hnot1 : σ ≠ Equiv.swap (w (n - 1)) z := by
    intro hcase
    have hsub2 : n - 2 + 1 = n - 1 := by omega
    have hc := hcomm (n - 2) (by omega) (by omega)
    rw [hsub2] at hc
    have hn2 := hne (n - 2) (by omega) (by omega)
    rw [hsub2] at hn2
    have huv2 : w (n - 2) ≠ w (n - 1) :=
      hw_ne (n - 2) (n - 1) (by omega) (by omega) (by omega)
    have hfix := swap_fix_of_commute huv2 hσ hn2 hc
    have hz : z = w (n - 1) := by
      have h := hfix.2
      rw [hcase, Equiv.swap_apply_left] at h
      exact h
    exact hzu hz
  have hσ_eq : σ = Equiv.swap (w n) z := by
    rcases hzcase with h | h
    · exact absurd h hnot1
    · exact h
  have hz0 : z ≠ w 0 := by
    intro hz0
    exact hloop (by rw [hσ_eq, hz0]; exact Equiv.swap_comm _ _)
  have hz1 : z ≠ w 1 := by
    intro hz1
    have hc := hcomm 1 (le_refl 1) (by omega)
    have hn1 := hne 1 (le_refl 1) (by omega)
    have huv1 : w 1 ≠ w 2 := hw_ne 1 2 (by omega) (by omega) (by omega)
    have hfix := swap_fix_of_commute huv1 hσ hn1 hc
    have hw1n : w 1 = w n := by
      have h := hfix.1
      rw [hσ_eq, hz1, Equiv.swap_apply_right] at h
      exact h.symm
    exact hw_ne 1 n (by omega) (le_refl n) (by omega) hw1n
  have hnodup : [w n, z, w 0, w 1].Nodup := by
    have hwnz : w n ≠ z := hzv.symm
    have hwn0 : w n ≠ w 0 := hw_ne n 0 (le_refl n) (by omega) (by omega)
    have hwn1 : w n ≠ w 1 := hw_ne n 1 (le_refl n) (by omega) (by omega)
    have h01 : w 0 ≠ w 1 := hw_ne 0 1 (by omega) (by omega) (by omega)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    tauto
  rw [hσ_eq]
  exact (Equiv.Perm.disjoint_swap_swap hnodup).commute

end End

end CFSG.StandardType
