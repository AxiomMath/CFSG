module

public import CFSG.Quasithin.Background.B3Chk
public import CFSG.Quasithin.Background.B3Rank

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

theorem cj_one (S : Subgroup (Gp n)) : cj 1 S = S := by
  ext x
  simp [mem_cj]

theorem qRow_spec (hn : 5 ≤ n) (k : Mod) {snum sden : ℕ} {C : List Tab} (hC : subOK n C = true)
    (h : qRow n k snum sden C = true) :
    rAV ((subOf n C).map (Mod.act n k)) = ((rkPair n k C).2 : ℚ) / (rkPair n k C).1 ∧
      0 < (rkPair n k C).1 ∧ snum * (rkPair n k C).1 ≤ sden * (rkPair n k C).2 := by
  simp only [qRow, Bool.and_eq_true, decide_eq_true_eq, rankOK, beq_iff_eq] at h
  obtain ⟨⟨⟨hlen, hcnt⟩, hpos⟩, hle⟩ := h
  exact ⟨(rank_data hn k hC hlen hcnt).2.2, hpos, hle⟩

theorem suppCardT_tab (σ : Gp n) : suppCardT (tab σ) = σ.support.card := by
  unfold suppCardT
  rw [length_tab, List.countP_eq_length_filter, length_filter_range]
  have h1 : σ.support.card = ∑ i : Fin n, if σ i ≠ i then 1 else 0 := by
    unfold Equiv.Perm.support
    rw [Finset.card_filter]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => if ((tab σ).getD i 0 != i) = true then 1 else 0) n |>.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_tab]
  simp [bne_iff_ne, Fin.val_ne_iff]

end CFSG.Quasithin.B3
