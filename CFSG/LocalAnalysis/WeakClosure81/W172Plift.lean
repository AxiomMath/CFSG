module

public import CFSG.LocalAnalysis.WeakClosure81.W172PliftEig
public import CFSG.LocalAnalysis.WeakClosure81.W172PliftRank
public import CFSG.LocalAnalysis.WeakClosure81.W172Two27

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem w172_plift {p : ℕ} {P N : Subgroup Γ} {D : Finset Γ} (h : W172PliftSetup p P N D) :
    (∃ B : Subgroup Γ, B ≤ P ∧ CFSG.Open.IsElemAbelian p B ∧ Nat.card B = p ^ D.card) ∧
      ∀ d ∈ D, ∃ B : Subgroup Γ, B ≤ P ⊓ Subgroup.centralizer {d} ∧
        CFSG.Open.IsElemAbelian p B ∧ Nat.card B = p ^ (D.card - 1) := by
  classical
  have hp := h.prime
  have hp2 := h.odd
  choose! y hyP hy1 hyp hyinv hycen using fun e (he : e ∈ D) => w172_plift_eig_lift h he
  have hcomm : ∀ e ∈ D, ∀ f ∈ D, y e * y f = y f * y e := by
    intro e he f hf
    by_cases hef : e = f
    · rw [hef]
    · exact w172_two27 hp hp2 h.pgroup (by rw [pow_two]; exact h.sq e he)
        (by rw [pow_two]; exact h.sq f hf) hef (h.comm e he f hf) (h.norm_p e he) (h.norm_p f hf)
        (fun u hu h1 h2 => h.no_two_inverted e he f hf hef u hu h1 h2) (hyP e he) (hyP f hf)
        (hyinv e he) (hycen e he f hf (Ne.symm hef)) (hycen f hf e he hef) (hyinv f hf)
  have hcard := fun (S : Finset Γ) (hS : S ⊆ D) =>
    w172_plift_card_family hp hp2 y hy1 hyp hyinv hycen hcomm hS
  refine ⟨⟨Subgroup.closure (y '' (D : Set Γ)), ?_, (hcard D subset_rfl).1,
    (hcard D subset_rfl).2⟩, fun d hd => ⟨Subgroup.closure (y '' ((D.erase d : Finset Γ) : Set Γ)),
    ?_, (hcard _ (Finset.erase_subset d D)).1, ?_⟩⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨e, he, rfl⟩
    exact hyP e he
  · refine le_inf ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ ⟨e, he, rfl⟩
      exact hyP e (Finset.mem_of_mem_erase he)
    · rw [Subgroup.closure_le]
      rintro _ ⟨e, he, rfl⟩
      have hed := Finset.mem_erase.mp he
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h1 := hycen e hed.2 d hd (Ne.symm hed.1)
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · rw [(hcard _ (Finset.erase_subset d D)).2, Finset.card_erase_of_mem hd]

end CFSG.LocalAnalysis.WeakClosure81

end
