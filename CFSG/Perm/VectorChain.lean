module

public import CFSG.Perm.OrbitTree

public section

namespace CFSG.Perm

variable {G X : Type*} [Group G] [MulAction G X]

theorem card_closure_eq_prod_of_chain (m : ℕ) (base : ℕ → X) (gens : ℕ → Set G)
    (size : ℕ → ℕ) (pt : ℕ → ℕ → X) (tr : ℕ → ℕ → G)
    (hgens : ∀ j < m, gens (j + 1) ⊆ Subgroup.closure (gens j))
    (hfix : ∀ j < m, ∀ g ∈ gens (j + 1), g • base j = base j)
    (hsize : ∀ j < m, 0 < size j)
    (hpt : ∀ j < m, pt j 0 = base j) (htr0 : ∀ j < m, tr j 0 = 1)
    (htr : ∀ j < m, ∀ k < size j, tr j k ∈ Subgroup.closure (gens j))
    (hsmul : ∀ j < m, ∀ k < size j, tr j k • base j = pt j k)
    (hinj : ∀ j < m, ∀ k < size j, ∀ k' < size j, pt j k = pt j k' → k = k')
    (hclosed : ∀ j < m, ∀ k < size j, ∀ g ∈ gens j, ∃ k' < size j, g • pt j k = pt j k')
    (hschreier : ∀ j < m, ∀ g ∈ gens j, ∀ k < size j, ∀ k' < size j, g • pt j k = pt j k' →
      (tr j k')⁻¹ * g * tr j k ∈ Subgroup.closure (gens (j + 1)))
    (hlast : gens m ⊆ {1}) :
    Nat.card (Subgroup.closure (gens 0)) = ∏ j ∈ Finset.range m, size j := by
  have hlevel : ∀ j < m, Nat.card (Subgroup.closure (gens j)) =
      size j * Nat.card (Subgroup.closure (gens (j + 1))) := fun j hj =>
    card_closure_eq_mul (hsize j hj) (hinj j hj)
      (fun k hk g hg => (hclosed j hj k hk g hg).imp fun _ h => ⟨h.1, h.2.symm⟩) (htr0 j hj)
      (htr j hj) (fun k hk => by rw [hpt j hj]; exact hsmul j hj k hk)
      ((Subgroup.closure_le _).2 (hgens j hj))
      ((Subgroup.closure_le _).2 fun g hg => by
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, hpt j hj]
        exact hfix j hj g hg)
      fun k hk g hg k' hk' e => hschreier j hj g hg k hk k' hk' e.symm
  have key : ∀ i ≤ m, Nat.card (Subgroup.closure (gens 0)) =
      (∏ j ∈ Finset.range i, size j) * Nat.card (Subgroup.closure (gens i)) := by
    intro i hi
    induction i with
    | zero => rw [Finset.prod_range_zero, one_mul]
    | succ i ih => rw [ih (by omega), hlevel i (by omega), Finset.prod_range_succ, mul_assoc]
  rw [key m le_rfl, Subgroup.closure_eq_bot_iff.2 hlast, Subgroup.card_bot, mul_one]

theorem card_closure_dvd_of_chain (m : ℕ) (base : ℕ → X) (gens : ℕ → Set G)
    (size : ℕ → ℕ) (pt : ℕ → ℕ → X) (tr : ℕ → ℕ → G)
    (hgens : ∀ j < m, gens (j + 1) ⊆ Subgroup.closure (gens j))
    (hfix : ∀ j < m, ∀ g ∈ gens (j + 1), g • base j = base j)
    (hsize : ∀ j < m, 0 < size j)
    (hpt : ∀ j < m, pt j 0 = base j) (htr0 : ∀ j < m, tr j 0 = 1)
    (htr : ∀ j < m, ∀ k < size j, tr j k ∈ Subgroup.closure (gens j))
    (hsmul : ∀ j < m, ∀ k < size j, tr j k • base j = pt j k)
    (hinj : ∀ j < m, ∀ k < size j, ∀ k' < size j, pt j k = pt j k' → k = k')
    (hclosed : ∀ j < m, ∀ k < size j, ∀ g ∈ gens j, ∃ k' < size j, g • pt j k = pt j k')
    (hschreier : ∀ j < m, ∀ g ∈ gens j, ∀ k < size j, ∀ k' < size j, g • pt j k = pt j k' →
      (tr j k')⁻¹ * g * tr j k ∈ Subgroup.closure (gens (j + 1)))
    (hlast : gens m ⊆ {1}) {N : ℕ} (hN : ∏ j ∈ Finset.range m, size j ∣ N) :
    Nat.card (Subgroup.closure (gens 0)) ∣ N := by
  rwa [card_closure_eq_prod_of_chain m base gens size pt tr hgens hfix hsize hpt htr0 htr hsmul
    hinj hclosed hschreier hlast]

end CFSG.Perm
