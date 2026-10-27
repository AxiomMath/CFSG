module

public import CFSG.LocalAnalysis.StandardType.PhanELocalFlag
public import CFSG.ClassicalInvolution.Phan.Frames.Basic

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.ClassicalGroups.Unitary Module

variable {K : Type} [Field K] {σ : K ≃+* K}

private theorem plh_filter_insert (k : Fin 4) :
    (Finset.univ.filter fun k' : Fin 4 => k'.val < k.val + 1) =
      insert k (Finset.univ.filter fun k' : Fin 4 => k'.val < k.val) := by
  ext k'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h' | h'
    · exact Or.inr h'
    · exact Or.inl (Fin.ext h')
  · rintro (rfl | h')
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt h'

private theorem plh_filter_zero :
    (Finset.univ.filter fun k : Fin 4 => k.val < 0) = ∅ := by
  ext k
  simp

private theorem plh_card_filter_val_lt (j : ℕ) (hj : j ≤ 4) :
    (Finset.univ.filter fun k : Fin 4 => k.val < j).card = j := by
  have h := Fin.card_filter_val_lt (n := 4) (m := j)
  rwa [min_eq_right hj] at h

private theorem plh_sup_inf_perp_eq_left {A B : Submodule K (Fin 4 → K)}
    (hB : Nondeg σ B) (hAB : Orth σ A B) :
    (A ⊔ B) ⊓ perp σ B = A := by
  have hAperp : A ≤ perp σ B := fun a ha => mem_perp.mpr (hAB a ha)
  rw [sup_inf_assoc_of_le B hAperp]
  have hrad : B ⊓ perp σ B = ⊥ := by
    simpa [rad] using (nondeg_iff_rad_eq_bot (S := B)).mp hB
  rw [hrad, sup_bot_eq]

@[expose] def NondegFlag (σ : K ≃+* K) (x : FlagK K 4) : Prop :=
  ∀ r : ℕ, r ≤ 4 → Nondeg σ (x.E r)

@[expose] noncomputable def frameOfFlag (hσ : IsUnitaryInvolution σ) (x : FlagK K 4)
    (hx : NondegFlag σ x) : Frame σ 4 where
  line k := x.E (k.val + 1) ⊓ perp σ (x.E k.val)
  finrank_line k := by
    have hP : Nondeg σ (x.E k.val) := hx k.val (by omega)
    have hPW : x.E k.val ≤ x.E (k.val + 1) := x.mono (Nat.le_succ _)
    have hdim := finrank_eq_add_finrank_inf_perp hσ hP hPW
    have hk := x.dim k.val (by omega)
    have hk1 := x.dim (k.val + 1) (by omega)
    omega
  nondeg_line k :=
    Nondeg.inf_perp hσ (hx (k.val + 1) (by omega)) (hx k.val (by omega))
      (x.mono (Nat.le_succ _))
  orth_line k l hkl := by
    intro u hu v hv
    rcases lt_or_gt_of_ne (fun h => hkl (Fin.ext h)) with h | h
    · exact herm_eq_zero_comm σ hσ.invol (hv.2 u (x.mono (by omega) hu.1))
    · exact hu.2 v (x.mono (by omega) hv.1)

@[expose] noncomputable def flagOfFrame (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    FlagK K 4 where
  E j := c.spanAt (Finset.univ.filter fun k : Fin 4 => k.val < j)
  mono := by
    intro a b hab
    exact c.spanAt_mono fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      omega
  dim := by
    intro j hj
    rw [Frame.finrank_spanAt]
    exact plh_card_filter_val_lt j hj
  top := by
    intro j hj
    have hS : (Finset.univ.filter fun k : Fin 4 => k.val < j) = Finset.univ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact lt_of_lt_of_le k.isLt hj
    rw [hS]
    exact Frame.spanAt_univ hσ

theorem nondegFlag_flagOfFrame (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    NondegFlag σ (flagOfFrame hσ c) := by
  intro r _
  change Nondeg σ (c.spanAt (Finset.univ.filter fun k : Fin 4 => k.val < r))
  exact Frame.nondeg_spanAt hσ _

theorem frameOfFlag_flagOfFrame (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    frameOfFlag hσ (flagOfFrame hσ c) (nondegFlag_flagOfFrame hσ c) = c := by
  refine Frame.ext (funext fun k => ?_)
  change c.spanAt (Finset.univ.filter fun k' : Fin 4 => k'.val < k.val + 1) ⊓
    perp σ (c.spanAt (Finset.univ.filter fun k' : Fin 4 => k'.val < k.val)) = c.line k
  rw [plh_filter_insert k, Frame.spanAt_insert]
  exact plh_sup_inf_perp_eq_left (Frame.nondeg_spanAt hσ _)
    (Frame.orth_spanAt (c := c) (l := k)
      (S := Finset.univ.filter fun k' : Fin 4 => k'.val < k.val) (by simp))

theorem flagOfFrame_frameOfFlag (hσ : IsUnitaryInvolution σ) (x : FlagK K 4)
    (hx : NondegFlag σ x) : flagOfFrame hσ (frameOfFlag hσ x hx) = x := by
  have hE : ∀ j ≤ 4, (frameOfFlag hσ x hx).spanAt
      (Finset.univ.filter fun k : Fin 4 => k.val < j) = x.E j := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [plh_filter_zero, Frame.spanAt_empty, FlagK.E_zero]
    | succ j ih =>
      intro hj
      have hlt : j < 4 := by omega
      rw [plh_filter_insert ⟨j, hlt⟩, Frame.spanAt_insert]
      rw [ih (by omega)]
      have hline : (frameOfFlag hσ x hx).line ⟨j, hlt⟩ =
          x.E (j + 1) ⊓ perp σ (x.E j) := rfl
      rw [hline, sup_comm]
      exact sup_inf_perp_of_nondeg hσ _ rfl (hx j (by omega)) (x.mono (Nat.le_succ j))
  apply FlagK.ext4
  · exact hE 1 (by norm_num)
  · exact hE 2 (by norm_num)
  · exact hE 3 (by norm_num)

end CFSG.ClassicalInvolution.Phan.PhanE

end
