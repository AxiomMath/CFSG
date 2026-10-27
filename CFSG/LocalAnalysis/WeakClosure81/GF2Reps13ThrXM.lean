module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXMC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

theorem s13_three_case_two_tetracode (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    (hov : ∃ a ∈ A,
      (s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q).ncard = 2) :
    ∃ L : Subgroup (MulAut W), L ≤ X ∧ Conc4_133 A t L ∧
      L = s13XSupp X (s13Supp X L) := by
  obtain ⟨L, hLX, hQL, hLrank, hLrk, hLcost, hLind, hLsupp⟩ :=
    w16g_three_tetracode_step h hH0 hQ3 he hov
  have hp3 : Nat.Prime 3 := by norm_num
  have hLp : L ≤ pCoreOf 3 A := hLX.trans h.hXO
  have hinv : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro hbot
    refine w16g_three_inv_ne_bot h ?_
    have h1 : ⁅Q, Subgroup.zpowers t⁆ ≤ ⁅L, Subgroup.zpowers t⁆ :=
      Subgroup.commutator_mono hQL le_rfl
    rw [hbot] at h1
    exact le_bot_iff.mp h1
  have ht3 : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 := by
    have hle3 : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 := h.hrk
    have hcost := (cost_commSub_Q h).1
    have h6 := w16g_three_rk_eq_six h he
    have h3 : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) = 3 := by
      omega
    have hle : commSub (commSub ⊤ Q) (Subgroup.zpowers t) ≤
        commSub ⊤ (Subgroup.zpowers t) :=
      commSub_mono le_top le_rfl
    have hge : 3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) :=
      le_trans (le_of_eq h3.symm) (rk_mono hle)
    omega
  refine ⟨L, hLX, ?_, hLsupp⟩
  exact ⟨3, hp3, hLp, hinv, hLind,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨hLrank, hLrk, hLcost, ht3⟩)))⟩

end CFSG.LocalAnalysis.WeakClosure81
