module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33bAux6

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A X Y : Subgroup Γ}

theorem iThetaM_iThetaL_mem
    (h : NearAsolvAction p A X) (hY : (iPairsY A X Y).Nonempty) :
    (iThetaM A X Y, iThetaL A X Y) ∈ iPairsY A X Y :=
  (Thm33b.thm33b_below p (Nat.card ↥X + 1) Γ A X Y (Nat.lt_succ_self _) h hY).1

theorem kOf_le_iThetaM
    (h : NearAsolvAction p A X) (hY : (iPairsY A X Y).Nonempty) :
    kOf X ≤ iThetaM A X Y :=
  (Thm33b.thm33b_below p (Nat.card ↥X + 1) Γ A X Y (Nat.lt_succ_self _) h hY).2.1

theorem iThetaY_mem_iEset
    (h : NearAsolvAction p A X) (hY : (iPairsY A X Y).Nonempty) :
    iThetaY A X Y ∈ iEset A X Y :=
  (Thm33b.thm33b_below p (Nat.card ↥X + 1) Γ A X Y (Nat.lt_succ_self _) h hY).2.2.1

omit [Finite Γ] in
theorem iThetaL_le_iThetaY (A X Y : Subgroup Γ) : iThetaL A X Y ≤ iThetaY A X Y :=
  iSup₂_le fun P hP =>
    le_iSup₂ (f := fun Z (_ : Z ∈ iEset A X Y) => Z) P.2 ⟨hP.1.2.1, hP.2⟩

theorem iThetaY_le_iThetaM
    (h : NearAsolvAction p A X) (hY : (iPairsY A X Y).Nonempty) :
    iThetaY A X Y ≤ iThetaM A X Y :=
  (Thm33b.thm33b_below p (Nat.card ↥X + 1) Γ A X Y (Nat.lt_succ_self _) h hY).2.2.2

omit [Finite Γ] in
theorem iThetaM_le_iThetaU (A X Y : Subgroup Γ) : iThetaM A X Y ≤ iThetaU A X Y :=
  iSup₂_le fun P hP => Thm33a.pair_le_iThetaU (X₁ := P.1) (X₂ := P.2) hP

end CFSG.SignalizerFunctorTheorem.McBride.Near
