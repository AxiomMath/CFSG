module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux6

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A X Y : Subgroup Γ}

theorem iThetaU_mem_iUset
    (h : NearAsolvAction p A X) (hY : (iPairsY A X Y).Nonempty) :
    iThetaU A X Y ∈ iUset A X Y :=
  Thm33a.thm33a_below p (Nat.card ↥X + 1) Γ A X Y (Nat.lt_succ_self _) h hY

end CFSG.SignalizerFunctorTheorem.McBride.Near
