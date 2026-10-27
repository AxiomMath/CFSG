module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux6

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A X Y : Subgroup Γ}

theorem iThm35
    (h : NearAsolvAction p A X) {D₂ : Subgroup Γ}
    (hD₂ : (iPairsY A X D₂).Nonempty)
    [(D₂.subgroupOf (cenIn X (A : Set Γ))).Normal] {N L R : Subgroup Γ}
    (hN : N ≤ X) (hL : L ≤ X) (hR : R ≤ X)
    (ha : IsNormalIn N (R ⊔ cenIn X (A : Set Γ) ⊔ A) ∧ IsNormalIn L (R ⊔ cenIn X (A : Set Γ) ⊔ A) ∧
      IsNormalIn R (R ⊔ cenIn X (A : Set Γ) ⊔ A))
    (hb : IsChiefFactorOf (R ⊔ cenIn X (A : Set Γ) ⊔ A) L N ∧ L ≤ R)
    (hc : A ⊔ R ≤ secCenIn (R ⊔ cenIn X (A : Set Γ) ⊔ A) L N)
    (hd : R ⊓ cenIn X (A : Set Γ) = fittingPre (cenIn X (A : Set Γ)) D₂ ∧
      cenIn X (A : Set Γ) ⊓ N ≤ D₂ ∧
      IsDirectProductMod N (fittingPre (cenIn X (A : Set Γ)) D₂ ⊔ N) (D₂ ⊔ N) L) :
    ∃ B : Subgroup Γ, B ≤ R ∧ IsNormalIn B (R ⊔ cenIn X (A : Set Γ) ⊔ A) ∧
      B ⊓ cenIn X (A : Set Γ) = D₂ ∧ R = B ⊔ fittingPre (cenIn X (A : Set Γ)) D₂ :=
  Thm35.thm35_below p (Nat.card ↥X + 1) Γ A X (cenIn X (A : Set Γ)) D₂ N L R (Nat.lt_succ_self _)
    ⟨h, rfl, hD₂, hN, hL, hR, ha.1, ha.2.1, ha.2.2, hb.1, hb.2, hc, hd.1, hd.2.1, hd.2.2⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near
