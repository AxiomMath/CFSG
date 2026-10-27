module

public import CFSG.RankThree.GF2n.Smith81.S81UFrame
public import CFSG.RankThree.GF2n.Smith81.S81UElem

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.RankThree.GF2n.Smith81.EGeom CFSG.RankThree.GF2n.Smith81.U6Cube
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

theorem u6MinuscStatement_holds :
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ) (_ : Nat.card F = (2 ^ f) ^ 2)
      (K : Type) [Field K] [Finite K] (e : K ≃+* Fσ (unitaryInvolution F 2 f)),
      MinuscGeom (e3uGam (unitaryInvolution F 2 f) e) (e3uP0 (unitaryInvolution F 2 f) e)
        (e3uU0 (unitaryInvolution F 2 f) e) 10 ∧
      MinuscLine (e3uGam (unitaryInvolution F 2 f) e) (e3uP0 (unitaryInvolution F 2 f) e)
        (e3uU0 (unitaryInvolution F 2 f) e) := by
  intro F _ _ _ f hF K _ _ e
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  have hKF : Nat.card F = Nat.card K ^ 2 := by
    have h1 : Nat.card K = 2 ^ f := (Nat.card_congr e.toEquiv).trans (card_Fσ_eq hF)
    rw [h1, hF]
  exact ⟨u6_MinuscGeom hσ hKF, u6_MinuscLine hσ⟩

end CFSG.RankThree.GF2n.Smith81
