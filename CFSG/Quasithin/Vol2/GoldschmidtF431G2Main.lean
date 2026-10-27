module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Local
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelRec
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSOutMain

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.H13
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift


theorem f431Rank2At_g2_of_std
    (hOutLie : ∀ f : ℕ, 2 ≤ f → F431TwoOutLieProp .G2 0 f)
    (hstd : ∀ f : ℕ, 2 ≤ f → ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      ∃ (z t v nr na : ↥(adjointGroup Tag.G2 K))
        (V L Zd Qd Xd Yd : Subgroup ↥(adjointGroup Tag.G2 K)),
        StdTwo ↥(adjointGroup Tag.G2 K) (posUnipotentSub Tag.G2 K) (Pmin K ⟨1, by decide⟩)
          (Pmin K ⟨0, by decide⟩) z t ∧
        StdLoc ↥(adjointGroup Tag.G2 K) (posUnipotentSub Tag.G2 K) z t V L ∧
        StdOrient ↥(adjointGroup Tag.G2 K) (posUnipotentSub Tag.G2 K) (Pmin K ⟨1, by decide⟩)
          (Pmin K ⟨0, by decide⟩) z t v nr na Zd Qd Xd Yd (Nat.card K) 2) :
    F431Rank2At .G2 0 := by
  intro G _ _ hG hnab M₁ M₂ f hpar hyps
  have hf : 2 ≤ f := hpar.1
  exact f431_nonL3_of_inputs (f431Recognition_g2 f) (f431G2Out_of_lie (hOutLie f hf))
    (f431Local_g2_of_std hf (hstd f hf)) G hG hnab M₁ M₂ hyps

end CFSG.Quasithin.H13.F431.G2
