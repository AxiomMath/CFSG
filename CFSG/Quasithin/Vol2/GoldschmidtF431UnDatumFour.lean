module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnRank2
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieStdV
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocMain

public section

namespace CFSG.Quasithin.H13.F431.Un

theorem unStdDatum_four (f : ℕ) (hf : 2 ≤ f) : UnStdDatum f := by
  intro F _ _ _ hF ζ _
  exact ⟨zUn hF, tUn hF, v4Un hF ζ, unVL hF hf, unUcL hF hf, unRL hF hf, unKL hF hf,
    stdTwo_datum hF ζ (one_le_two.trans hf), unStdV_datum hF ζ hf, unStdLoc_datum hF hf⟩

section Main


theorem f431Rank2At_psu4_of_outLie (hOut : ∀ f : ℕ, 2 ≤ f → F431UnOutLieProp 4 f) :
    F431Rank2At .PSU 4 :=
  f431Rank2At_psu4_of_inputs hOut unStdDatum_four

end Main

end CFSG.Quasithin.H13.F431.Un
