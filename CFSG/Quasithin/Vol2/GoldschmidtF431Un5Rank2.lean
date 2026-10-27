module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LocWire
public import CFSG.Quasithin.Vol2.Ch5Sec3PerType
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Rec

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Blueprint CFSG.Quasithin.H13

theorem finite_of_lieModel_psu5 {f : ℕ} (D : Type) [Group D] (hD : LieModel D .PSU 5 2 f) :
    Finite D := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un5_model_equiv hD
  exact Finite.of_equiv _ e.toEquiv

theorem f431Out_psu5 (hOut : F431UnOutLieProp 5 2) : F431Out .PSU 5 2 :=
  f431Out_of_unLie (fun D _ hD => finite_of_lieModel_psu5 D hD) hOut

section Main


theorem f431Rank2At_psu5_of_inputs (hOut : F431UnOutLieProp 5 2) (hStd : Un5StdDatum) :
    F431Rank2At .PSU 5 := by
  intro G _ _ hG hnab M₁ M₂ f hP hyps
  have hf : f = 2 := by
    rcases hP.2 with h | h | h | h | h | h | h <;> simp_all
  subst hf
  exact f431_nonL3_of_inputs f431Recognition_un5 (f431Out_psu5 hOut)
    (f431Local_psu5_of_std hStd) G hG hnab M₁ M₂ hyps

end Main

end CFSG.Quasithin.H13.F431.Un
