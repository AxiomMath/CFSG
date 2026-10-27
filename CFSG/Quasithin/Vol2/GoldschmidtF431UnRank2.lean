module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocWire
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnGlue
public import CFSG.Quasithin.Vol2.Ch5Sec3PerType

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Blueprint CFSG.Quasithin.H13

theorem finite_of_lieModel_psu4 {f : ℕ} (D : Type) [Group D] (hD : LieModel D .PSU 4 2 f) :
    Finite D := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  exact Finite.of_equiv _ e.toEquiv

theorem f431Out_psu4 {f : ℕ} (hOut : F431UnOutLieProp 4 f) : F431Out .PSU 4 f :=
  f431Out_of_unLie (fun D _ hD => finite_of_lieModel_psu4 D hD) hOut

section Main


theorem f431Rank2At_psu4_of_inputs (hOut : ∀ f : ℕ, 2 ≤ f → F431UnOutLieProp 4 f)
    (hStd : ∀ f : ℕ, 2 ≤ f → UnStdDatum f) : F431Rank2At .PSU 4 := by
  intro G _ _ hG hnab M₁ M₂ f hP hyps
  exact f431_nonL3_of_inputs (f431Recognition_un f hP.1) (f431Out_psu4 (hOut f hP.1))
    (f431Local_psu4_of_std f (hStd f hP.1)) G hG hnab M₁ M₂ hyps

end Main

end CFSG.Quasithin.H13.F431.Un
