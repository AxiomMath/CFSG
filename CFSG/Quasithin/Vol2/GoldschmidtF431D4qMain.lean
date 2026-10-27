module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutAsm
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocalMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSOutMain
public import CFSG.LieType.Simplicity.LieModelFinite

public section

namespace CFSG.Quasithin.H13.F431.D4q

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

set_option linter.unusedSectionVars false


theorem f431TwoOutLieProp_d4q (f : ℕ) (hf : 1 ≤ f) : F431TwoOutLieProp .trialityD4 0 f :=
  Struct.f431TwoOutLieProp_of_normalized f (OutAsm.twoOutNorm_d4q f hf)

theorem f431Out_d4q (f : ℕ) (hf : 1 ≤ f) : F431Out .trialityD4 0 f :=
  f431Out_of_twoLie (by simp) (fun _ _ hD => CFSG.LieType.Simplicity.finite_of_native_lieModel hD)
    (f431TwoOutLieProp_d4q f hf)

theorem f431Rank2At_of_std (hStd : ∀ f : ℕ, 2 ≤ f → Local.Std3D4 f) :
    F431Rank2At .trialityD4 0 := by
  intro G _ _ hG hnab M₁ M₂ f hP hyps
  have hf2 : 2 ≤ f := hP.1
  exact f431_nonL3_of_inputs (recognition_of_facts (Hex.f431ModelFacts_d4 f)
      (Hex.f431Generation_d4 f) (polyNumber .trialityD4) (three_le_polyNumber _)
      (Hex.f431Facts45_d4 f (Hex.f431ModelFacts_d4 f))
      (F48.f431F48_d4q f hf2 (Hex.f431ModelFacts_d4 f))) (f431Out_d4q f (by omega))
    (Local.f431Local_d4q f (hStd f hf2)) G hG hnab M₁ M₂ hyps

end CFSG.Quasithin.H13.F431.D4q
