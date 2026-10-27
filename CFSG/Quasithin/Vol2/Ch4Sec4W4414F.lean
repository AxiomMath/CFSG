module

public import CFSG.Quasithin.Vol2.Ch4Sec4W4414Z
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.KGFact4413All

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13

theorem thm4414ZCentral_holds (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : Thm4414ZCentral := by
  intro G _ _ T M L V₀ H hs hnab hK hT hM hTM hL hLf hLM hq hV₀ hV₀r hH hV1 _ hnFF
  exact le_centralizer_omegaOneCenter_of_hyp421 ⟨hs, hnab, hK, hT, hM, hTM, hL, hLf, hLM, hq⟩
    hC58 h317 h37 h38 h39 hV₀ hV₀r hH hV1 hnFF

theorem stmt4_4_14_of_steps
    (h443 : Stmt4_4_3Orbit') (hC : E2.E22StatementC)
    (hC58 : TheoremC58) (h317 : AS317Sylow) : Stmt4_4_14 := by
  have hE : E22BorelFacts := e22BorelFacts_of_lie hC e22BorelFactsLie_holds
  have hNA : Lemma4413NA := lemma4413NA_of_lie hC lemma4413NALie_holds
  have h37 : A37ForSQTK := a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat
    (CFSG.QuasithinUnique.Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact
      CFSG.QuasithinUnique.Vol2Native.a134SQTKFactCat
      CFSG.QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
      CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
  have h39 : A39ForSQTK := a39ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a39ForSQTKCat_proved
  exact stmt4_4_14_of h443 (stmt4_4_13_of hE hNA) (thm4414ZCentral_holds hC58 h317 h37 h38 h39)
    (e22HallAbelian_of hE) h37 h38 h39

end CFSG.Quasithin.H13.Ch4
