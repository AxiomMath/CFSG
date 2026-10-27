module

public import CFSG.Quasithin.H13.U3L14E6
public import CFSG.Quasithin.H13.U3L14Producers
public import CFSG.Quasithin.H13.U3L14A

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Stmt13_3_14d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ V₃ Lp : Subgroup G), Set14 G T L V V₂ V₃ Lp →
    pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G) → StepD T V Lp

theorem stmt13_3_14_of
    (h1332 : Stmt13_3_2) (h1336 : A6.Stmt13_3_6) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (hF : A318Facts)
    (h1310 : Stmt13_3_10) (hd : Stmt13_3_14d) (hA6 : Set14ProducerA6)
    (hL32 : Set14ProducerL32) (hU33 : Set14ProducerU33) : A6.Stmt13_3_14 := by
  intro G _ _ T L V V₂ hH hV hzv hV2 hA5 hQ
  obtain ⟨V₃, Lp, S⟩ := exists_set14_of_producers h1332 hA6 hL32 hU33 hH hV hzv hV2 hA5
  obtain ⟨K, hD⟩ := S.exists_kData h1332 h1336 h37 h38 h39 hQ (hd G T L V V₂ V₃ Lp S hQ)
  have hg := S.stepG h1332 hC58 h317 h56 hQ hD
  rcases S.K_A5_or_L32 h1332 hF h38 hD hg with h | h
  · exact S.false_of_A5 h1332 h1310 hA5 hD hg h
  · exact S.not_L32 hD hg h

end CFSG.Quasithin.H13.U3
