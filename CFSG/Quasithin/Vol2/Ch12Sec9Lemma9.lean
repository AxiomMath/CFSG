module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9Two
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9W0
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem lemma12_9_9 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1293 : Lemma12_9_3One) (h1294 : Lemma12_9_4)
    (h1295 : Lemma12_9_5) (h1296 : Lemma12_9_6) (h1297 : Lemma12_9_7) : Lemma12_9_9 := by
  intro G _ _ T L V n hcx
  have hW₀ : (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) ≤
      Subgroup.centralizer (V : Set G) := iSup₂_le fun g hg =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (commutator_eq_bot_of_conjugate_le h1222 h12213 h37 h38 h39 h1293 h1294 h1295 h1296 h1297
        hcx hg)
  exact ⟨⟨hW₀, normalizer_wZero_le h1222 h37 h38 h39 hcx hW₀⟩, fun g hAT hidx hAV =>
    inf_centralizer_eq_bot_of_hyperplane h1222 h37 h38 h39 h1294 h1297 hcx hAT hidx hAV⟩

end CFSG.Quasithin.H13
