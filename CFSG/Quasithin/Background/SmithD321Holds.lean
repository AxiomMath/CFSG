module

public import CFSG.Quasithin.Background.SmithD321CaseI
public import CFSG.Quasithin.Background.SmithD321Two
public import CFSG.Quasithin.Background.SmithD39TwoSzHolds
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DiscList
public import CFSG.Quasithin.Background.F918K8
public import CFSG.Quasithin.Background.SmithD321SzK
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DiscAut

public section

namespace CFSG.Quasithin

namespace SmithD321

theorem caseIStep_of (h56 : AsB56) (h37 : D37) : CaseIStep :=
  fun _ _ _ _ _ _ _ _ _ _ _ hS hVT hAC => caseI_false h56 h37 hS hVT hAC

end SmithD321

open SmithD321 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique in
theorem d321_of_inputs
    (h36 : D36c) (h37 : D37) (hL38 : D3L38) (h38 : D38Top)
    (hB42 : AsB42) (hB56 : AsB56) (hA21 : AsA21SQTKSection) (hA23 : A23SQTKListFact)
    (hS3 : H13.SimpleThreePrimeSuzukiFact) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hNS : Insp5aNonShape) (hSz : SzStep) :
    ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
      D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
        Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
        orbSup T V = ⊤ ∨
          (IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
            commV L ≤ fixV (conjAutSub t L) ∧ (D321Two L ∨ D321Three Mp L)) :=
  d321_of_steps h36 h37 hL38 h38 hA23 hS3 (caseIStep_of hB56 h37)
    (caseIIaStep_holds hA21 hB42 (a38B42_of hF hNS)) hSz

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique in
theorem d321_holds
    :
    ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
      D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
        Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
        orbSup T V = ⊤ ∨
          (IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
            commV L ≤ fixV (conjAutSub t L) ∧ (D321Two L ∨ D321Three Mp L)) :=
  d321_of_inputs SmithD39Two.d36c_holds d37_holds (d3L38_of_a38 d3A38_holds)
    SmithD39Two.d38Top_holds asB42_holds asB56_holds asA21SQTKSection a23SQTKListFact
    H13.simpleThreePrimeSuzukiFact Vol2.Ch10.SecA.facts10_1_holds insp5aNonShape_holds
    (SmithD321.szStep_holds H13.szTwoAutInnerFact asB45_holds Vol2.Ch10.SecA.facts10_1_holds
      asA21SQTKSection asB42_holds SmithD39Two.d38Top_holds a23SQTKListFact
      H13.simpleThreePrimeSuzukiFact (d3L38_of_a38 d3A38_holds))

end CFSG.Quasithin
