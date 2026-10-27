module

public import CFSG.Quasithin.Background.F918Z7bCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

theorem caseII_concl
    (h45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1) (hX : Insp5aNonShape)
    {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}
    (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G) (hAT : A ≤ T')
    (hAD : ∀ a ∈ A, D.map (MulAut.conj a).toMonoidHom = D) : Z37Concl D X :=
  caseII_concl_of_core
    (fun {_ _} hZ' {_} hA' hAT' hAD' hnc' => caseII_core h45 hF hX hZ' hA' hAT' hAD' hnc')
    hZ hA hAT hAD

end CFSG.Quasithin
