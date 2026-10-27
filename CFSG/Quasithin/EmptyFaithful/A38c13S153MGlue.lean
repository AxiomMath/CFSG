module

public import CFSG.Quasithin.EmptyFaithful.A38c13S1565C
public import CFSG.Quasithin.EmptyFaithful.A38c13S153MOne
public import CFSG.Quasithin.EmptyFaithful.A38c13S153MTwo

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace S153M

theorem eltOne_unconditionalC
    (hA21 : AsA21SQTKSection) (h51 : AsB51) :
    Input15365FFnatEltOneC :=
  eltOne_holdsC hA21 h51 (noStrongOne_holdsC hA21 h51)

theorem input15365FFnatElt_of_one_twoC (hOne : Input15365FFnatEltOneC)
    (hTwo : Input15365FFnatEltTwoC) : Input15365FFnatEltC := by
  intro G _ _ T Mc M V₁ V₂ H K t D I hV₁I hIU W hW hirr hne hFF
  by_cases hK0 : conjClosure K T = K
  · exact hOne G T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hne hFF
  · exact hTwo G T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hne hFF

theorem input15365FFnatElt_unconditionalC
    (hA21 : AsA21SQTKSection) (h51 : AsB51) (h56 : AsB56)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) : Input15365FFnatEltC :=
  input15365FFnatElt_of_one_twoC (eltOne_unconditionalC hA21 h51)
    (eltTwo_unconditionalC hA21 h56 hA37 hA38)

theorem stage15365One_of_natmodule_elt_inputsC
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hE22 : E2.E22StatementW) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (hNat : Input15365TypesFourNatModuleC) (hElt : Input15365FFnatEltC) : Stage15365One :=
  stage15365One_of_layer_inputsC h11 h113 hE22 input15365Odd_of
    (input15365TypesFour_of_eltC (input15365TypesFourElt_of_natmoduleC hD310 hD391 hI4 hNat))
    (input15365TypesFive_ofC hD36 hD37 hD321 hI5 hA37 hA38)
    (input15365FFnat_of_eltC hElt)

end S153M

end CFSG.Quasithin
