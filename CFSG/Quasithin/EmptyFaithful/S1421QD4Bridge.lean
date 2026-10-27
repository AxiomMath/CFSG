module

public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.Recognition.CertD4Bridge

public section

namespace CFSG.Quasithin

theorem trialityD4Bridge_holds :
    TrialityD4Bridge :=
  fun D _ h => trialityD4ModelBridge_of_lieModel D h

end CFSG.Quasithin
