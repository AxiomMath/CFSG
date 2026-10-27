module

public import CFSG.Quasithin.EmptyFaithful.S153QPB4
public import CFSG.Quasithin.EmptyFaithful.S153QSL3

public section

namespace CFSG.Quasithin

theorem stages14613_to_14617_of_SBc17K_cert_noUK_solDec
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iOE : SBc17.Input14615ContraOuterE)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP ∧ Stage14614 ∧ Stage14615 ∧ Stage14616 ∧ Stage14617 :=
  stages14613_to_14617_of_SBc17F_cert_noUK_solDec hC27 h2 h5 h12 h4 h36 h38 iA iB1 iB2 i14b i14c iSF
    iFix (SBc17.input14615ContraOuterD_of_E h36 iOE)
    (SBc17.input14615ContraInnerE_of_F_nc SBc17.input14615ContraInnerF_proved) iWeak iF

end CFSG.Quasithin
