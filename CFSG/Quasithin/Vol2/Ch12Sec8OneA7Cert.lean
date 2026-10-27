module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Fact
public import CFSG.Quasithin.Vol2.Ch12Sec8OneSix
public import Certificates.Certificate7099

public section

namespace CFSG.Quasithin.H13

theorem a7NatFact12813 : A7NatFact12813 :=
  A7Mod.a7NatFact12813_of_raw Certificates.certificate7099

theorem lemma12_8_13_six_hat (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1228 : Stmt12_2_8) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h5 : Lemma12_8_8_five) : Lemma12_8_13_six_hat :=
  lemma12_8_13_six_hat_of h1222 h12213 h1228 h37 h38 h39 h5 a7NatFact12813

end CFSG.Quasithin.H13
