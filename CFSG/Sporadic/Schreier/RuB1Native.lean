module

public import CFSG.Sporadic.Schreier.RuB1Facts
public import CFSG.Sporadic.Schreier.RuB1E8
public import CFSG.Sporadic.Schreier.RuB1XFacts
public import CFSG.Sporadic.Schreier.RuB1F8
public import Certificates.Certificate15119

public section

namespace CFSG.Sporadic.RuSchreier


theorem ruB1NativeFacts : RuB1NativeFacts ruESub ruXN ruG5 where
  A1_char := ruESub_char_of_check Certificates.certificate15119.1
  X_eq := rfl
  X_comm := ruXN_comm_of_check Certificates.certificate15119.2.1
  X_sq := ruXN_sq_of_check Certificates.certificate15119.2.1
  card_X := card_ruXN_of_check Certificates.certificate15119.2.1
  X_le := ruXN_le_of_check Certificates.certificate15119.2.1
  g5_mem := ruG5_mem
  g5_order := orderOf_ruG5_of_check Certificates.certificate15119.2.1
  g5_cent := ruG5_cent_of_check Certificates.certificate15119.2.1
  g5_gen := ruG5_gen_of_check Certificates.certificate15119.2.1
  F8 := ruB1_F8_of_check Certificates.certificate15119.2.2

end CFSG.Sporadic.RuSchreier
