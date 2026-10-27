
module


public import Certificates.Certificate3085

public section

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.Ly.Omega

set_option maxRecDepth 3000 in
theorem ly_certificate : LyFacts :=
  Certificates.certificate3085.1.snd.1

theorem ly_word_facts : LyWordFacts :=
  Certificates.certificate3085.1.snd.2.1

theorem ly_five_facts : LyFiveFacts :=
  Certificates.certificate3085.1.snd.2.2

end CFSG.Sporadic.Ly
