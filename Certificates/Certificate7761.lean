
module

public import Certificates.Certificate7761Base

import Certificates.Kernel.G23F48.Restate
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace Certificates

open CFSG CFSG.ASVolI in
theorem certificate7761 : Nat.card ↥burnsideF48t_g23X = 4245696 ∧
    Nat.card ↥burnsideF48t_g23P1' = 11664 ∧
    Nat.card ↥burnsideF48t_g23P2' = 11664 ∧
    Nat.card ↥burnsideF48t_g23B' = 2916 ∧
    Nat.card ↥burnsideF48t_g23S0' = 729 ∧
    Nat.card ↥burnsideF48t_g23K' = 4 :=
  ⟨certificate7761_card_X, CFSG.KC.G23F48.card_rest certificate7761_card_X⟩

end Certificates
