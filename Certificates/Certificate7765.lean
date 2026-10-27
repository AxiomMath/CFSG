module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Pres
import Certificates.Kernel.PresLetters.F7765
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7765 : Finite (PG 4 burnsideF48t_g23Ws) ∧ Nat.card (PG 4 burnsideF48t_g23Ws) ≤ 4245696 := by
  obtain ⟨f, c⟩ := TableFact.card_restrict burnsideF48t_g23Ws (by norm_num) (subsetOf 4 [0, 1, 2])
    (by decide) CFSG.KBFact.F7765a CFSG.KBFact.F7765b
  exact ⟨f, c.trans (by norm_num)⟩

end Certificates
