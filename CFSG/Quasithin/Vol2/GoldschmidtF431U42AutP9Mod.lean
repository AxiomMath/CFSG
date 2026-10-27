module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7E4

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def lt2 : PL := comp (Th2.getD 1 []) (Th2.getD 2 [])

theorem P9_check :
    fhatL ∈ Bl2 ∧ lt2 ∈ Bl2 ∧ lt2 ≠ idL ∧ (∃ k < 43, invL k = lt2 ∧ invTgt.getD k 0 = 1) ∧
    (∀ l ∈ Al2, l ∈ ZCl → ∃ a ∈ Bl1, a ≠ idL ∧ ∃ b ∈ Bl2, b ≠ idL ∧ comp a b = l) ∧
    xL ∈ Al2 ∧ xL ∈ ZCl ∧ comp fhatL xL ∈ Al2 ∧ comp fhatL xL ∈ ZCl ∧ fhatL ≠ idL := by
  decide +kernel

end CFSG.Quasithin.H13.F431.U42Aut
