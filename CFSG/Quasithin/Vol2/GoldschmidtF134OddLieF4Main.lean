module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Trans
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Contain
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Out

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Blueprint CFSG.QuasithinUnique

theorem f4Even_simple :
    ∀ n : ℕ, NoOddCfg fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n := by
  intro n A _ _ p _ L P T hp5 hL hcfg
  obtain ⟨hn, hout⟩ := F4.odd_and_pow_mem_inner hL
  exact F4.false_of_odd_out hp5 hcfg (F4.center_eq_bot hL) hn hout
    (fun _ _ _ ha hS hSH hH => F4.le_normalizer_of_card_eq hL (Fact.out : p.Prime) hp5 ha hS hSH hH)
    (fun _ hS _ hx _ hy => F4.commutator_mem_of_isSylowTwoOf hL hS hx hy)

end CFSG.Quasithin.H13.NQCore
