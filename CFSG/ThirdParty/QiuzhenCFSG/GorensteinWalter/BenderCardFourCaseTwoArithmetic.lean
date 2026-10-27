module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BenderInvolutionCosetInequality

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Bender's order-four Case-2 arithmetic

This module isolates the numerical end of Bender's second case in Section 3
of *Finite groups with large subgroups*.
-/

namespace CFSG.GorensteinWalter

/-- Bender's aggregate Case-2 data force no singly occupied cosets,
twenty-one involutions, and ambient order `168`. -/
public theorem bender_card_four_case_two_arithmetic
    (singleCosets involutions cosetIndex groupOrder : ℕ)
    (hcosets : 1 + singleCosets + 6 ≤ cosetIndex)
    (hcount : involutions = 9 + singleCosets + 6 + 6)
    (hlarge : cosetIndex < involutions)
    (hratio : involutions - cosetIndex = 2 * cosetIndex)
    (horder : 8 * involutions = groupOrder) :
    singleCosets = 0 ∧ involutions = 21 ∧ groupOrder = 168 := by
  have hineq : 2 * (singleCosets + 1 + 6) < 1 * (9 + 6) := by
    exact bender_involution_coset_inequality
      cosetIndex involutions 9 singleCosets 6 6 2 1
      hcosets hcount hlarge (by omega) (by simpa using hratio)
  have hsingle : singleCosets = 0 := by omega
  subst singleCosets
  have hinvolutions : involutions = 21 := by omega
  subst involutions
  omega

end CFSG.GorensteinWalter
