module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BenderInvolutionCosetInequality

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Bender's order-four Case-1 arithmetic

This module isolates the numerical end of Bender's first case in Section 3
of *Finite groups with large subgroups*.
-/

namespace CFSG.GorensteinWalter

/-- Bender's aggregate Case-1 data force `a = 9`, no singly occupied
cosets, forty-five involutions, and ambient order `360`.

The divisibility hypothesis is Lemma 2's orbit congruence after the
fixed-point-free term is shown to vanish. -/
public theorem bender_card_four_case_one_arithmetic
    (a singleCosets involutions cosetIndex groupOrder : ℕ)
    (ha : 9 ≤ a)
    (hsingle : a ∣ singleCosets)
    (hcosets : 1 + singleCosets + 2 * a ≤ cosetIndex)
    (hcount :
      involutions = a + singleCosets + 2 * a + 2 * a)
    (hlarge : cosetIndex < involutions)
    (hratio :
      4 * (involutions - cosetIndex) = (a - 4) * cosetIndex)
    (horder : 8 * involutions = groupOrder) :
    a = 9 ∧ singleCosets = 0 ∧ involutions = 45 ∧ groupOrder = 360 := by
  have hineq :
      (a - 4) * (singleCosets + 1 + 2 * a) <
        4 * (a + 2 * a) := by
    exact bender_involution_coset_inequality
      cosetIndex involutions a singleCosets (2 * a) (2 * a) (a - 4) 4
      (by omega) hcount hlarge (by omega) hratio
  rcases hsingle with ⟨m, hm⟩
  have hsub : a - 4 + 4 = a := by omega
  have haeq : a = 9 := by nlinarith
  subst a
  norm_num at hineq hm
  have hsingleEq : singleCosets = 0 := by omega
  subst singleCosets
  have hinvolutions : involutions = 45 := by omega
  subst involutions
  omega

end CFSG.GorensteinWalter
