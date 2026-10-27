module

public import CFSG.Sporadic.Schreier.M12
public import Certificates.Certificate4241

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m12_no_order_twelve :
    ∀ x : NativeSporadic.M12, orderOf x ≠ 12 := by
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  have h := card_orderOf_eq (by norm_num) m12Certificate hQ (m := 12) (by norm_num)
  rw [Certificates.certificate4241, m12Certificate_originalSubgroup] at h
  intro x hx
  have hpos : 0 < Nat.card {y : NativeSporadic.M12 // orderOf y = 12} :=
    haveI : Nonempty {y : NativeSporadic.M12 // orderOf y = 12} := ⟨⟨x, hx⟩⟩
    Nat.card_pos
  omega

end CFSG.Sporadic.Schreier
