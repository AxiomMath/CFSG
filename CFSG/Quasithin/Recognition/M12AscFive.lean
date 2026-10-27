module

public import CFSG.Quasithin.Recognition.M12AscCoxRel
public import CFSG.Quasithin.Recognition.M12AscCox

public section

namespace CFSG.Quasithin

open CFSG.GH74.M12 (Asc03Hyp)

namespace AscModel

variable {G : Type*} [Group G] {z : G} (m : AscModel z)

include m

theorem five_dvd_card
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G) :
    5 ∣ Nat.card G := by
  obtain ⟨u', x1, -, -, -, -, -, -, hsq, hrel, h13, -⟩ := m.exists_coxeter hyp h27
  have h5 := coxeterA5_order_five (coxVec z x1 (m.ψ mA) u' (m.ψ mX)) hsq hrel h13
  rw [← h5]
  exact orderOf_dvd_natCard _

theorem card_eq_95040
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z)
    (hG : Nat.card G = 12096 ∨ Nat.card G = 95040) : Nat.card G = 95040 := by
  have h27 : 27 ∣ Nat.card G := by
    rcases hG with h | h <;> rw [h] <;> norm_num
  have h5 := m.five_dvd_card hyp h27
  rcases hG with h | h
  · rw [h] at h5
    omega
  · exact h

end AscModel

end CFSG.Quasithin
