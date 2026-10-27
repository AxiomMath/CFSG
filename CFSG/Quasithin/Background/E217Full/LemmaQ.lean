module

public import CFSG.Quasithin.Background.E217Full.QInvolution
public import CFSG.Quasithin.Background.E217Full.QCentral
public import CFSG.Quasithin.Background.E217Full.QRankTwo

public section

namespace CFSG.Quasithin.E217Full.LemmaQ

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem qhatOf_le_one [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hV16 : Nat.card V = 16)
    {X : Subgroup (MulAut V)} (hX : IsPGroup 2 X) (h8 : 8 ≤ Nat.card X) :
    qhatOf X ≤ ((1 : ℚ) : WithTop ℚ) := by
  have hne : X ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h8
    omega
  obtain ⟨z, hzX, hz1, hz, hzc⟩ := exists_central_involution hX hne
  rcases index_fixV_zpowers hV hV16 hz hz1 with h2 | h4
  · exact qhatOf_le_one_of_index_two hV hzX hz hz1 h2
  · exact qhatOf_le_one_of_index_four hV hV16 hX h8 hz hzc h4

end CFSG.Quasithin.E217Full.LemmaQ
