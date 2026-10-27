module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP3
import Certificates.Kernel.M24Dc.Over
public import CFSG.Assembly.Defs

public section

public section

namespace Certificates

open CFSG.Blueprint.NativeSporadic

theorem certificate589201 : 
    CFSG.Quasithin.H13.OverSylow2M24Cov := by
  intro X S hS hcard hSX h5 h9
  by_contra hne
  have hG : Nat.card (Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
  have hidx : S.index = 239085 := by
    have h1 := Subgroup.card_mul_index S
    rw [hcard, hG] at h1
    omega
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ :=
    CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨hS, by rw [hidx]; decide⟩
  have hX := CFSG.KD.M24Dc.card_of_sylow_le hT hSX hne
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with h | h | h | h | h | h | h <;> rw [h] at h5 h9 <;> omega

end Certificates

end

end
