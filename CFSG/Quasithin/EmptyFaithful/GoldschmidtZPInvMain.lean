module

public import CFSG.Quasithin.EmptyFaithful.S151S7A
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvMathieu
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvJ2He
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvTits
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvU33
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvD4

public section

namespace CFSG.Quasithin

theorem input15122ZPUniqueInv_holds :
    Input15122ZPUniqueInv := by
  intro Q _ _ P hP hPi h
  have hz : ZPInv.ZPUniq Q := by
    rcases h with (h | h | h) | h
    · exact ZPInv.zpUniq_u33 h
    · exact ZPInv.zpUniq_tits h
    · exact ZPInv.zpUniq_3d4 h
    · unfold SporadicSix at h
      rcases h with h | h | h | h | h | h
      · obtain ⟨e⟩ := h
        exact ZPInv.ZPUniq.of_mulEquiv e ZPInv.zpUniq_j2
      · obtain ⟨e⟩ := h
        exact ZPInv.ZPUniq.of_mulEquiv e ZPInv.zpUniq_he
      · obtain ⟨e⟩ := h
        refine ZPInv.ZPUniq.of_mulEquiv ?_ ZPInv.zpUniq_m12
        exact e
      · obtain ⟨e⟩ := h
        refine ZPInv.ZPUniq.of_mulEquiv ?_ ZPInv.zpUniq_m22
        exact e
      · obtain ⟨e⟩ := h
        refine ZPInv.ZPUniq.of_mulEquiv ?_ ZPInv.zpUniq_m23
        exact e
      · obtain ⟨e⟩ := h
        refine ZPInv.ZPUniq.of_mulEquiv ?_ ZPInv.zpUniq_m24
        exact e
  exact ⟨hz.1, hz.2 P hP hPi⟩

end CFSG.Quasithin
