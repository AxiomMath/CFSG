module

public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsFix
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsPGL
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsG2

public section

namespace CFSG.StandardType

theorem ggTriD4ComponentsInput_holds :
    GGTriD4ComponentsInput := by
  intro n hn K _ _ hK _ σ hσ3 hσ Q hQ
  rcases ggTriD4_fixedShape hn K hK σ hσ3 hσ with
    ⟨k, _, _, hk, ⟨E⟩⟩ | ⟨hev, F, _, _, hF, ⟨E⟩⟩ | ⟨hodd, F, _, _, hF, ⟨E⟩⟩
  · obtain ⟨hZ, hM⟩ := ggTriD4_g2_clause hn hk E hQ
    exact ⟨hZ, Or.inl hM⟩
  · obtain ⟨hZ, hM⟩ := ggTriD4_pgl_clause hev hn hF E hQ
    exact ⟨hZ, Or.inr hM⟩
  · obtain ⟨hZ, hM⟩ := ggTriD4_pgu_clause hodd hF E hQ
    exact ⟨hZ, Or.inr hM⟩

end CFSG.StandardType
