module

public import CFSG.Quasithin.Recognition.CertU33AutEnum

public section

namespace CFSG.Quasithin

open CFSG.Sporadic.Bridge

theorem u33_ab_cover_0 : ∀ i₁ < 32, ∀ i₂ < 32,
    compL (compL (u33TelTab.getD i₁ []) (u33DTab.getD 0 [])) (u33TelTab.getD i₂ []) ∈
      u33ABTab := by
  decide +kernel

theorem u33_ab_cover_1 : ∀ i₁ < 32, ∀ i₂ < 32,
    compL (compL (u33TelTab.getD i₁ []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ∈
      u33ABTab := by
  decide +kernel

theorem u33_ab_cover_2 : ∀ i₁ < 32, ∀ i₂ < 32,
    compL (compL (u33TelTab.getD i₁ []) (u33DTab.getD 2 [])) (u33TelTab.getD i₂ []) ∈
      u33ABTab := by
  decide +kernel

theorem u33_ab_cover : ∀ j ∈ [0, 1, 2], ∀ i₁ < 32, ∀ i₂ < 32,
    compL (compL (u33TelTab.getD i₁ []) (u33DTab.getD j [])) (u33TelTab.getD i₂ []) ∈
      u33ABTab := by
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  exacts [u33_ab_cover_0, u33_ab_cover_1, u33_ab_cover_2]

end CFSG.Quasithin
