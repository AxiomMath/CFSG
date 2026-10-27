module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuMain

public section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuType
  CFSG.Quasithin.H13.F431.F45

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA


theorem facts45L_twoF4_of_oct (hpoly : IsGenPolygon octGraph 8) {b₁ w₁₀ w₁₁ : Vtx}
    {Fg₁ : Set ↥TA} {L₁ : Finset ↥TA}
    (D₁ : LocalData ↥TA octGraph 8 (Sum.inl 0) b₁ w₁₀ w₁₁ Fg₁ L₁ 20480 1024 5)
    {b₂ w₂₀ w₂₁ : Vtx} {Fg₂ : Set ↥TA} {L₂ : Finset ↥TA}
    (D₂ : LocalData ↥TA octGraph 8 (Sum.inr 0) b₂ w₂₀ w₂₁ Fg₂ L₂ 12288 2048 3) :
    twoF4Setting.Facts45L := by
  have h00' : (0 : Fin 1755) ∈ titsLine (0 : Fin 2925) :=
    (RuType.J47.titsLine_mem_iff 0 0).2 RuType.J47.onLine_0_0
  have M₁ := modelBase_of_local hpoly.connected D₁
  have M₂ := modelBase_of_local hpoly.connected D₂
  have n1 := D₁.card_N
  have n2 := D₂.card_N
  exact facts45L_of_model (xdatum_oct h00') hpoly (by omega) (by omega) _ _ rfl rfl M₁ M₂

end CFSG.Quasithin.H13.F45Ru
