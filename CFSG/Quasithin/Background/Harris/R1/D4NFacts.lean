module

public import CFSG.Quasithin.Background.Harris.R1.D4Q2Aut
public import CFSG.Quasithin.Background.Harris.R1.D4VertModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocV

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.Quasithin.D4Hex CFSG.LargeExtraspecial.S63 CFSG.CosetTable

structure D4NFacts :
    Prop where
  y1_mem : y1D ∈ d4B
  y2_mem : y2D ∈ d4B
  ze_mem : zeD ∈ d4B
  r0_mem : r0D ∈ d4B
  s0_mem : s0D ∈ d4N
  closure_B : Subgroup.closure ({y1D, y2D, zeD, r0D} : Set D) = d4B
  card_B : Nat.card d4B = 28672
  normalizer_U : Subgroup.normalizer (d4U : Set D) = d4B
  U_le_H : d4U ≤ d4H
  V_le_H : d4V ≤ d4H
  cent : d4U ⊓ Subgroup.centralizer (d4V : Set D) = Q2
  center : ∀ q ∈ Q2, (∀ q' ∈ Q2, q * q' = q' * q) → q ∈ d4V
  kc_cent : ∀ k ∈ Kc, (∀ q ∈ Q2, k * q = q * k) → k = 1
  range_n : nModel.range = d4N
  inj_n : Function.Injective nModel

end CFSG.Quasithin.Background.Harris.R1.D4Vert
