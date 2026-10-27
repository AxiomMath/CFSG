module

public import CFSG.Quasithin.Recognition.St84.G24Model
public import Certificates.Data.G24IdentWit

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Fischer CFSG.Quasithin.G2U


structure ChevFacts : Prop where
  toGL_injective : Function.Injective toGL
  toGL_agY : ∀ w : List (Fin 6 × Bool), (toGL (agY w) : Matrix (Fin 14) (Fin 14) F4) =
    CFSG.LieType.Multipliers.G24.toMat 14 (CFSG.LieType.Multipliers.G24.wordArr w)
  agY_append : ∀ u v : List (Fin 6 × Bool), agY (u ++ v) = agY u * agY v
  agY_invW : ∀ w : List (Fin 6 × Bool), agY (CFSG.Quasithin.St84.G24Wit.invW w) = (agY w)⁻¹
  xY_eq_agY : ∀ (i : Fin 2) (c : F4),
    xY i c = agY (CFSG.LieType.Multipliers.G24.genWordX (ix i) c)
  yY_eq_agY : ∀ (i : Fin 2) (c : F4),
    yY i c = agY (CFSG.LieType.Multipliers.G24.genWordY (ix i) c)
  nY_eq : ∀ i : Fin 2, nY i = xY i 1 * yY i 1 * xY i 1
  hY_eq : ∀ i : Fin 2, hY i = xY i F4.ω * yY i (F4.ω * F4.ω) * xY i F4.ω * nY i
  xY_mem_B0 : ∀ (i : Fin 2) (c : F4), xY i c ∈ B0
  hY_mem_B0 : ∀ i : Fin 2, hY i ∈ B0
  nY_one_mem_M1 : nY 1 ∈ M1
  nY_zero_mem_M2 : nY 0 ∈ M2
  T0_le_B0 : T0 ≤ B0
  B0_le_M1 : B0 ≤ M1
  B0_le_M2 : B0 ≤ M2
  M1_le_of : ∀ {H : Subgroup Y}, B0 ≤ H → nY 1 ∈ H → M1 ≤ H
  M2_le_of : ∀ {H : Subgroup Y}, B0 ≤ H → nY 0 ∈ H → M2 ≤ H
  inf_M1_M2 : M1 ⊓ M2 = B0
  normalizer_T0 : Subgroup.normalizer (T0 : Set Y) = B0
  card_T0 : Nat.card T0 = 4096
  card_B0 : Nat.card B0 = 36864
  le_T0_of_isPGroup : ∀ {N : Subgroup Y}, N ≤ B0 → IsPGroup 2 N → N ≤ T0
  isSylowTwoOf_T0_M1 : CFSG.QuasithinUnique.IsSylowTwoOf T0 M1
  isSylowTwoOf_T0_M2 : CFSG.QuasithinUnique.IsSylowTwoOf T0 M2
  card_pCoreOf_M1 : Nat.card (CFSG.Open.pCoreOf 2 M1) = 1024
  card_pCoreOf_M2 : Nat.card (CFSG.Open.pCoreOf 2 M2) = 1024

end CFSG.Quasithin.F112R.St84.G24M
