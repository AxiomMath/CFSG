module

public import CFSG.Quasithin.Recognition.CertU33DcInputs

public section

open CFSG.Quasithin CFSG.CosetTable CFSG.Sporadic.Bridge

namespace CertificateChecks.Batch19953

open CFSG.Quasithin CFSG.CosetTable CFSG.Sporadic.Bridge

private theorem u33_genTab_rep_0 : ∀ k < 5, RepL (u33GenTab.getD k []) (u33GenP k) := by
  decide +kernel

private theorem u33_genInvTab_rep_1 : ∀ k < 5, RepL (u33GenInvTab.getD k []) (u33GenP k)⁻¹ := by
  decide +kernel

private theorem u33T_telTab_2 : ∀ i < 32, u33TelTab.getD i [] = u33WordL (u33TelW i) := by
  decide +kernel

private theorem u33T_dTab_3 : ∀ j < 14, u33DTab.getD j [] = u33WordL (u33DW j) := by
  decide +kernel

private theorem u33T_dInvTab_4 : ∀ j < 14, u33DInvTab.getD j [] = u33WordL (u33InvW (u33DW j)) := by
  decide +kernel

private theorem u33P_letters_5 :
    (∀ i < 32, ∀ l ∈ u33TelW i, l.1 < 3) ∧ (∀ j < 14, ∀ l ∈ u33DW j, l.1 < 5) ∧
    (∀ l ∈ u33DW 1, l.1 < 4) ∧ (∀ l ∈ u33DW 2, l.1 = 4) := by
  decide +kernel

private theorem u33T_orders_6 :
    (List.replicate 4 (u33GenTab.getD 0 [])).foldr compL (List.range 28) = List.range 28 ∧
    (List.replicate 4 (u33GenTab.getD 1 [])).foldr compL (List.range 28) = List.range 28 ∧
    (List.replicate 2 (u33GenTab.getD 2 [])).foldr compL (List.range 28) = List.range 28 ∧
    (List.replicate 3 (u33GenTab.getD 3 [])).foldr compL (List.range 28) = List.range 28 ∧
    (List.replicate 3 (u33GenTab.getD 4 [])).foldr compL (List.range 28) = List.range 28 := by
  decide +kernel

private theorem u33T_next_7 : ∀ i < 32, ∀ g < 3,
    compL (u33TelTab.getD i []) (u33GenTab.getD g []) = u33TelTab.getD (u33Nxt i g % 32) [] := by
  decide +kernel

private theorem u33T_decX_0_8 : ∀ i < 32,
    compL (compL (u33DTab.getD 0 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 0 i % 32) [])
        (u33DTab.getD (u33DecXk 0 i % 14) [])) (u33TelTab.getD (u33DecXb 0 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_1_9 : ∀ i < 32,
    compL (compL (u33DTab.getD 1 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 1 i % 32) [])
        (u33DTab.getD (u33DecXk 1 i % 14) [])) (u33TelTab.getD (u33DecXb 1 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_2_10 : ∀ i < 32,
    compL (compL (u33DTab.getD 2 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 2 i % 32) [])
        (u33DTab.getD (u33DecXk 2 i % 14) [])) (u33TelTab.getD (u33DecXb 2 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_3_11 : ∀ i < 32,
    compL (compL (u33DTab.getD 3 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 3 i % 32) [])
        (u33DTab.getD (u33DecXk 3 i % 14) [])) (u33TelTab.getD (u33DecXb 3 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_4_12 : ∀ i < 32,
    compL (compL (u33DTab.getD 4 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 4 i % 32) [])
        (u33DTab.getD (u33DecXk 4 i % 14) [])) (u33TelTab.getD (u33DecXb 4 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_5_13 : ∀ i < 32,
    compL (compL (u33DTab.getD 5 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 5 i % 32) [])
        (u33DTab.getD (u33DecXk 5 i % 14) [])) (u33TelTab.getD (u33DecXb 5 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_6_14 : ∀ i < 32,
    compL (compL (u33DTab.getD 6 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 6 i % 32) [])
        (u33DTab.getD (u33DecXk 6 i % 14) [])) (u33TelTab.getD (u33DecXb 6 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_7_15 : ∀ i < 32,
    compL (compL (u33DTab.getD 7 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 7 i % 32) [])
        (u33DTab.getD (u33DecXk 7 i % 14) [])) (u33TelTab.getD (u33DecXb 7 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_8_16 : ∀ i < 32,
    compL (compL (u33DTab.getD 8 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 8 i % 32) [])
        (u33DTab.getD (u33DecXk 8 i % 14) [])) (u33TelTab.getD (u33DecXb 8 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_9_17 : ∀ i < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 9 i % 32) [])
        (u33DTab.getD (u33DecXk 9 i % 14) [])) (u33TelTab.getD (u33DecXb 9 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_10_18 : ∀ i < 32,
    compL (compL (u33DTab.getD 10 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 10 i % 32) [])
        (u33DTab.getD (u33DecXk 10 i % 14) [])) (u33TelTab.getD (u33DecXb 10 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_11_19 : ∀ i < 32,
    compL (compL (u33DTab.getD 11 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 11 i % 32) [])
        (u33DTab.getD (u33DecXk 11 i % 14) [])) (u33TelTab.getD (u33DecXb 11 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_12_20 : ∀ i < 32,
    compL (compL (u33DTab.getD 12 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 12 i % 32) [])
        (u33DTab.getD (u33DecXk 12 i % 14) [])) (u33TelTab.getD (u33DecXb 12 i % 32) []) := by
  decide +kernel

private theorem u33T_decX_13_21 : ∀ i < 32,
    compL (compL (u33DTab.getD 13 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 13 i % 32) [])
        (u33DTab.getD (u33DecXk 13 i % 14) [])) (u33TelTab.getD (u33DecXb 13 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_0_22 : ∀ i < 32,
    compL (compL (u33DTab.getD 0 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 0 i % 32) [])
        (u33DTab.getD (u33DecYk 0 i % 14) [])) (u33TelTab.getD (u33DecYb 0 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_1_23 : ∀ i < 32,
    compL (compL (u33DTab.getD 1 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 1 i % 32) [])
        (u33DTab.getD (u33DecYk 1 i % 14) [])) (u33TelTab.getD (u33DecYb 1 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_2_24 : ∀ i < 32,
    compL (compL (u33DTab.getD 2 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 2 i % 32) [])
        (u33DTab.getD (u33DecYk 2 i % 14) [])) (u33TelTab.getD (u33DecYb 2 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_3_25 : ∀ i < 32,
    compL (compL (u33DTab.getD 3 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 3 i % 32) [])
        (u33DTab.getD (u33DecYk 3 i % 14) [])) (u33TelTab.getD (u33DecYb 3 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_4_26 : ∀ i < 32,
    compL (compL (u33DTab.getD 4 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 4 i % 32) [])
        (u33DTab.getD (u33DecYk 4 i % 14) [])) (u33TelTab.getD (u33DecYb 4 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_5_27 : ∀ i < 32,
    compL (compL (u33DTab.getD 5 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 5 i % 32) [])
        (u33DTab.getD (u33DecYk 5 i % 14) [])) (u33TelTab.getD (u33DecYb 5 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_6_28 : ∀ i < 32,
    compL (compL (u33DTab.getD 6 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 6 i % 32) [])
        (u33DTab.getD (u33DecYk 6 i % 14) [])) (u33TelTab.getD (u33DecYb 6 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_7_29 : ∀ i < 32,
    compL (compL (u33DTab.getD 7 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 7 i % 32) [])
        (u33DTab.getD (u33DecYk 7 i % 14) [])) (u33TelTab.getD (u33DecYb 7 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_8_30 : ∀ i < 32,
    compL (compL (u33DTab.getD 8 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 8 i % 32) [])
        (u33DTab.getD (u33DecYk 8 i % 14) [])) (u33TelTab.getD (u33DecYb 8 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_9_31 : ∀ i < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 9 i % 32) [])
        (u33DTab.getD (u33DecYk 9 i % 14) [])) (u33TelTab.getD (u33DecYb 9 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_10_32 : ∀ i < 32,
    compL (compL (u33DTab.getD 10 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 10 i % 32) [])
        (u33DTab.getD (u33DecYk 10 i % 14) [])) (u33TelTab.getD (u33DecYb 10 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_11_33 : ∀ i < 32,
    compL (compL (u33DTab.getD 11 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 11 i % 32) [])
        (u33DTab.getD (u33DecYk 11 i % 14) [])) (u33TelTab.getD (u33DecYb 11 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_12_34 : ∀ i < 32,
    compL (compL (u33DTab.getD 12 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 12 i % 32) [])
        (u33DTab.getD (u33DecYk 12 i % 14) [])) (u33TelTab.getD (u33DecYb 12 i % 32) []) := by
  decide +kernel

private theorem u33T_decY_13_35 : ∀ i < 32,
    compL (compL (u33DTab.getD 13 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 13 i % 32) [])
        (u33DTab.getD (u33DecYk 13 i % 14) [])) (u33TelTab.getD (u33DecYb 13 i % 32) []) := by
  decide +kernel

private theorem u33P_decXA_36 :
    ∀ j < 2, ∀ i < 32, u33DecXk j i % 14 = 0 ∨ u33DecXk j i % 14 = 1 := by
  decide +kernel

private theorem u33P_decYB_37 : ∀ j < 3, j ≠ 1 → ∀ i < 32,
    u33DecYk j i % 14 = 0 ∨ u33DecYk j i % 14 = 2 := by
  decide +kernel

private theorem u33T_mem_38 : ∀ j < 14,
    (u33MemX.getD j "" ≠ "" →
      u33WordL4 j (u33W4 (u33MemX.getD j "")) = u33GenTab.getD 3 []) ∧
    (u33MemY.getD j "" ≠ "" →
      u33WordL4 j (u33W4 (u33MemY.getD j "")) = u33GenTab.getD 4 []) := by
  decide +kernel

private theorem u33T_memLetters_39 : ∀ j < 14,
    (∀ l ∈ u33W4 (u33MemX.getD j ""), l.1 < 4) ∧ (∀ l ∈ u33W4 (u33MemY.getD j ""), l.1 < 4) := by
  decide +kernel

private theorem u33P_mem_ne_40 : u33MemX.getD 1 "" ≠ "" ∧ u33MemY.getD 2 "" ≠ "" ∧
    ∀ j : Fin 14, 3 ≤ j.val → u33MemX.getD j "" ≠ "" ∧ u33MemY.getD j "" ≠ "" := by
  decide +kernel

private theorem u33T_sep3_0_41 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 0 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_1_42 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 1 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_2_43 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 2 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_3_44 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 3 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_4_45 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 4 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_5_46 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 5 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_6_47 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 6 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_7_48 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 7 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_8_49 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 8 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_9_50 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 9 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_10_51 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 10 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_11_52 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 11 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_12_53 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 12 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_13_54 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 13 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_14_55 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 14 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_15_56 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 15 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_16_57 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 16 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_17_58 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 17 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_18_59 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 18 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_19_60 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 19 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_20_61 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 20 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_21_62 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 21 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_22_63 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 22 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_23_64 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 23 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_24_65 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 24 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_25_66 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 25 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_26_67 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 26 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_27_68 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 27 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_28_69 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 28 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_29_70 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 29 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_30_71 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 30 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep3_31_72 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 31 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_sep_a_73 : ∀ i < 32, u33TelTab.getD i [] ≠ u33DTab.getD 1 [] := by
  decide +kernel

private theorem u33T_sep_b_74 : ∀ i < 32, u33TelTab.getD i [] ≠ u33DTab.getD 2 [] := by
  decide +kernel

private theorem u33T_inj_75 :
    ∀ i < 32, ∀ j < 32, u33TelTab.getD i [] = u33TelTab.getD j [] → i = j := by
  decide +kernel

private theorem u33_gword_eq_76 : u33W u33GWord = u33DW 9 := by
  decide +kernel

private theorem u33T_g_0_77 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 0 [] → u33TelTab.getD 0 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_1_78 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 1 [] → u33TelTab.getD 1 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_2_79 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 2 [] → u33TelTab.getD 2 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_3_80 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 3 [] → u33TelTab.getD 3 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_4_81 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 4 [] → u33TelTab.getD 4 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_5_82 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 5 [] → u33TelTab.getD 5 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_6_83 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 6 [] → u33TelTab.getD 6 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_7_84 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 7 [] → u33TelTab.getD 7 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_8_85 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 8 [] → u33TelTab.getD 8 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_9_86 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 9 [] → u33TelTab.getD 9 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_10_87 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 10 [] → u33TelTab.getD 10 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_11_88 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 11 [] → u33TelTab.getD 11 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_12_89 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 12 [] → u33TelTab.getD 12 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_13_90 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 13 [] → u33TelTab.getD 13 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_14_91 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 14 [] → u33TelTab.getD 14 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_15_92 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 15 [] → u33TelTab.getD 15 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_16_93 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 16 [] → u33TelTab.getD 16 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_17_94 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 17 [] → u33TelTab.getD 17 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_18_95 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 18 [] → u33TelTab.getD 18 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_19_96 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 19 [] → u33TelTab.getD 19 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_20_97 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 20 [] → u33TelTab.getD 20 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_21_98 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 21 [] → u33TelTab.getD 21 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_22_99 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 22 [] → u33TelTab.getD 22 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_23_100 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 23 [] → u33TelTab.getD 23 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_24_101 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 24 [] → u33TelTab.getD 24 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_25_102 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 25 [] → u33TelTab.getD 25 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_26_103 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 26 [] → u33TelTab.getD 26 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_27_104 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 27 [] → u33TelTab.getD 27 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_28_105 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 28 [] → u33TelTab.getD 28 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_29_106 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 29 [] → u33TelTab.getD 29 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_30_107 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 30 [] → u33TelTab.getD 30 [] = List.range 28 := by
  decide +kernel

private theorem u33T_g_31_108 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 31 [] → u33TelTab.getD 31 [] = List.range 28 := by
  decide +kernel

private theorem u33T_xy_109 : u33GenTab.getD 0 [] ≠ List.range 28 ∧
    (∀ i' < 32, compL (compL (u33GenTab.getD 3 []) (u33TelTab.getD 5 []))
      (u33GenInvTab.getD 3 []) ≠ u33TelTab.getD i' []) ∧
    (∀ i' < 32, compL (compL (u33GenTab.getD 4 []) (u33TelTab.getD 1 []))
      (u33GenInvTab.getD 4 []) ≠ u33TelTab.getD i' []) := by
  decide +kernel

private theorem u33T_V_110 : ∀ k < 4, ∀ i < 3,
    (∃ j < 3, compL (compL (u33GenTab.getD k []) (u33VTab i)) (u33GenInvTab.getD k []) =
      u33VTab j) ∧
    (∃ j < 3, compL (compL (u33GenInvTab.getD k []) (u33VTab i)) (u33GenTab.getD k []) =
      u33VTab j) := by
  decide +kernel

private theorem u33T_A2_111 : u33A2Tab ≠ List.range 28 ∧ u33ZTab ≠ List.range 28 := by
  decide +kernel

private theorem u33T_Z_112 : ∀ k < 5, k ≠ 3 →
    compL (compL (u33GenTab.getD k []) u33ZTab) (u33GenInvTab.getD k []) = u33ZTab ∧
    compL (compL (u33GenInvTab.getD k []) u33ZTab) (u33GenTab.getD k []) = u33ZTab := by
  decide +kernel

end CertificateChecks.Batch19953

namespace Certificates

open CertificateChecks

open CFSG.Quasithin CFSG.CosetTable CFSG.Sporadic.Bridge in
theorem certificate19953 : ((∀ k < 5, RepL (u33GenTab.getD k []) (u33GenP k))
      ∧ (∀ k < 5, RepL (u33GenInvTab.getD k []) (u33GenP k)⁻¹)
      ∧ (∀ i < 32, u33TelTab.getD i [] = u33WordL (u33TelW i))
      ∧ (∀ j < 14, u33DTab.getD j [] = u33WordL (u33DW j))
      ∧ (∀ j < 14, u33DInvTab.getD j [] = u33WordL (u33InvW (u33DW j)))
      ∧ ((∀ i < 32, ∀ l ∈ u33TelW i, l.1 < 3) ∧ (∀ j < 14, ∀ l ∈ u33DW j, l.1 < 5) ∧
          (∀ l ∈ u33DW 1, l.1 < 4) ∧ (∀ l ∈ u33DW 2, l.1 = 4))
      ∧ ((List.replicate 4 (u33GenTab.getD 0 [])).foldr compL (List.range 28) = List.range 28 ∧
          (List.replicate 4 (u33GenTab.getD 1 [])).foldr compL (List.range 28) = List.range 28 ∧
          (List.replicate 2 (u33GenTab.getD 2 [])).foldr compL (List.range 28) = List.range 28 ∧
          (List.replicate 3 (u33GenTab.getD 3 [])).foldr compL (List.range 28) = List.range 28 ∧
          (List.replicate 3 (u33GenTab.getD 4 [])).foldr compL (List.range 28) = List.range 28)
      ∧ (∀ i < 32, ∀ g < 3,
          compL (u33TelTab.getD i []) (u33GenTab.getD g []) = u33TelTab.getD (u33Nxt i g % 32) [])
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 0 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 0 i % 32) [])
              (u33DTab.getD (u33DecXk 0 i % 14) [])) (u33TelTab.getD (u33DecXb 0 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 1 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 1 i % 32) [])
              (u33DTab.getD (u33DecXk 1 i % 14) [])) (u33TelTab.getD (u33DecXb 1 i % 32) [])))
    ∧ ((∀ i < 32,
          compL (compL (u33DTab.getD 2 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 2 i % 32) [])
              (u33DTab.getD (u33DecXk 2 i % 14) [])) (u33TelTab.getD (u33DecXb 2 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 3 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 3 i % 32) [])
              (u33DTab.getD (u33DecXk 3 i % 14) [])) (u33TelTab.getD (u33DecXb 3 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 4 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 4 i % 32) [])
              (u33DTab.getD (u33DecXk 4 i % 14) [])) (u33TelTab.getD (u33DecXb 4 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 5 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 5 i % 32) [])
              (u33DTab.getD (u33DecXk 5 i % 14) [])) (u33TelTab.getD (u33DecXb 5 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 6 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 6 i % 32) [])
              (u33DTab.getD (u33DecXk 6 i % 14) [])) (u33TelTab.getD (u33DecXb 6 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 7 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 7 i % 32) [])
              (u33DTab.getD (u33DecXk 7 i % 14) [])) (u33TelTab.getD (u33DecXb 7 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 8 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 8 i % 32) [])
              (u33DTab.getD (u33DecXk 8 i % 14) [])) (u33TelTab.getD (u33DecXb 8 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 9 i % 32) [])
              (u33DTab.getD (u33DecXk 9 i % 14) [])) (u33TelTab.getD (u33DecXb 9 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 10 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 10 i % 32) [])
              (u33DTab.getD (u33DecXk 10 i % 14) [])) (u33TelTab.getD (u33DecXb 10 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 11 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 11 i % 32) [])
              (u33DTab.getD (u33DecXk 11 i % 14) [])) (u33TelTab.getD (u33DecXb 11 i % 32) [])))
    ∧ ((∀ i < 32,
          compL (compL (u33DTab.getD 12 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 12 i % 32) [])
              (u33DTab.getD (u33DecXk 12 i % 14) [])) (u33TelTab.getD (u33DecXb 12 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 13 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
            compL (compL (u33TelTab.getD (u33DecXa 13 i % 32) [])
              (u33DTab.getD (u33DecXk 13 i % 14) [])) (u33TelTab.getD (u33DecXb 13 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 0 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 0 i % 32) [])
              (u33DTab.getD (u33DecYk 0 i % 14) [])) (u33TelTab.getD (u33DecYb 0 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 1 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 1 i % 32) [])
              (u33DTab.getD (u33DecYk 1 i % 14) [])) (u33TelTab.getD (u33DecYb 1 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 2 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 2 i % 32) [])
              (u33DTab.getD (u33DecYk 2 i % 14) [])) (u33TelTab.getD (u33DecYb 2 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 3 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 3 i % 32) [])
              (u33DTab.getD (u33DecYk 3 i % 14) [])) (u33TelTab.getD (u33DecYb 3 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 4 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 4 i % 32) [])
              (u33DTab.getD (u33DecYk 4 i % 14) [])) (u33TelTab.getD (u33DecYb 4 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 5 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 5 i % 32) [])
              (u33DTab.getD (u33DecYk 5 i % 14) [])) (u33TelTab.getD (u33DecYb 5 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 6 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 6 i % 32) [])
              (u33DTab.getD (u33DecYk 6 i % 14) [])) (u33TelTab.getD (u33DecYb 6 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 7 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 7 i % 32) [])
              (u33DTab.getD (u33DecYk 7 i % 14) [])) (u33TelTab.getD (u33DecYb 7 i % 32) [])))
    ∧ ((∀ i < 32,
          compL (compL (u33DTab.getD 8 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 8 i % 32) [])
              (u33DTab.getD (u33DecYk 8 i % 14) [])) (u33TelTab.getD (u33DecYb 8 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 9 i % 32) [])
              (u33DTab.getD (u33DecYk 9 i % 14) [])) (u33TelTab.getD (u33DecYb 9 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 10 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 10 i % 32) [])
              (u33DTab.getD (u33DecYk 10 i % 14) [])) (u33TelTab.getD (u33DecYb 10 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 11 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 11 i % 32) [])
              (u33DTab.getD (u33DecYk 11 i % 14) [])) (u33TelTab.getD (u33DecYb 11 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 12 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 12 i % 32) [])
              (u33DTab.getD (u33DecYk 12 i % 14) [])) (u33TelTab.getD (u33DecYb 12 i % 32) []))
      ∧ (∀ i < 32,
          compL (compL (u33DTab.getD 13 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
            compL (compL (u33TelTab.getD (u33DecYa 13 i % 32) [])
              (u33DTab.getD (u33DecYk 13 i % 14) [])) (u33TelTab.getD (u33DecYb 13 i % 32) []))
      ∧ (∀ j < 2, ∀ i < 32, u33DecXk j i % 14 = 0 ∨ u33DecXk j i % 14 = 1)
      ∧ (∀ j < 3, j ≠ 1 → ∀ i < 32,
          u33DecYk j i % 14 = 0 ∨ u33DecYk j i % 14 = 2)
      ∧ (∀ j < 14,
          (u33MemX.getD j "" ≠ "" →
            u33WordL4 j (u33W4 (u33MemX.getD j "")) = u33GenTab.getD 3 []) ∧
          (u33MemY.getD j "" ≠ "" →
            u33WordL4 j (u33W4 (u33MemY.getD j "")) = u33GenTab.getD 4 []))
      ∧ (∀ j < 14,
          (∀ l ∈ u33W4 (u33MemX.getD j ""), l.1 < 4) ∧ (∀ l ∈ u33W4 (u33MemY.getD j ""), l.1 < 4)))
    ∧ ((u33MemX.getD 1 "" ≠ "" ∧ u33MemY.getD 2 "" ≠ "" ∧
          ∀ j : Fin 14, 3 ≤ j.val → u33MemX.getD j "" ≠ "" ∧ u33MemY.getD j "" ≠ "")
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 0 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 1 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 2 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 3 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 4 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 5 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 6 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 7 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 8 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 []))
    ∧ ((∀ i₂ < 32,
          compL (compL (u33TelTab.getD 9 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 10 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 11 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 12 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 13 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 14 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 15 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 16 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 17 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 18 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 []))
    ∧ ((∀ i₂ < 32,
          compL (compL (u33TelTab.getD 19 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 20 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 21 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 22 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 23 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 24 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 25 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 26 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 27 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 28 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 []))
    ∧ ((∀ i₂ < 32,
          compL (compL (u33TelTab.getD 29 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 30 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i₂ < 32,
          compL (compL (u33TelTab.getD 31 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
            u33DTab.getD 2 [])
      ∧ (∀ i < 32, u33TelTab.getD i [] ≠ u33DTab.getD 1 [])
      ∧ (∀ i < 32, u33TelTab.getD i [] ≠ u33DTab.getD 2 [])
      ∧ (∀ i < 32, ∀ j < 32, u33TelTab.getD i [] = u33TelTab.getD j [] → i = j)
      ∧ (u33W u33GWord = u33DW 9)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 0 [] → u33TelTab.getD 0 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 1 [] → u33TelTab.getD 1 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 2 [] → u33TelTab.getD 2 [] = List.range 28))
    ∧ ((∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 3 [] → u33TelTab.getD 3 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 4 [] → u33TelTab.getD 4 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 5 [] → u33TelTab.getD 5 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 6 [] → u33TelTab.getD 6 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 7 [] → u33TelTab.getD 7 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 8 [] → u33TelTab.getD 8 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 9 [] → u33TelTab.getD 9 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 10 [] → u33TelTab.getD 10 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 11 [] → u33TelTab.getD 11 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 12 [] → u33TelTab.getD 12 [] = List.range 28))
    ∧ ((∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 13 [] → u33TelTab.getD 13 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 14 [] → u33TelTab.getD 14 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 15 [] → u33TelTab.getD 15 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 16 [] → u33TelTab.getD 16 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 17 [] → u33TelTab.getD 17 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 18 [] → u33TelTab.getD 18 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 19 [] → u33TelTab.getD 19 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 20 [] → u33TelTab.getD 20 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 21 [] → u33TelTab.getD 21 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 22 [] → u33TelTab.getD 22 [] = List.range 28))
    ∧ ((∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 23 [] → u33TelTab.getD 23 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 24 [] → u33TelTab.getD 24 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 25 [] → u33TelTab.getD 25 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 26 [] → u33TelTab.getD 26 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 27 [] → u33TelTab.getD 27 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 28 [] → u33TelTab.getD 28 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 29 [] → u33TelTab.getD 29 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 30 [] → u33TelTab.getD 30 [] = List.range 28)
      ∧ (∀ i' < 32,
          compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
            u33TelTab.getD 31 [] → u33TelTab.getD 31 [] = List.range 28)
      ∧ (u33GenTab.getD 0 [] ≠ List.range 28 ∧
          (∀ i' < 32, compL (compL (u33GenTab.getD 3 []) (u33TelTab.getD 5 []))
            (u33GenInvTab.getD 3 []) ≠ u33TelTab.getD i' []) ∧
          (∀ i' < 32, compL (compL (u33GenTab.getD 4 []) (u33TelTab.getD 1 []))
            (u33GenInvTab.getD 4 []) ≠ u33TelTab.getD i' [])))
    ∧ ((∀ k < 4, ∀ i < 3,
          (∃ j < 3, compL (compL (u33GenTab.getD k []) (u33VTab i)) (u33GenInvTab.getD k []) =
            u33VTab j) ∧
          (∃ j < 3, compL (compL (u33GenInvTab.getD k []) (u33VTab i)) (u33GenTab.getD k []) =
            u33VTab j))
      ∧ (u33A2Tab ≠ List.range 28 ∧ u33ZTab ≠ List.range 28)
      ∧ (∀ k < 5, k ≠ 3 →
          compL (compL (u33GenTab.getD k []) u33ZTab) (u33GenInvTab.getD k []) = u33ZTab ∧
          compL (compL (u33GenInvTab.getD k []) u33ZTab) (u33GenTab.getD k []) = u33ZTab)) := by
  exact ⟨
    ⟨@CertificateChecks.Batch19953.u33_genTab_rep_0, @CertificateChecks.Batch19953.u33_genInvTab_rep_1, @CertificateChecks.Batch19953.u33T_telTab_2,
      @CertificateChecks.Batch19953.u33T_dTab_3, @CertificateChecks.Batch19953.u33T_dInvTab_4, @CertificateChecks.Batch19953.u33P_letters_5,
      @CertificateChecks.Batch19953.u33T_orders_6, @CertificateChecks.Batch19953.u33T_next_7, @CertificateChecks.Batch19953.u33T_decX_0_8,
      @CertificateChecks.Batch19953.u33T_decX_1_9⟩,
    ⟨@CertificateChecks.Batch19953.u33T_decX_2_10, @CertificateChecks.Batch19953.u33T_decX_3_11, @CertificateChecks.Batch19953.u33T_decX_4_12,
      @CertificateChecks.Batch19953.u33T_decX_5_13, @CertificateChecks.Batch19953.u33T_decX_6_14, @CertificateChecks.Batch19953.u33T_decX_7_15,
      @CertificateChecks.Batch19953.u33T_decX_8_16, @CertificateChecks.Batch19953.u33T_decX_9_17, @CertificateChecks.Batch19953.u33T_decX_10_18,
      @CertificateChecks.Batch19953.u33T_decX_11_19⟩,
    ⟨@CertificateChecks.Batch19953.u33T_decX_12_20, @CertificateChecks.Batch19953.u33T_decX_13_21, @CertificateChecks.Batch19953.u33T_decY_0_22,
      @CertificateChecks.Batch19953.u33T_decY_1_23, @CertificateChecks.Batch19953.u33T_decY_2_24, @CertificateChecks.Batch19953.u33T_decY_3_25,
      @CertificateChecks.Batch19953.u33T_decY_4_26, @CertificateChecks.Batch19953.u33T_decY_5_27, @CertificateChecks.Batch19953.u33T_decY_6_28,
      @CertificateChecks.Batch19953.u33T_decY_7_29⟩,
    ⟨@CertificateChecks.Batch19953.u33T_decY_8_30, @CertificateChecks.Batch19953.u33T_decY_9_31, @CertificateChecks.Batch19953.u33T_decY_10_32,
      @CertificateChecks.Batch19953.u33T_decY_11_33, @CertificateChecks.Batch19953.u33T_decY_12_34, @CertificateChecks.Batch19953.u33T_decY_13_35,
      @CertificateChecks.Batch19953.u33P_decXA_36, @CertificateChecks.Batch19953.u33P_decYB_37, @CertificateChecks.Batch19953.u33T_mem_38,
      @CertificateChecks.Batch19953.u33T_memLetters_39⟩,
    ⟨@CertificateChecks.Batch19953.u33P_mem_ne_40, @CertificateChecks.Batch19953.u33T_sep3_0_41, @CertificateChecks.Batch19953.u33T_sep3_1_42,
      @CertificateChecks.Batch19953.u33T_sep3_2_43, @CertificateChecks.Batch19953.u33T_sep3_3_44, @CertificateChecks.Batch19953.u33T_sep3_4_45,
      @CertificateChecks.Batch19953.u33T_sep3_5_46, @CertificateChecks.Batch19953.u33T_sep3_6_47, @CertificateChecks.Batch19953.u33T_sep3_7_48,
      @CertificateChecks.Batch19953.u33T_sep3_8_49⟩,
    ⟨@CertificateChecks.Batch19953.u33T_sep3_9_50, @CertificateChecks.Batch19953.u33T_sep3_10_51, @CertificateChecks.Batch19953.u33T_sep3_11_52,
      @CertificateChecks.Batch19953.u33T_sep3_12_53, @CertificateChecks.Batch19953.u33T_sep3_13_54, @CertificateChecks.Batch19953.u33T_sep3_14_55,
      @CertificateChecks.Batch19953.u33T_sep3_15_56, @CertificateChecks.Batch19953.u33T_sep3_16_57, @CertificateChecks.Batch19953.u33T_sep3_17_58,
      @CertificateChecks.Batch19953.u33T_sep3_18_59⟩,
    ⟨@CertificateChecks.Batch19953.u33T_sep3_19_60, @CertificateChecks.Batch19953.u33T_sep3_20_61, @CertificateChecks.Batch19953.u33T_sep3_21_62,
      @CertificateChecks.Batch19953.u33T_sep3_22_63, @CertificateChecks.Batch19953.u33T_sep3_23_64, @CertificateChecks.Batch19953.u33T_sep3_24_65,
      @CertificateChecks.Batch19953.u33T_sep3_25_66, @CertificateChecks.Batch19953.u33T_sep3_26_67, @CertificateChecks.Batch19953.u33T_sep3_27_68,
      @CertificateChecks.Batch19953.u33T_sep3_28_69⟩,
    ⟨@CertificateChecks.Batch19953.u33T_sep3_29_70, @CertificateChecks.Batch19953.u33T_sep3_30_71, @CertificateChecks.Batch19953.u33T_sep3_31_72,
      @CertificateChecks.Batch19953.u33T_sep_a_73, @CertificateChecks.Batch19953.u33T_sep_b_74, @CertificateChecks.Batch19953.u33T_inj_75,
      @CertificateChecks.Batch19953.u33_gword_eq_76, @CertificateChecks.Batch19953.u33T_g_0_77, @CertificateChecks.Batch19953.u33T_g_1_78,
      @CertificateChecks.Batch19953.u33T_g_2_79⟩,
    ⟨@CertificateChecks.Batch19953.u33T_g_3_80, @CertificateChecks.Batch19953.u33T_g_4_81, @CertificateChecks.Batch19953.u33T_g_5_82,
      @CertificateChecks.Batch19953.u33T_g_6_83, @CertificateChecks.Batch19953.u33T_g_7_84, @CertificateChecks.Batch19953.u33T_g_8_85,
      @CertificateChecks.Batch19953.u33T_g_9_86, @CertificateChecks.Batch19953.u33T_g_10_87, @CertificateChecks.Batch19953.u33T_g_11_88,
      @CertificateChecks.Batch19953.u33T_g_12_89⟩,
    ⟨@CertificateChecks.Batch19953.u33T_g_13_90, @CertificateChecks.Batch19953.u33T_g_14_91, @CertificateChecks.Batch19953.u33T_g_15_92,
      @CertificateChecks.Batch19953.u33T_g_16_93, @CertificateChecks.Batch19953.u33T_g_17_94, @CertificateChecks.Batch19953.u33T_g_18_95,
      @CertificateChecks.Batch19953.u33T_g_19_96, @CertificateChecks.Batch19953.u33T_g_20_97, @CertificateChecks.Batch19953.u33T_g_21_98,
      @CertificateChecks.Batch19953.u33T_g_22_99⟩,
    ⟨@CertificateChecks.Batch19953.u33T_g_23_100, @CertificateChecks.Batch19953.u33T_g_24_101, @CertificateChecks.Batch19953.u33T_g_25_102,
      @CertificateChecks.Batch19953.u33T_g_26_103, @CertificateChecks.Batch19953.u33T_g_27_104, @CertificateChecks.Batch19953.u33T_g_28_105,
      @CertificateChecks.Batch19953.u33T_g_29_106, @CertificateChecks.Batch19953.u33T_g_30_107, @CertificateChecks.Batch19953.u33T_g_31_108,
      @CertificateChecks.Batch19953.u33T_xy_109⟩,
    ⟨@CertificateChecks.Batch19953.u33T_V_110, @CertificateChecks.Batch19953.u33T_A2_111, @CertificateChecks.Batch19953.u33T_Z_112⟩⟩

end Certificates
