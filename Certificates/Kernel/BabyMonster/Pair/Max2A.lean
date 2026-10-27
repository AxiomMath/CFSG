module

public import Certificates.Kernel.BabyMonster.Pair.Facts
public import Certificates.Kernel.BabyMonster.Pair.Pinned
public import CFSG.Monster.B.Dyadic.Max2K
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.All
public import CFSG.Certificates.Kernel.BabyMonster.Chain4
public import CFSG.Certificates.Kernel.BabyMonster.Chain4Pair
public import CFSG.Certificates.Kernel.BabyMonster.Max2.All
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check10
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check11
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check12
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check13
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check14
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check15
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check16
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check17
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check18
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check19
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check20
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check21
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check22
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check23
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check24
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check25
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check26
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check27
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check28
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check29
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check30
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check31
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check32
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check33
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check34
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check35
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check36
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check37
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check38
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check39
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check40
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check41
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check42
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check43
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check44
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check45
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check46
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check47
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check48
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check49
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check50
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check51
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check52
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check53
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check54
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check55
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check56
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check57
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check58
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check59
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check60
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check61
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check62
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check63
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check64
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check65
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check66
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check67
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check68
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check69
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check70
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check71
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check72
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check9
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Transfer.All
public import CFSG.Certificates.Kernel.BabyMonster.Transfer.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Transfer.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Transfer.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Transfer.Check4

public section

namespace CertificateChecks.KernelBM.Pair

open CFSG.KC.BM CFSG.Monster.B.Dyadic

set_option maxRecDepth 100000

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem QnK_eq {j : ℕ} (hj : j < 26) : QnK j = stripMat (Qs.getD j []) := by
  rw [QnK, dite_eq_left hj]
  exact qmat_Qs ⟨j, hj⟩

theorem wordQK_eq {w : List ℕ} (hw : ∀ j ∈ w, j < 26) :
    wordQK w = ((w.map fun j => Qs.getD j []).map stripMat).prod := by
  rw [wordQK, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun j hj => QnK_eq (hw j hj))

@[expose] noncomputable def parityL : List (List Nat) :=
  CFSG.Monster.B.Bin.parityWord24.map fun j => Qs.getD j []

theorem parityL_eq : parityL = NativePair.Q12 :: parityL.tail := rfl

theorem parity_range : ∀ j ∈ CFSG.Monster.B.Bin.parityWord24, j < 26 := by decide +kernel

theorem pchain : WChain parityL.tail NativePair.Q12 Max2T.Wp := by
  bm_wchain4 CFSG.KC.BM.Max2T.cWp 0 CFSG.KC.BM.Max2T.wf_

theorem parity_eq : wordQK CFSG.Monster.B.Bin.parityWord24 = stripMat Max2T.Wp := by
  have hwf : ∀ X ∈ parityL.tail, wfMat X = true := by
    intro X hX
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_of_mem_tail hX)
    exact wf_Qs j (parity_range j hj)
  rw [wordQK_eq parity_range, ← parityL, parityL_eq, List.map_cons, List.prod_cons,
    ← foldl_mul_eq]
  exact stripMat_wchain pchain hwf NativePair24.wf_Q12

@[expose] noncomputable def Ml : List (List Nat) :=
  [NativePair.Q0, Max2.E1, Max2.E2, Max2.E3, Max2.E4_0, Max2.E4_1, Max2.E4, Max2.E5, Max2.E6,
    Max2.E7, Max2.E8, Max2.E9, Max2.E10, Max2.E11_0, Max2.E11, Max2.E12, Max2.E13, Max2.E14_0,
    Max2.E14, Max2.E15_0, Max2.E15, Max2.E16_0, Max2.E16, Max2.E17_0, Max2.E17, Max2.E18_0,
    Max2.E18, Max2.E19_0, Max2.E19, Max2.E20_0, Max2.E20, Max2.E21_0, Max2.E21_1, Max2.E21_2,
    Max2.E21_3, Max2.E21_4, Max2.E21]

@[expose] noncomputable def Bl : List (List Nat) :=
  [NativePair.Q24, NativePair.Q14, NativePair.Q24, NativePair.Q22, NativePair.Q24, NativePair.Q7,
    NativePair.Q24, NativePair.Q2, NativePair.Q24, NativePair.Q23, NativePair.Q24, NativePair.Q5,
    NativePair.Q24, NativePair.Q12, NativePair.Q24, NativePair.Q16, NativePair.Q24, NativePair.Q23,
    NativePair.Q24, NativePair.Q2, NativePair.Q24, NativePair.Q9, NativePair.Q24, NativePair.Q14,
    NativePair.Q24, NativePair.Q5, NativePair.Q24, NativePair.Q23, NativePair.Q24, NativePair.Q3,
    NativePair.Q24, NativePair.Q7, NativePair.Q24, NativePair.Q14, NativePair.Q24, NativePair.Q1]

theorem Bl_eq : CFSG.Monster.B.Bin.basisWord.map (fun j => Qs.getD j []) = Bl := rfl

theorem basis_range : ∀ j ∈ CFSG.Monster.B.Bin.basisWord, j < 26 := by decide +kernel

theorem steps : ∀ k < 36, stripMat (Bl.getD k []) * stripMat (Ml.getD (k + 1) []) =
    stripMat (Ml.getD k []) * stripMat (Bl.getD k []) := by
  intro k hk
  interval_cases k
  · exact sm11 Max2.wf_E1 NativePair24.wf_Q24 NativePair24.wf_Q24 NativePair24.wf_Q0
      (by bm_strips2 CFSG.KC.BM.Max2.cE1 69)
  · exact sm11 Max2.wf_E2 NativePair24.wf_Q14 NativePair24.wf_Q14 Max2.wf_E1
      (by bm_strips2 CFSG.KC.BM.Max2.cE2 69)
  · exact sm11 Max2.wf_E3 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E2
      (by bm_strips2 CFSG.KC.BM.Max2.cE3 69)
  · exact sm11 Max2.wf_E4_0 NativePair24.wf_Q22 NativePair24.wf_Q22 Max2.wf_E3
      (by bm_strips2 CFSG.KC.BM.Max2.cE4_0 69)
  · exact sm11 Max2.wf_E4_1 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E4_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE4_1 69)
  · exact sm11 Max2.wf_E4 NativePair24.wf_Q7 NativePair24.wf_Q7 Max2.wf_E4_1
      (by bm_strips2 CFSG.KC.BM.Max2.cE4 69)
  · exact sm11 Max2.wf_E5 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E4
      (by bm_strips2 CFSG.KC.BM.Max2.cE5 69)
  · exact sm11 Max2.wf_E6 NativePair24.wf_Q2 NativePair24.wf_Q2 Max2.wf_E5
      (by bm_strips2 CFSG.KC.BM.Max2.cE6 69)
  · exact sm11 Max2.wf_E7 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E6
      (by bm_strips2 CFSG.KC.BM.Max2.cE7 69)
  · exact sm11 Max2.wf_E8 NativePair24.wf_Q23 NativePair24.wf_Q23 Max2.wf_E7
      (by bm_strips2 CFSG.KC.BM.Max2.cE8 69)
  · exact sm11 Max2.wf_E9 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E8
      (by bm_strips2 CFSG.KC.BM.Max2.cE9 69)
  · exact sm11 Max2.wf_E10 NativePair24.wf_Q5 NativePair24.wf_Q5 Max2.wf_E9
      (by bm_strips2 CFSG.KC.BM.Max2.cE10 69)
  · exact sm11 Max2.wf_E11_0 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E10
      (by bm_strips2 CFSG.KC.BM.Max2.cE11_0 69)
  · exact sm11 Max2.wf_E11 NativePair24.wf_Q12 NativePair24.wf_Q12 Max2.wf_E11_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE11 69)
  · exact sm11 Max2.wf_E12 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E11
      (by bm_strips2 CFSG.KC.BM.Max2.cE12 69)
  · exact sm11 Max2.wf_E13 NativePair24.wf_Q16 NativePair24.wf_Q16 Max2.wf_E12
      (by bm_strips2 CFSG.KC.BM.Max2.cE13 69)
  · exact sm11 Max2.wf_E14_0 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E13
      (by bm_strips2 CFSG.KC.BM.Max2.cE14_0 69)
  · exact sm11 Max2.wf_E14 NativePair24.wf_Q23 NativePair24.wf_Q23 Max2.wf_E14_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE14 69)
  · exact sm11 Max2.wf_E15_0 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E14
      (by bm_strips2 CFSG.KC.BM.Max2.cE15_0 69)
  · exact sm11 Max2.wf_E15 NativePair24.wf_Q2 NativePair24.wf_Q2 Max2.wf_E15_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE15 69)
  · exact sm11 Max2.wf_E16_0 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E15
      (by bm_strips2 CFSG.KC.BM.Max2.cE16_0 69)
  · exact sm11 Max2.wf_E16 NativePair24.wf_Q9 NativePair24.wf_Q9 Max2.wf_E16_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE16 69)
  · exact sm11 Max2.wf_E17_0 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E16
      (by bm_strips2 CFSG.KC.BM.Max2.cE17_0 69)
  · exact sm11 Max2.wf_E17 NativePair24.wf_Q14 NativePair24.wf_Q14 Max2.wf_E17_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE17 69)
  · exact sm11 Max2.wf_E18_0 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E17
      (by bm_strips2 CFSG.KC.BM.Max2.cE18_0 69)
  · exact sm11 Max2.wf_E18 NativePair24.wf_Q5 NativePair24.wf_Q5 Max2.wf_E18_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE18 69)
  · exact sm11 Max2.wf_E19_0 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E18
      (by bm_strips2 CFSG.KC.BM.Max2.cE19_0 69)
  · exact sm11 Max2.wf_E19 NativePair24.wf_Q23 NativePair24.wf_Q23 Max2.wf_E19_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE19 69)
  · exact sm11 Max2.wf_E20_0 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E19
      (by bm_strips2 CFSG.KC.BM.Max2.cE20_0 69)
  · exact sm11 Max2.wf_E20 NativePair24.wf_Q3 NativePair24.wf_Q3 Max2.wf_E20_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE20 69)
  · exact sm11 Max2.wf_E21_0 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E20
      (by bm_strips2 CFSG.KC.BM.Max2.cE21_0 69)
  · exact sm11 Max2.wf_E21_1 NativePair24.wf_Q7 NativePair24.wf_Q7 Max2.wf_E21_0
      (by bm_strips2 CFSG.KC.BM.Max2.cE21_1 69)
  · exact sm11 Max2.wf_E21_2 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E21_1
      (by bm_strips2 CFSG.KC.BM.Max2.cE21_2 69)
  · exact sm11 Max2.wf_E21_3 NativePair24.wf_Q14 NativePair24.wf_Q14 Max2.wf_E21_2
      (by bm_strips2 CFSG.KC.BM.Max2.cE21_3 69)
  · exact sm11 Max2.wf_E21_4 NativePair24.wf_Q24 NativePair24.wf_Q24 Max2.wf_E21_3
      (by bm_strips2 CFSG.KC.BM.Max2.cE21_4 69)
  · exact sm11 Max2.wf_E21 NativePair24.wf_Q1 NativePair24.wf_Q1 Max2.wf_E21_4
      (by bm_strips2 CFSG.KC.BM.Max2.cE21 69)

theorem prefix_step : ∀ k ≤ 36, ((Bl.take k).map stripMat).prod * stripMat (Ml.getD k []) =
    stripMat NativePair.Q0 * ((Bl.take k).map stripMat).prod
  | 0, _ => by
    change 1 * stripMat NativePair.Q0 = stripMat NativePair.Q0 * 1
    rw [one_mul, mul_one]
  | k + 1, hk => by
    have hlen : k < Bl.length := by
      change k < 36
      omega
    rw [List.take_add_one,List.getElem?_eq_getElem hlen, Option.toList_some, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc,
      ← List.getD_eq_getElem _ [] hlen, steps k (by omega), ← mul_assoc, prefix_step k (by omega),
      mul_assoc]

theorem E_eq_Ml : ∀ i < 22, Elist.getD i [] =
    Ml.getD (CFSG.Monster.B.Bin.basisLens.getD i 0) [] := by
  intro i hi
  interval_cases i <;> rfl

theorem lens_le : ∀ i < 22, CFSG.Monster.B.Bin.basisLens.getD i 0 ≤ 36 := by
  intro i hi
  interval_cases i <;> decide

theorem prefix_conj : ∀ i < 22, prefixK i * EK i = QnK 0 * prefixK i := by
  intro i hi
  have hw : ∀ j ∈ CFSG.Monster.B.Bin.basisWord.take (CFSG.Monster.B.Bin.basisLens.getD i 0),
      j < 26 := fun j hj => basis_range j (List.mem_of_mem_take hj)
  rw [prefixK, wordQK_eq hw, List.map_take, Bl_eq, EK, E_eq_Ml i hi, QnK_eq (by norm_num)]
  exact prefix_step _ (lens_le i hi)

theorem s_eq : stripMat Max2.G2 * stripMat Max2.G1 * stripMat Max2.G1 * stripMat Max2.G2 *
    stripMat Max2.G2 * stripMat Max2.G1 = stripMat Max2.S := by
  have h0 : stripMat Max2.G2 * stripMat Max2.G1 * stripMat Max2.G1 = stripMat Max2.S_0 := by
    have e := stripMat_mul_of_allStrips (Ws := [Max2.G1, Max2.G1]) (A := Max2.G2) (C := Max2.S_0)
      (wf2 Max2.wf_G1 Max2.wf_G1) Max2.wf_G2 (by bm_strips CFSG.KC.BM.Max2.cS_0 69)
    rwa [List.map_cons, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_cons,
      List.foldl_nil] at e
  have h1 : stripMat Max2.S_0 * stripMat Max2.G2 * stripMat Max2.G2 = stripMat Max2.S_1 := by
    have e := stripMat_mul_of_allStrips (Ws := [Max2.G2, Max2.G2]) (A := Max2.S_0) (C := Max2.S_1)
      (wf2 Max2.wf_G2 Max2.wf_G2) Max2.wf_S_0 (by bm_strips CFSG.KC.BM.Max2.cS_1 69)
    rwa [List.map_cons, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_cons,
      List.foldl_nil] at e
  rw [h0, h1, sm1 Max2.wf_G1 Max2.wf_S_1 (by bm_strips CFSG.KC.BM.Max2.cS 69)]

theorem kk_eq : KK = (G2K * G1K * G1K * G2K * G2K * G1K) ^ 14 := by
  have h2 : stripMat Max2.S ^ 2 = stripMat Max2.S_sq1 := by
    rw [sq, sm1 Max2.wf_S Max2.wf_S (by bm_strips CFSG.KC.BM.Max2.cS_sq1 69)]
  have h4 : stripMat Max2.S ^ 4 = stripMat Max2.S_sq2 :=
    sq_step h2 (sm1 Max2.wf_S_sq1 Max2.wf_S_sq1 (by bm_strips CFSG.KC.BM.Max2.cS_sq2 69)) rfl
  have h8 : stripMat Max2.S ^ 8 = stripMat Max2.S_sq3 :=
    sq_step h4 (sm1 Max2.wf_S_sq2 Max2.wf_S_sq2 (by bm_strips CFSG.KC.BM.Max2.cS_sq3 69)) rfl
  have e : stripMat Max2.S ^ 14 = stripMat Max2.S ^ 2 * stripMat Max2.S ^ 4 *
      stripMat Max2.S ^ 8 := by
    rw [← pow_add, ← pow_add]
  rw [KK, G1K, G2K, s_eq, e, h2, h4, h8,
    sm1 Max2.wf_S_sq2 Max2.wf_S_sq1 (by bm_strips CFSG.KC.BM.Max2.cKp0 69),
    sm1 Max2.wf_S_sq3 Max2.wf_Kp0 (by bm_strips CFSG.KC.BM.Max2.cK 69)]

theorem y_pow : YK ^ 5 = 1 := by
  have h2 : stripMat Max2T.Yz ^ 2 = stripMat Max2T.Yz_sq1 := by
    rw [sq, sm1 Max2T.wf_Yz Max2T.wf_Yz (by bm_strips4 CFSG.KC.BM.Max2T.cYz_sq1 69)]
  have h4 : stripMat Max2T.Yz ^ 4 = stripMat Max2T.Yz_sq2 :=
    sq_step h2 (sm1 Max2T.wf_Yz_sq1 Max2T.wf_Yz_sq1 (by bm_strips4 CFSG.KC.BM.Max2T.cYz_sq2 69)) rfl
  rw [YK, pow_succ, h4,
    sm1one Max2T.wf_Yz Max2T.wf_Yz_sq2 (by bm_strips4 CFSG.KC.BM.Max2T.oy_pow 69)]

theorem y_ne : YK ≠ 1 := by
  have h := orbOK_sound (m₁ := 4) rfl (by decide) Max2T.wf_Yz Max2T.oy_orb 1 (by norm_num)
    (by norm_num)
  rwa [pow_one] at h

theorem y3_eq : YK ^ 3 = stripMat Max2T.Y3 := by
  have e : stripMat Max2T.Yz_sq1 * stripMat Max2T.Yz = stripMat Max2T.Y3 :=
    sm1 Max2T.wf_Yz Max2T.wf_Yz_sq1 (by bm_strips4 CFSG.KC.BM.Max2T.cY3 69)
  rw [YK, pow_succ, sq, sm1 Max2T.wf_Yz Max2T.wf_Yz (by bm_strips4 CFSG.KC.BM.Max2T.cYz_sq1 69), e]

theorem xp_eq : stripMat NativePair.Q25 * stripMat NativePair.Q25 * stripMat Max2.Xb *
    stripMat NativePair.Q25 = stripMat Transfer.Xp := by
  have e := stripMat_mul_of_allStrips (Ws := [NativePair.Q25, Max2.Xb, NativePair.Q25])
    (A := NativePair.Q25) (C := Transfer.Xp)
    (fun W hW => by
      rcases List.mem_cons.1 hW with rfl | hW
      · exact NativePair24.wf_Q25
      rcases List.mem_cons.1 hW with rfl | hW
      · exact Max2.wf_Xb
      rw [List.mem_singleton.1 hW]
      exact NativePair24.wf_Q25) NativePair24.wf_Q25 (by bm_strips CFSG.KC.BM.Transfer.cXp 69)
  rwa [List.map_cons, List.map_cons, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_cons, List.foldl_cons, List.foldl_nil] at e

theorem yq_eq :
    stripMat Max2.Ci * stripMat Transfer.Xp * stripMat Max2.C = stripMat Transfer.Yq := by
  have e := stripMat_mul_of_allStrips (Ws := [Transfer.Xp, Max2.C]) (A := Max2.Ci)
    (C := Transfer.Yq) (wf2 Transfer.wf_Xp Max2.wf_C) Max2.wf_Ci
    (by bm_strips CFSG.KC.BM.Transfer.cYq 69)
  rwa [List.map_cons, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_cons,
    List.foldl_nil] at e

theorem wy_pow : (stripMat Transfer.Wq * stripMat Transfer.Yq) ^ 5 = 1 := by
  have hWY : stripMat Transfer.Wq * stripMat Transfer.Yq = stripMat Transfer.WY :=
    sm1 Transfer.wf_Yq Transfer.wf_Wq (by bm_strips CFSG.KC.BM.Transfer.cWY 69)
  have h2 : stripMat Transfer.WY ^ 2 = stripMat Transfer.WY_sq1 := by
    rw [sq, sm1 Transfer.wf_WY Transfer.wf_WY (by bm_strips CFSG.KC.BM.Transfer.cWY_sq1 69)]
  have h4 : stripMat Transfer.WY ^ 4 = stripMat Transfer.WY_sq2 :=
    sq_step h2 (sm1 Transfer.wf_WY_sq1 Transfer.wf_WY_sq1
      (by bm_strips CFSG.KC.BM.Transfer.cWY_sq2 69)) rfl
  rw [hWY, pow_succ, h4, sm1one Transfer.wf_WY Transfer.wf_WY_sq2
    (by bm_strips CFSG.KC.BM.Transfer.wy5 69)]

end CertificateChecks.KernelBM.Pair

end
