module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLat
public import CFSG.Quasithin.Background.E2TwoProofSporLat
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2111
public import Certificates.Certificate2112
public import Certificates.Certificate2198
public import Certificates.Certificate2205
public import Certificates.Certificate2218
public import Certificates.Certificate2219
public import Certificates.Certificate2220
public import Certificates.Certificate2221
public import Certificates.Certificate2222
public import Certificates.Certificate2223
public import Certificates.Certificate2224
public import Certificates.Certificate2225
public import Certificates.Certificate2247
public import Certificates.Certificate2249
public import Certificates.Certificate2250
public import Certificates.Certificate2251
public import Certificates.Certificate2252
public import Certificates.Certificate2253
public import Certificates.Certificate2254
public import Certificates.Certificate2255
public import Certificates.Certificate2256
public import Certificates.Certificate2258
public import Certificates.Certificate2259
public import Certificates.Certificate2260
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3017
public import Certificates.Certificate3046
public import Certificates.Certificate3167
public import Certificates.Certificate3168
public import Certificates.Certificate3172
public import Certificates.Certificate4033
public import Certificates.Certificate4034
public import Certificates.Certificate4068
public import Certificates.Certificate4075
public import Certificates.Certificate4102
public import Certificates.Certificate4140
public import Certificates.Certificate4141
public import Certificates.Certificate4143
public import Certificates.Certificate8033
public import Certificates.Certificate9116
public import Certificates.Certificate9118
public import Certificates.Certificate9123
public import Certificates.Certificate9129
public import Certificates.Certificate9209
public import Certificates.Certificate9210
public import Certificates.Certificate9215
public import Certificates.Certificate9218

import CFSG.Blueprint.NativeSporadic
import all CFSG.Quasithin.Background.E2TwoProofSporLat
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
import CFSG.Sporadic.Schreier.PairHSOut
import CFSG.Sporadic.Schreier.PairHePairs
import CFSG.Sporadic.Schreier.RuAutInner
import CFSG.Sporadic.Schreier.RuIso
import CFSG.Sporadic.Schreier.PairOuter
import CFSG.Sporadic.Bridge.M24Surj
import CFSG.Sporadic.Bridge.HSSurj
import CFSG.Sporadic.Bridge.HeSurj
import CFSG.Sporadic.Bridge.RuSurj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat Subgroup
open CFSG.Quasithin.E2P.SporB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem asch54SporGenAt_m24 :
    Asch54SporGenAt .M24 := by
  have hL : m24CtxB.D.Om.map (fun o => o.lbl.size) =
      #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9] := M24.m24_Om_map
  have hN : m24CtxB.D.O.lbl.size = 239085 := M24.m24_O_size
  have hk : m24CtxB.k = 10 := by
    have h := m24CtxB.hΓ
    rw [M24.m24_card, hN] at h
    exact Nat.pow_right_injective le_rfl
      (Nat.eq_of_mul_eq_mul_left (by norm_num) (h.symm.trans (mul_comm _ _)))
  have hS : IsSylowTwoOf m24CtxB.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨m24CtxB.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index m24CtxB.S
    rw [m24CtxB.S_card, m24CtxB.hΓ, hN, hk] at h1
    have h2 : m24CtxB.S.index = 239085 := by omega
    rw [h2]
    norm_num
  refine asch54SporGenAt_of_list_of_card_outer_eq_one
    (CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv.map MulEquiv.symm)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.AGLEmbedding.card_outer_M24 hS (lat_all m24CtxB hL) (fun j _ => m24CtxB.S_le_Y j)
    (lat_card m24CtxB hL) (by rw [m24CtxB.hΓ, hN]) (a := 3) (b := 4) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [hk]
    decide +kernel
  · rw [hk]
    decide +kernel

theorem asch54SporGenAt_hs :
    Asch54SporGenAt .HS := by
  have hOut : Nat.card (Outer (CFSG.Sporadic.SmallF2.J CFSG.Sporadic.HS.Native.hsData)) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.Schreier.HS_outer_card_le_two.1
      (CFSG.Sporadic.SmallF2.seedEquiv HS.hs_facts.toBaseFacts).symm
  refine asch54SporGenAt_of_list
    (CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv.map fun f =>
      f.symm.trans (CFSG.Sporadic.SmallF2.seedEquiv HS.hs_facts.toBaseFacts))
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut
    (L := #[1, 15, 21, 3, 3]) (N := 86625) (k := 9) HS.hs_S_sylow HS.hs_complete
    (fun j _ => HS.hsCtx.S_le_Y j) (fun j hj => ?_) (by rw [HS.hs_card]; ring) (a := 1) (b := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [HS.hs_member_card j hj]
  norm_num

theorem asch54SporGenAt_ru :
    Asch54SporGenAt .Ru := by
  have hR : Nat.card (Outer CFSG.Blueprint.NativeSporadic.Ru) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv
      (by rw [CFSG.Sporadic.RuSchreier.card_outer_ruP]; norm_num)
      CFSG.Sporadic.RuSchreier.ruEquivP
  have hOut : Nat.card (Outer (CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Ru.Native.ruData)) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv hR
      (CFSG.Sporadic.SmallF2.seedEquiv Ru.ru_facts.toBaseFacts).symm
  refine asch54SporGenAt_of_list
    (CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv.map fun f =>
      f.symm.trans (CFSG.Sporadic.SmallF2.seedEquiv Ru.ru_facts.toBaseFacts))
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut
    (L := #[1, 15, 21, 3, 3]) (N := 8906625) (k := 14) Ru.ru_S_sylow Ru.ru_complete
    (fun j _ => Ru.ruCtx.S_le_Y j) (fun j hj => ?_) (by rw [Ru.ru_card]; ring) (a := 1) (b := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [Ru.ru_member_card j hj]
  norm_num

theorem asch54SporGenAt_he :
    Asch54SporGenAt .He := by
  have h23 : He.heCtx.Y 2 ≤ He.heCtx.Y 3 :=
    (He.he_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have h24 : He.heCtx.Y 2 ≤ He.heCtx.Y 4 :=
    (He.he_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have h27 : ¬ He.heCtx.Y 2 ≤ He.heCtx.Y 7 := fun h =>
    absurd ((He.he_Y_le_iff (by norm_num) (by norm_num)).mp h) (by decide)
  have hOut : Nat.card (Outer ↥CFSG.Sporadic.He.J) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.Schreier.AT_He_Schreier.1
      CFSG.Sporadic.He.heEquivJ.symm
  refine asch54SporGenAt_of_list_meet
    (CFSG.Sporadic.Bridge.He.nonempty_mulEquiv.map fun f =>
      f.symm.trans CFSG.Sporadic.He.heEquivJ)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut
    (L := #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3]) (N := 3935925) (k := 10) He.he_S_sylow
    He.he_complete (fun j _ => He.heCtx.S_le_Y j) (fun j hj => ?_) (by rw [He.he_card]; ring)
    (a := 7) (c := 3) (d := 4) (by decide +kernel) h23 h24 h27 (by decide +kernel)
    (by decide +kernel)
  rw [He.he_member_card j hj]
  norm_num

end CFSG.LocalAnalysis.WeakClosure81

end
