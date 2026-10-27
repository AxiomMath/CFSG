module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.Sporadic.J4.QTRankProof

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporNine
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
import CFSG.Quasithin.Background.RonanE114J4Gen
public import CFSG.Sporadic.J4.QTOutNorm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem pow_three_eq_one_of_pow_nine_J4
    (g : J) (hg : g ^ 9 = 1) : g ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM := j4Facts.mat
  obtain ⟨x, y, -, hx, hy, -, hzx, hzy, hQ, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
  set Q := Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J4)
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.J4 = 86775571046077562880 := by
    rw [Nat.card_congr (seedEquiv hM).toEquiv, card_J j4Facts]
  have hidx : ¬ 3 ∣ Q.index := by
    have h1 := Subgroup.card_mul_index Q
    rw [hQ, hcard] at h1
    omega
  have hg' : ((seedEquiv hM).symm g) ^ (3 ^ 2) = 1 := by
    rw [← map_pow, show 3 ^ 2 = 9 by norm_num, hg, map_one]
  have h3 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.pow_eq_one_of_index Q hQ hidx
    (fun q hq =>
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.pow_three_eq_one_of_mem_closure_cubic
        hx hy hzx hzy hq) hg'
  apply (seedEquiv hM).symm.injective
  rw [map_pow, h3, map_one]

theorem isSylowIn_P0_J4 :
    IsSylowIn 2 P0 ⊤ := by
  obtain ⟨h2, hi⟩ := CFSG.Quasithin.E2P.J4Two.P0_sylow
  exact ⟨le_top, h2, by rwa [Subgroup.relIndex_top_right]⟩

private theorem calL0NineCheck_Hj : calL0NineCheck 21 501397585920 = true := by
  decide +kernel

section


theorem not_hasCompFactor_isCalL0_Hj : ¬ HasCompFactor Hj IsCalL0 :=
  not_hasCompFactor_isCalL0_of_dvd_of_pow_nine
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput calL0NineCheck_Hj
    pow_three_eq_one_of_pow_nine_J4 (dvd_of_eq (card_Hj j4Facts))

theorem not_hasCompFactor_isCalL0_centralizer_eta_1131 :
    ¬ HasCompFactor (Subgroup.centralizer ({eta uJ 11 1131} : Set J)) IsCalL0 :=
  not_hasCompFactor_isCalL0_of_dvd_of_pow_nine
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput calL0NineCheck_Hj
    pow_three_eq_one_of_pow_nine_J4
    (by rw [CFSG.Sporadic.J4.QT2.card_centralizer_eta_1131]; norm_num)

theorem isLPair_Hj_centralizer_eta_1131 :
    IsLPair IsCalL0 P0 Hj (Subgroup.centralizer ({eta uJ 11 1131} : Set J)) where
  le_left := P0_le_Hj
  le_right := CFSG.Quasithin.E2P.J4Two.P0_le_centralizer
  ne_top_left := (isCoatom_Hj j4Facts).1
  ne_top_right h := by
    have h1 := congrArg (fun H : Subgroup J => Nat.card H) h
    simp only [Subgroup.card_top, CFSG.Sporadic.J4.QT2.card_centralizer_eta_1131,
      card_J j4Facts] at h1
    omega
  not_left := not_hasCompFactor_isCalL0_Hj
  not_right := not_hasCompFactor_isCalL0_centralizer_eta_1131
  sup_eq_top := CFSG.Quasithin.RonanE114.Hj_sup_centralizer_z0

theorem asch54SporGenAt_j4 :
    Asch54SporGenAt .J4 := by
  let e : J ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4 := (seedEquiv j4Facts.mat).symm
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J4) := Finite.of_equiv J e.toEquiv
  exact asch54SporGenAt_of_isLPair_of_card_outer_eq_one
    (C := CFSG.Blueprint.NativeSporadic.Carrier .J4)
    (CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv.map MulEquiv.symm) CFSG.AGLEmbedding.card_outer_J4
    (isSylowIn_top_map_mulEquiv isSylowIn_P0_J4 e) (isLPair_Hj_centralizer_eta_1131.map e)

end

end CFSG.LocalAnalysis.WeakClosure81

end
