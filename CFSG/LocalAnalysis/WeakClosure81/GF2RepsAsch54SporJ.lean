module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLat
public import CFSG.Quasithin.Background.E2TwoProofSporJ1
public import CFSG.Quasithin.Background.E2TwoProofSporJ2
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
public import Certificates.Certificate2164
public import Certificates.Certificate2165
public import Certificates.Certificate2166
public import Certificates.Certificate2167
public import Certificates.Certificate2233
public import Certificates.Certificate2234
public import Certificates.Certificate2235
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3119
public import Certificates.Certificate3139
public import Certificates.Certificate4142
public import Certificates.Certificate7124
public import Certificates.Certificate7125
public import Certificates.Certificate8033

import CFSG.Blueprint.NativeSporadic
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.Sporadic.Bridge.J1
import CFSG.Sporadic.Bridge.J2
import CFSG.Sporadic.J1.Setup
import CFSG.Sporadic.J2.Setup
import CFSG.Sporadic.Schreier.PairJ2Pairs
import CFSG.Sporadic.Schreier.PairOuter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat Subgroup
open CFSG.Quasithin.E2P.SporB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem asch54SporGenAt_j1 :
    Asch54SporGenAt .J1 := by
  have hOut : Nat.card (Outer ↥CFSG.Sporadic.J1.J) = 1 :=
    (Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      CFSG.Sporadic.J1.nativeEquiv.symm).toEquiv).trans CFSG.Sporadic.Schreier.at_j1_schreier.1
  refine asch54SporGenAt_of_list_of_card_outer_eq_one
    (CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv.map fun f =>
      f.symm.trans CFSG.Sporadic.J1.nativeEquiv)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut j1_sylow j1_all
    (fun j _ => j1_S_le_Y j) j1_cards j1_card_J (a := 16) (b := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem asch54SporGenAt_j2 :
    Asch54SporGenAt .J2 := by
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  have hN : j2Ctx.D.O.lbl.size = 4725 := j2_O_size
  have hk : j2Ctx.k = 7 := rfl
  have hS : IsSylowTwoOf j2Ctx.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨j2Ctx.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index j2Ctx.S
    rw [j2Ctx.S_card, j2Ctx.hΓ, hN, hk] at h1
    have h2 : j2Ctx.S.index = 4725 := by omega
    rw [h2]
    norm_num
  have hOut : Nat.card (Outer ↥CFSG.Sporadic.J2.J) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.Schreier.AT_J2_Schreier.1
      CFSG.Sporadic.J2.nativeEquiv.symm
  refine asch54SporGenAt_of_list
    (CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv.map fun f =>
      f.symm.trans CFSG.Sporadic.J2.nativeEquiv)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut hS (lat_all j2Ctx hL)
    (fun j _ => j2Ctx.S_le_Y j) (lat_card j2Ctx hL) (by rw [j2Ctx.hΓ, hN]) (a := 2) (b := 3)
    (by decide +kernel) ?_ ?_
  · rw [hk]
    decide +kernel
  · rw [hk]
    decide +kernel

end CFSG.LocalAnalysis.WeakClosure81

end
