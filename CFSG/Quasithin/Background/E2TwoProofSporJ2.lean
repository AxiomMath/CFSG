
module

public import CFSG.Quasithin.Background.E2TwoProofSporJ2Base

public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Background.E2TwoProofSporJ2Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2
public import Certificates.Certificate7125
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

namespace E2P

namespace SporB

section J2

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB.J2Lat CFSG.Sporadic.J2

theorem j2_lat_cert :
    LatFactsK (codeSetLab 315) 315 j2ta.toArray j2tb.toArray j2Delta (a : J) (b : J) j2Sg j2STabs
      j2LatD ∧ j2LatD.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] :=
  Certificates.certificate7125

@[expose] noncomputable def j2Ctx :
    LatCtx ↥J 315 (List ℕ) :=
  LatFactsK.ctx codeSetLab_lawful j2_delta_valid j2_ta' j2_tb' closure_ab j2_sGens.1 j2_sGens.2
    4725 (by rw [card_J]; norm_num) j2_lat_cert.1

theorem j2_O_size :
    j2Ctx.D.O.lbl.size = 4725 :=
  LatFactsK.ctx_O_size ..

theorem j2_Om_size :
    j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] :=
  j2_lat_cert.2

theorem hasInvPair_J2 :
    HasInvPair ↥J := by
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  have hN : j2Ctx.D.O.lbl.size = 4725 := j2_O_size
  have hS : IsSylowTwoOf j2Ctx.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨j2Ctx.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index j2Ctx.S
    rw [j2Ctx.S_card, j2Ctx.hΓ, hN] at h1
    have h2 : j2Ctx.S.index = 4725 := by
      have : j2Ctx.k = 7 := rfl
      rw [this] at h1
      omega
    rw [h2]
    norm_num
  exact hasInvPair_of_lat j2Ctx hS hL hN (a := 2) (b := 3) (by decide +kernel)

theorem asc86bClauseB_J2 :
    Asc86bClauseB .J2 :=
  @asc86bClauseB_of_hasInvPair .J2 ↥J inferInstance inferInstance nativeEquiv hasInvPair_J2

end J2

end SporB

end E2P

end CFSG.Quasithin
