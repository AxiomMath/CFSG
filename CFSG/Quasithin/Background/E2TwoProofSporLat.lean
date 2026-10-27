module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

namespace E2P

namespace SporB

section M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Sporadic.Mathieu (m24a m24b m24_hyp)

noncomputable def m24CtxB :
    LatCtx ↥CFSG.Blueprint.NativeSporadic.M24 24 (List ℕ) :=
  m24Ctx

theorem asc86bClauseB_M24 :
    Asc86bClauseB .M24 := by
  have hL : m24CtxB.D.Om.map (fun o => o.lbl.size) =
      #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9] := m24_Om_map
  have hN : m24CtxB.D.O.lbl.size = 239085 := m24_O_size
  have hS : IsSylowTwoOf m24CtxB.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨m24CtxB.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index m24CtxB.S
    rw [m24CtxB.S_card, m24CtxB.hΓ, hN] at h1
    have h2 : m24CtxB.S.index = 239085 := by
      have : m24CtxB.k = 10 := rfl
      rw [this] at h1
      omega
    rw [h2]
    norm_num
  exact @asc86bClauseB_of_hasInvPair .M24 ↥CFSG.Blueprint.NativeSporadic.M24 inferInstance
    inferInstance (MulEquiv.refl _)
    (hasInvPair_of_lat m24CtxB hS hL hN (a := 1) (b := 3) (by decide +kernel))

end M24

theorem hasInvPair_HS :
    HasInvPair (CFSG.Sporadic.SmallF2.J CFSG.Sporadic.HS.Native.hsData) := by
  refine hasInvPair_of_list (L := #[1, 15, 21, 3, 3]) (N := 86625) (k := 9) HS.hs_S_sylow
    HS.hs_complete (fun j _ => HS.hsCtx.S_le_Y j) (fun j hj => ?_) (by rw [HS.hs_card]; ring)
    (a := 1) (b := 2) (by decide +kernel)
  rw [HS.hs_member_card j hj]
  norm_num

theorem asc86bClauseB_HS :
    Asc86bClauseB .HS :=
  @asc86bClauseB_of_hasInvPair .HS (CFSG.Sporadic.SmallF2.J CFSG.Sporadic.HS.Native.hsData)
    inferInstance inferInstance (CFSG.Sporadic.SmallF2.seedEquiv HS.hs_facts.toBaseFacts)
    hasInvPair_HS

theorem hasInvPair_Ru :
    HasInvPair (CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Ru.Native.ruData) := by
  refine hasInvPair_of_list (L := #[1, 15, 21, 3, 3]) (N := 8906625) (k := 14) Ru.ru_S_sylow
    Ru.ru_complete (fun j _ => Ru.ruCtx.S_le_Y j) (fun j hj => ?_) (by rw [Ru.ru_card]; ring)
    (a := 1) (b := 2) (by decide +kernel)
  rw [Ru.ru_member_card j hj]
  norm_num

theorem asc86bClauseB_Ru :
    Asc86bClauseB .Ru :=
  @asc86bClauseB_of_hasInvPair .Ru (CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Ru.Native.ruData)
    inferInstance inferInstance (CFSG.Sporadic.SmallF2.seedEquiv Ru.ru_facts.toBaseFacts)
    hasInvPair_Ru

theorem hasInvPair_He :
    HasInvPair CFSG.Sporadic.He.J := by
  have h23 : He.heCtx.Y 2 ≤ He.heCtx.Y 3 :=
    (He.he_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have h24 : He.heCtx.Y 2 ≤ He.heCtx.Y 4 :=
    (He.he_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have h27 : ¬ He.heCtx.Y 2 ≤ He.heCtx.Y 7 := fun h =>
    absurd ((He.he_Y_le_iff (by norm_num) (by norm_num)).mp h) (by decide)
  refine hasInvPair_of_list_meet (L := #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3]) (N := 3935925)
    (k := 10) He.he_S_sylow He.he_complete (fun j _ => He.heCtx.S_le_Y j) (fun j hj => ?_)
    (by rw [He.he_card]; ring) (a := 7) (c := 3) (d := 4) (by decide +kernel) h23 h24 h27
  rw [He.he_member_card j hj]
  norm_num

theorem asc86bClauseB_He :
    Asc86bClauseB .He :=
  @asc86bClauseB_of_hasInvPair .He CFSG.Sporadic.He.J inferInstance inferInstance
    CFSG.Sporadic.He.heEquivJ hasInvPair_He

end SporB

end E2P

end CFSG.Quasithin
