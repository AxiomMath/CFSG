module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3F2
public import CFSG.Quasithin.Background.Equivariance
public import CFSG.Quasithin.H13.GoldschmidtC137S6Sub

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

theorem card_map_act (K : Subgroup (Gp 6)) :
    Nat.card (K.map (Mod.act 6 Mod.ut0)) = Nat.card K :=
  Subgroup.card_map_of_injective (act_injective (n := 6) (by norm_num) Mod.ut0)

theorem offender_F_ge {K : Subgroup (Gp 6)} (h : IsOffG 6 Mod.ut0 K) :
    K ≠ ⊥ ∧ 16 ≤ Nat.card (K.map (Mod.act 6 Mod.ut0)) *
      Nat.card (fixV (K.map (Mod.act 6 Mod.ut0))) := by
  refine ⟨fun hK => h.2.1 (by rw [hK, Subgroup.map_bot]), ?_⟩
  have h1 := h.2.2.2 ⊥ bot_le
  rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, card_V6] at h1
  omega

theorem P_le_N_J (P : Subgroup G) : P ≤ normalizer (thompsonJ (pCoreOf 2 P) : Set G) :=
  fun _ hp => normalizer_le_normalizer_of_map_mulEquiv (F := thompsonJ)
    (fun φ Y => thompsonJ_map_mulEquiv φ Y) (pCoreOf 2 P)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hp)

end CFSG.Quasithin.H13.U3.GC137
