module

public import CFSG.Quasithin.H13.L32AL2Ic
public import CFSG.Quasithin.H13.L32A706c

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem pRank_T_and_thompsonJ_ne_bot (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : 3 ≤ CFSG.Open.pRank 2 T ∧ thompsonJ T ≠ ⊥ := by
  obtain ⟨V₂, _, S14⟩ := D.exists_set14 h1222 h1332 h1334
  have hVe : IsElemAbelian 2 V := ⟨inferInstance, fun v hv => S14.sq_V hv⟩
  refine ⟨le_pRank Nat.prime_two S14.VT hVe (by rw [S14.card_V]; norm_num), ?_⟩
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
  intro hb
  have hA₀J : A₀ ≤ thompsonJ T := le_iSup₂_of_le A₀ hA₀ le_rfl
  have h8 : Nat.card V ≤ Nat.card A₀ := hA₀.2.2 V S14.VT hVe
  rw [le_bot_iff.mp (hA₀J.trans hb.le), Subgroup.card_bot, S14.card_V] at h8
  omega

theorem inf_centralizer_le_pCoreOf (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  obtain ⟨V₂, _, S14⟩ := D.exists_set14 h1222 h1332 h1334
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S14.LV S14.TV
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg)
      (mem_normalizer_centralizer (hLTV hg))) S14.isPGroup_cent_sup

theorem normalizer_thompsonJ_le (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hJV : thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    Subgroup.normalizer (thompsonJ T : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨hr, hJne⟩ := D.pRank_T_and_thompsonJ_ne_bot h1222 h1332 h1334
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo D.S.hyp.fsu.sylow le_sup_right)
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJQ : thompsonJ T ≤ Q :=
    le_inf (hJT.trans le_sup_right) hJV |>.trans (D.inf_centralizer_le_pCoreOf h1222 h1332 h1334)
  have hJ : thompsonJ T = thompsonJ Q := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le (by omega) (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJQ) hQT
  refine L32A.Setting147.normalizer_le_M D.S h1332 hJne (D.isPGroup_T.to_le hJT) ?_
  rw [hJ]
  exact (le_normalizer_pCoreOf 2 (L ⊔ T)).trans (normalizer_le_normalizer_thompsonJ Q)

theorem not_thompsonJ_le_centralizer_vI (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (vI T L V z z' : Set G) := by
  intro hJ
  obtain ⟨hr, -⟩ := D.pRank_T_and_thompsonJ_ne_bot h1222 h1332 h1334
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJC := hJ.trans D.centralizer_vI_le
  have hJTY : thompsonJ T ≤ TY :=
    (le_inf (le_inf hJT (hJC.trans inf_le_left)) (hJC.trans inf_le_right)).trans D.hCT
  have hJY : thompsonJ T ≤ pCoreOf 2 (a114Y z z' ⊔ TY) := by
    rw [D.hO2Y]
    exact le_inf (hJTY.trans le_sup_right) (hJC.trans inf_le_right)
  have hYT : pCoreOf 2 (a114Y z z' ⊔ TY) ≤ T :=
    (pCoreOf_le_of_isSylowTwoOf D.hSyl).trans D.hTY
  have hJeq : thompsonJ T = thompsonJ (pCoreOf 2 (a114Y z z' ⊔ TY)) := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le (by omega) (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJY) hYT
  have hYN : a114Y z z' ⊔ TY ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [hJeq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_thompsonJ _)
  exact D.a114Y_not_le_normalizer_L h1222 h1332 h1334 (le_sup_left.trans
    (hYN.trans (D.normalizer_thompsonJ_le h1222 h1332 h1334 (hJC.trans inf_le_left))))

end IData

end CFSG.Quasithin.H13.L32A.L2
