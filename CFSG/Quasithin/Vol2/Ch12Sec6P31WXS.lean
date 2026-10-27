module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXF
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXL1
public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropAFrame
public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropAStar

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
  Equiv CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

section GLevel

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem singleData_of_setting (h1229 : Lemma12_6_29) (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hIs : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K) (hK₀ : conjClosure K T = K)
    (hthree : 3 ∣ Nat.card ↥(star H K)) :
    SingleData' (HStar H) (star H T) (star H (Subgroup.normalizer (L : Set G) ⊓ H))
      (star H (Li L F.V1)) (star H (T ⊓ L)) (star H K) := by
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  have hL1H : Li L F.V1 ≤ H := le_sup_left.trans h.L₁T_le_H
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hsylT := isSylowTwoOf_T h
  have hsylTs := isSylowTwoOf_star hsylT
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hsylT
  have hQM : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) := hQT.trans hH.hyp.normalizes
  have hKn : (star H K).Normal := by
    have := normal_star h918.K₀_normal
    rwa [hK₀] at this
  have hTsN : star H T ≤ Subgroup.normalizer (star H K : Set (HStar H)) :=
    Subgroup.le_normalizer_of_normal
  have hSs : IsSylowTwoOf (star H T ⊓ star H K) (star H K) :=
    A4.isSylowTwoOf_inf_normal hsylTs le_top Subgroup.le_normalizer_of_normal
  have hBM : borel (star H K) (star H T) ≤ star H (Subgroup.normalizer (L : Set G) ⊓ H) :=
    le_sup_right.trans (le_star_M h1229 F hH hZ hTH (pCoreOf_ne_bot h) le_sup_left
      (isSolvable_sup_borel hsylTs.2.1 hTsN hSs))
  obtain ⟨r, hr, S, hSL, hSe, hS9, hSinv⟩ :=
    exists_inverting_pair h1222 F hH hL1H hTH h.T_normalizes_V₁
  refine ⟨?_, hsylTs, hthree, hKn, star_mono (le_inf hH.hyp.normalizes hTH), hBM,
    not_le_star_M hKH hQM hIs.2.1,
    star_mono (le_inf (F126.L1_le_L.trans Subgroup.le_normalizer) hL1H),
    P31A.isSolvable_star (P31A.isSolvable_L1 h1222 F hH),
    S126P31.star_le_normalizer_star hL1H hTH (S126L19b.T_le_normalizer_L1 h1222 hH),
    star_mono inf_le_left, ⟨r, hr, S, hSL, hSe, hS9, hSinv⟩⟩
  exact threeRankLE2_of_noThree fun hA hB hC hAB hAC hBC hi hi' =>
    S126P31.false_of_three hH (pCoreOf_ne_bot h) hA hB hC hAB hAC hBC hi hi'

theorem not_27_dvd_card_Ms (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) :
    ¬ 27 ∣ Nat.card ↥(star H (Subgroup.normalizer (L : Set G) ⊓ H)) := by
  intro hd
  exact not_27_dvd_card_normalizer h1222 h1228 F hH
    (hd.trans ((Dvd.intro _ (F126.card_star
      (inf_le_right : Subgroup.normalizer (L : Set G) ⊓ H ≤ H))).trans
      (Subgroup.card_dvd_of_le inf_le_left)))

end GLevel

end CFSG.Quasithin.H13.P31X
