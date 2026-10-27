module

public import CFSG.Quasithin.Vol2.Ch9Lem945

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H CFSG.Quasithin.E3 Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem rk_fsuV (h2 : n = 2) : rk ↥(fsuV T I) = 8 := by
  unfold rk
  rw [hc.card_fsuV h2, show (256 : ℕ) = 2 ^ 8 by norm_num, padicValNat.prime_pow]

theorem false_of_nParam_eq_one (h36 : A36ForSQTK)
    (h312 : A312ForSQTK) (h314 : A314Facts) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (hFa : A314QuasiRankFact)
    (hFb : A314FFCohomFact) (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four)
    (h612 : ASInputs.AS_E_6_12) (hH11 : Ch9InH11Plus) (h1 : zQ T I = fsuV T I) (h2 : n = 2)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hn : E1.nParam H = 1) : False := by
  have hr := hc.three_lt_rParam h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h3228
    hE610 h612 h1 h2
  have h944 := hc.wClos_zero_le h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h3228
    hE610 h612 h1 h2
  have h945 := hc.wClos_one_le h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h3228
    hE610 h612 h1 h2
  have hU := S.isUniqueM_normalizer_Q
  have hTtop : IsSylowIn 2 T ⊤ := isSylowIn_top_of_fsu S.hyp.fsu
  have hrk := hc.rk_fsuV h2
  have hV0 : fsuV T I ≤ wClos (fsuV T I) 0 T :=
    le_wClos_of_mQuot_le_self S.hV S.fsuV_le_T le_rfl (by rw [mQuot_self]) (by omega)
  have hV1 : fsuV T I ≤ wClos (fsuV T I) 1 T :=
    le_wClos_of_mQuot_le_self S.hV S.fsuV_le_T le_rfl (by rw [mQuot_self]; norm_num) (by omega)
  have hW0 : wClos (fsuV T I) 0 T ≠ ⊥ := fun h => S.fsuV_ne_bot (le_bot_iff.mp (h ▸ hV0))
  have hW1 : wClos (fsuV T I) 1 T ≠ ⊥ := fun h => S.fsuV_ne_bot (le_bot_iff.mp (h ▸ hV1))
  have hN0 := (e3_16_one hTtop le_top S.isPGroup_Q h944 hW0 hU).2
  have hC1 := e3_16_three hTtop le_top S.isPGroup_Q h945 hW1 hU
  have hm : 1 < mParam (autI S.hV ⊤) := by
    have h3 := S.le_mParam hH11
    rw [← S.normalizer_V_eq, autI_normalizer_eq_top] at h3
    omega
  have hs : 0 + 1 < sParam S.hV := by
    rw [zero_add]
    exact lt_sParam_of_lt S.hV (lt_trans (by norm_num) hr) hm
  have h319 := e3_19 S.hV (S.isSylowIn_of_le hH.1.1) (i := 0) (j := 1) (by rw [hn]; rfl) hs
  apply hH.2.1
  rw [← h319]
  exact sup_le (inf_le_right.trans hC1) (inf_le_right.trans hN0)

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
