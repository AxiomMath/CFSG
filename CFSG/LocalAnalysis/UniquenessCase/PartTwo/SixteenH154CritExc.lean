module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcGT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcX
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ChiD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3G
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Perm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_false_of_Z7_six_three (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) 7)
    (hrk : rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) = 6)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 3) (h3 : D.sig = {3}) : False := by
  have hp7 : (7 : ℕ).Prime := by norm_num
  have hk : D.k = 1 := by
    have hsp := S.hSig.sig1_sp 3 (by rw [← hσ, h3]; exact Set.mem_singleton 3)
    unfold Data.k RankThreeUC.kParam
    rw [if_pos hsp]
  have hχ : ¬ ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n := fun hχ => by
    have := s16h_rk_wTil_le_three_of_chi D h hc hp7 hLp hχ
    omega
  have hLd := s16h_le_commutator_of_not_centralizes hp7 hLp.2
    (barSub_mono V₀ V h.hyp151.isElemAbelian h.hyp151.le) hχ
  obtain ⟨t, -, -, -, -, hW⟩ := hc
  obtain ⟨X, hXd, hXn, hXe, hXc⟩ := s16h_closure_of_le_commutator hp7 hLp.2 hLd
    (fun q hq q' hq' hne => (s16h_conj_comm_inf_of_conc hW hq hq' hne).1)
    (s16h_sSupIndep_conj_of_conc hW)
  have hX3 : Nat.card ↥X = 7 ^ 3 := by rw [hXc, ← hs]; rfl
  obtain ⟨-, -, -, -, hind, -⟩ := s16h_conc4_133_of_prime_card hp7 hLp.2 hW
  have hgt : MBarGT D.M V₀ V (D.k + 1) := by
    rw [hk]
    exact (h.hyp16.hyp125.mBarGT_iff_lt_mBar 2).2
      (s16h_two_lt_mParam_of_Z7_six (s15_Infra_vtil_sq_eq_one V₀ V _) hW hind hLp hrk)
  exact s16h_not_mBarGT_of_bar D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111 S.h112 S.hThin S.hCyc
    S.h127 S.h126 S.h1211 S.h111W S.h6161ii hσ h.hyp16 hp7 (by norm_num) hXn hXe hXd
    (by norm_num) (fun _ => by norm_num) hX3 hgt

private theorem s16h_v1Sub_eq_of_odd_card_Z3 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hodd : Odd (Nat.card ↥(lBar V₀ V hV L))) :
    v1Sub D.M V₀ V hV L = V₀ := by
  by_cases h0 : V₀ = ⊥
  · subst h0
    exact s16c167_v1Sub_eq_bot_of_inf_fixV D hV rfl
      (s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd)
  · exact v1Sub_of_ne_bot D.M V₀ V hV L h0

theorem s16h_unique₁_of_Z3_six_two (D : Data G) (S : s16h_Std D)
    (h4 : 3 < CFSG.Open.evenRank G) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) 3)
    (hrk : rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) = 6)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2) (h3 : D.sig = {3}) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by rw [hLp.2]; decide
  have hv1 : v1Sub D.M V₀ V hV L ≤ V₀ := (s16h_v1Sub_eq_of_odd_card_Z3 D hV hodd).le
  have h3mem : 3 ∈ D.sig := by rw [h3]; exact Set.mem_singleton 3
  obtain ⟨R, hRle, hRp, hRc⟩ :=
    s16h_exists_noncyclic_of_Z3_six_two D S h4 hσ h hc hLp hrk hs h3
  refine s16h_unique₁_of_wSub D h.hyp151 hv1 (fun w hw hw1 => ?_)
  by_cases hw0 : w ∈ V₀
  · exact s16c34_uniqueMax_cent_of_mem_v0 D S.h61 h.hyp16 h3mem
      (S.hSig.three_le 3 h3mem) hw0 hw1
  · have hwV : w ∈ V := preTil_le V₀ V hV _ hw
    exact s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16 h3mem hRp hRc hwV hw0
      (hRle.trans (s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hw))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
