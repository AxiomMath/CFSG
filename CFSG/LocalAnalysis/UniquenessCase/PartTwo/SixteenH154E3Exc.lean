module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3ExcDisp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3AltBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FrameGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Para
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Vec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Engine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5TwoK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FstarTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Strong
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Three
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Trans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Cond

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81 (card_eq_of_isL3)

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_alt5_centreless {X : Type} [Group X] (h : UC22.IsAlt X 5) :
    ∀ a : X, (∀ b : X, a * b = b * a) → a = 1 := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup X := e.isSimpleGroup
  have hcardX : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  intro a ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h0 | h0
  · have hz' : a ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun g => (ha g).symm
    rwa [h0, Subgroup.mem_bot] at hz'
  · exfalso
    haveI : IsMulCommutative X := ⟨⟨fun x y => by
      have hx : x ∈ Subgroup.center X := h0 ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm⟩⟩
    have hprime : Nat.Prime (Nat.card X) :=
      Group.is_simple_iff_prime_card.mp (show IsSimpleGroup X from inferInstance)
    rw [hcardX] at hprime
    exact (by norm_num at hprime : False)

theorem s16h_e3_A5_two_concl
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
 (h880 : F08.R880 D) (hJP : K_JonesParshallH1) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar V₀ V h.hyp151.isElemAbelian L) = ⊥) (h3 : 3 ∈ D.sig)
    (hrow : s16h_H5A5Sum (lBar V₀ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L)) ⊥ 2)
    (hbad : ¬ ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔
        v1Sub D.M V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    Concl164 D V₀ V h.hyp151.isElemAbelian L := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨hAltL, hsum⟩ := s16h_a5Sum_alt hrow
  have hv1V₀ : v1Sub D.M V₀ V hV L ≤ V₀ := by
    rcases eq_or_ne V₀ ⊥ with h0 | h0
    · rw [s16c167_v1Sub_eq_bot_of_inf_fixV D hV h0 hZ]
      exact bot_le
    · exact (v1Sub_of_ne_bot D.M V₀ V hV L h0).le
  have hv1 : v1Sub D.M V₀ V hV L ≤ wSub V₀ V hV L := s16h_v1Sub_le_wSub D h.hyp151 hv1V₀
  have hcfg : s16h_H5Cfg (Mbar D.M V₀ V hV) (lBar V₀ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one V₀ V hV, ht, ht2, ht1, htr, hW, hcomp, hthin⟩
  have hrowZ : s16h_H5A5Sum (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2 := by
    rw [hZ]
    exact hrow
  have hσ3 : D.sig = {3} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨h3, fun q hq => ?_⟩
    by_contra hq3
    exact hbad (s16h_unique₁_of_wSub D h.hyp151 hv1V₀
      (s16h_uniqueMax_of_blockBound_one_two D S.h61 S.h127 h hs2.le hq (S.hx.three_le q hq)
        (s16h_H5_row_A5_one hcfg (by norm_num : 2 ≤ 3) hrowZ (D.sig_prime q hq).1
          (D.sig_prime q hq).2 (Or.inl hq3))))
  have h60 : Nat.card ↥(lBar V₀ V hV L) = 60 := by
    obtain ⟨e⟩ := hAltL
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V) := fun h3dvd =>
    hbad (s16h_e3_unique₁_of_dvd_cTil D S h hs2 hcomp Nat.prime_three (by norm_num) (Or.inl h3)
      (by rw [h60]; norm_num) h3dvd)
  have hp3 : CFSG.Open.pRank 3 D.M = 3 := s16h_pRank_eq_three D S hr3 h3
  obtain ⟨E, hEM, hEab, hEcard⟩ := c23_exists_elemAbelian_card_pow (p := 3) (M := D.M) (k := 3)
    Nat.prime_three (by rw [UC6.groupPRank_eq_pRank]; omega)
  obtain ⟨Eb, hEbX, hEbab, hEbcard⟩ :=
    s16h_e3_bar_rank_ge D h.hyp16.hyp125 h3C ⟨E, hEM, hEab, hEcard⟩
  have hrank : ∀ E' : Subgroup (MulAut (Vtil V₀ V hV)), E' ≤ Mbar D.M V₀ V hV →
      IsElemAbelian 3 E' → Nat.card ↥E' ≤ 27 := fun E' hE' hab => by
    have := s16h_e3_bar_card_le D h.hyp16.hyp125 Nat.prime_three h3C hp3.le E' hE' hab
    simpa using this
  have hbad' : ∃ w ∈ wTil V₀ V hV L, w ≠ 1 ∧ ∀ E' : Subgroup (MulAut (Vtil V₀ V hV)),
      E' ≤ Mbar D.M V₀ V hV → IsElemAbelian 3 E' → (∀ e ∈ E', e w = w) → Nat.card ↥E' ≤ 3 := by
    by_contra hcon
    apply hbad
    refine s16h_e3_uniqueMax_of_fixed D S h h3 hv1 ?_
    intro w hw hw1
    by_contra hno
    apply hcon
    refine ⟨w, hw, hw1, fun E' hE' hab hfixE => ?_⟩
    by_contra hlt
    apply hno
    refine ⟨E', hE', hab, ?_, hfixE⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).1 hab.isPGroup
    rw [hj] at hlt ⊢
    rcases j with _ | _ | j
    · simp at hlt
    · simp at hlt
    · calc 3 ^ 2 ≤ 3 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = _ := rfl
  obtain ⟨L', U', F⟩ := s16h_e3_frame_of_setting D S h1217 h hs2 hZ
  obtain ⟨Z, hZc, hZX, hZn, hZcomm, hK⟩ := s16h_e3_a5_two_center F hAltL hsum hrank
    ⟨Eb, hEbX, hEbab, by simpa using hEbcard⟩ hbad'
  obtain ⟨t', ht'T, hLt', -⟩ := F.swap
  have hAc : ∀ a ∈ lBar V₀ V hV L, (∀ b ∈ lBar V₀ V hV L, a * b = b * a) → a = 1 :=
    fun a ha hc => by
      have := s16h_e3_alt5_centreless hAltL ⟨a, ha⟩ fun b => Subtype.ext (hc b b.2)
      exact congrArg Subtype.val this
  have hfs := s16h_fstar_iso_of_two_components (X := Mbar D.M V₀ V hV) hcomp t'
    (F.t_le ht'T) hLt'.symm F.comm hAc hZX hZc hZn hZcomm hK
  exact ⟨hs2, Or.inr (Or.inl ⟨Or.inl ⟨hAltL, hsum⟩, hσ3, hp3, hfs⟩)⟩

theorem s16h_e3_A5_three_false
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
 (h880 : F08.R880 D) (hJP : K_JonesParshallH1) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar V₀ V h.hyp151.isElemAbelian L) = ⊥) (h3 : 3 ∈ D.sig)
    (hrow : s16h_H5A5Sum (lBar V₀ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L)) ⊥ 3) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  by_contra hbad
  have hV := h.hyp151.isElemAbelian
  obtain ⟨hAltL, hsum⟩ := s16h_a5Sum_alt hrow
  have h60 : Nat.card ↥(lBar V₀ V hV L) = 60 := by
    obtain ⟨e⟩ := hAltL
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V) := fun h3dvd =>
    hbad (s16h_e3_unique₁_of_dvd_cTil D S h hs2 hcomp Nat.prime_three (by norm_num) (Or.inl h3)
      (by rw [h60]; norm_num) h3dvd)
  obtain ⟨L', U', F⟩ := s16h_e3_frame_of_setting D S h1217 h hs2 hZ
  have hm : MBarGT D.M V₀ V 2 :=
    s16h_e3_mBarGT_of_rank D h.hyp16.hyp125 (fun τ hτ h2 h1 => by
      simpa using s16h_e3_a5_involution_rank F hAltL hsum hτ h2 h1) ⟨t, ht, ht2, ht1⟩
  obtain ⟨J, a, hJX, hTJ, hJcard, hJexp⟩ := s16h_e3_a5_parabolic F hAltL
  obtain ⟨Y, hYM, hY3, -, hYexp, hYnc, hYperm⟩ :=
    s16h_e3_permuting_lift D h.hyp16.hyp125 h3C hJX hTJ hJcard hJexp
  by_cases hV₀ : V₀ = ⊥
  · obtain ⟨w, hw1, hwT, E, hEX, hEab, hEcard, hEw⟩ := s16h_e3_a5_good_vector F hAltL hsum
    obtain ⟨v, hvV, hvT, hvC⟩ :=
      s16h_e3_good_vector_lift D S h hV₀ h3 hw1 hwT hEX hEab hEcard hEw
    exact s16h_e3_false_of_permuting_three D S hσ h h3 hm hYM hY3 hYexp hYnc hYperm
      (Or.inr (Or.inr ⟨v, hvV, hvT, hvC⟩))
  · exact s16h_e3_false_of_permuting_three D S hσ h h3 hm hYM hY3 hYexp hYnc hYperm
      (Or.inl hV₀)

theorem s16h_e3_L3_three_concl
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
 (h880 : F08.R880 D) (hJP : K_JonesParshallH1) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar V₀ V h.hyp151.isElemAbelian L) = ⊥)
    {q : ℕ} (hq : q ∈ D.sig) (hq37 : q = 3 ∨ q = 7)
    (hrow : s16h_H5L3Sum (lBar V₀ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L)) ⊥ 3)
    (hbad : ¬ ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔
        v1Sub D.M V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    Concl164 D V₀ V h.hyp151.isElemAbelian L := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨hSL, hsum⟩ := id hrow
  have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := s16k_isLn_of_isSLn (by norm_num) hSL
  have hv1V₀ : v1Sub D.M V₀ V hV L ≤ V₀ := by
    rcases eq_or_ne V₀ ⊥ with h0 | h0
    · rw [s16c167_v1Sub_eq_bot_of_inf_fixV D hV h0 hZ]
      exact bot_le
    · exact (v1Sub_of_ne_bot D.M V₀ V hV L h0).le
  have hv1 : v1Sub D.M V₀ V hV L ≤ wSub V₀ V hV L := s16h_v1Sub_le_wSub D h.hyp151 hv1V₀
  have hcfg : s16h_H5Cfg (Mbar D.M V₀ V hV) (lBar V₀ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one V₀ V hV, ht, ht2, ht1, htr, hW, hcomp, hthin⟩
  have hrowZ : s16h_H5L3Sum (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3 := by
    rw [hZ]
    exact hrow
  have hσ37 : ∀ q' ∈ D.sig, q' = 3 ∨ q' = 7 := by
    intro q' hq'
    by_contra hne
    exact hbad (s16h_unique₁_of_wSub D h.hyp151 hv1V₀
      (s16h_uniqueMax_of_blockBound_one_two D S.h61 S.h127 h hs2.le hq' (S.hx.three_le q' hq')
        (s16h_H5_row_L3_one hcfg (le_refl 3) hrowZ (D.sig_prime q' hq').1 (D.sig_prime q' hq').2
          (Or.inl ⟨fun h3 => hne (Or.inl h3), fun h7 => hne (Or.inr h7)⟩))))
  obtain ⟨L', U', F⟩ := s16h_e3_frame_of_setting D S h1217 h hs2 hZ
  have htrans := s16h_e3_trans_of_l3_three hcfg hrow hZ
  have h3σ : 3 ∉ D.sig := fun h3 =>
    hbad (s16h_e3_l3_three_unique D S hr3 h hs2 hcomp hL3 hsum hv1 F htrans (Or.inl h3))
  have h7 : 7 ∈ D.sig := by
    rcases hq37 with rfl | rfl
    · exact absurd hq h3σ
    · exact hq
  have hσ7 : D.sig = {7} := Set.eq_singleton_iff_unique_mem.2 ⟨h7, fun q' hq' => by
    rcases hσ37 q' hq' with rfl | rfl
    · exact absurd hq' h3σ
    · rfl⟩
  have h168 : Nat.card ↥(lBar V₀ V hV L) = 168 := card_eq_of_isL3 hL3
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7C : ¬ 7 ∣ Nat.card ↥(F11.CTilde D.M V₀ V) := fun h7dvd =>
    hbad (s16h_e3_unique₁_of_dvd_cTil D S h hs2 hcomp (by norm_num : Nat.Prime 7) (by norm_num)
      (Or.inl h7) (by rw [h168]; norm_num) h7dvd)
  have hp7 : CFSG.Open.pRank 7 D.M = 3 := s16h_pRank_eq_three D S hr3 h7
  obtain ⟨E, hEM, hEab, hEcard⟩ := c23_exists_elemAbelian_card_pow (p := 7) (M := D.M) (k := 3)
    (by norm_num) (by rw [UC6.groupPRank_eq_pRank]; omega)
  obtain ⟨Eb, hEbX, hEbab, hEbcard⟩ :=
    s16h_e3_bar_rank_ge D h.hyp16.hyp125 h7C ⟨E, hEM, hEab, hEcard⟩
  have hrank : ∀ E' : Subgroup (MulAut (Vtil V₀ V hV)), E' ≤ Mbar D.M V₀ V hV →
      IsElemAbelian 7 E' → Nat.card ↥E' ≤ 343 := fun E' hE' hab => by
    have := s16h_e3_bar_card_le D h.hyp16.hyp125 (by norm_num : Nat.Prime 7) h7C hp7.le E' hE' hab
    simpa using this
  have hbad' : ∃ w ∈ wTil V₀ V hV L, w ≠ 1 ∧ ∀ E' : Subgroup (MulAut (Vtil V₀ V hV)),
      E' ≤ Mbar D.M V₀ V hV → IsElemAbelian 7 E' → (∀ e ∈ E', e w = w) → Nat.card ↥E' ≤ 7 := by
    by_contra hcon
    apply hbad
    refine s16h_e3_uniqueMax_of_fixed D S h h7 hv1 ?_
    intro w hw hw1
    by_contra hno
    apply hcon
    refine ⟨w, hw, hw1, fun E' hE' hab hfixE => ?_⟩
    by_contra hlt
    apply hno
    refine ⟨E', hE', hab, ?_, hfixE⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 7)).1 hab.isPGroup
    rw [hj] at hlt ⊢
    rcases j with _ | _ | j
    · simp at hlt
    · simp at hlt
    · calc 7 ^ 2 ≤ 7 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = _ := rfl
  rcases s16h_e3_l3_seven_K F hL3 hsum hrank ⟨Eb, hEbX, hEbab, by simpa using hEbcard⟩ hbad' with
    ⟨Z, hZcard, hZX, hZn, hZcomm, hKs, hFit⟩ | hK
  · obtain ⟨t', ht'T, hLt', -⟩ := F.swap
    have hAc : ∀ a ∈ lBar V₀ V hV L, (∀ b ∈ lBar V₀ V hV L, a * b = b * a) → a = 1 :=
      fun a ha hc => by
        have := s16h_isL3_centreless hL3 ⟨a, ha⟩ fun b => Subtype.ext (hc b b.2)
        exact congrArg Subtype.val this
    have hfs := s16h_fstar_iso_of_two_components_gen (X := Mbar D.M V₀ V hV) (p := 7)
      (by norm_num) hcomp t' (F.t_le ht'T) hLt'.symm F.comm hAc hZX hZcard hZn hZcomm hKs hFit
    exact ⟨hs2, Or.inr (Or.inr (Or.inl ⟨hL3, hsum, hσ7, hp7, hfs⟩))⟩
  · obtain ⟨hsp, h3r⟩ := s16h_e3_l3_K_strong D S h hcomp hL3 F hK
    exact (hbad (s16h_e3_l3_three_unique D S hr3 h hs2 hcomp hL3 hsum hv1 F htrans
      (Or.inr ⟨hsp, h3r⟩))).elim

theorem s16h_exc_struct
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
 (h880 : F08.R880 D) (hJP : K_JonesParshallH1) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar V₀ V h.hyp151.isElemAbelian L) = ⊥)
    (hall : ∀ q ∈ D.sig, ¬ s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1)
    (hfix : ∀ q ∈ D.sig, ¬ s16h_H5Fix (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q) :
    (∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
        w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) ∨
      Concl164 D V₀ V h.hyp151.isElemAbelian L := by
  by_cases hU : ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔
      v1Sub D.M V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))
  · exact Or.inl hU
  refine Or.inr ?_
  have hV := h.hyp151.isElemAbelian
  obtain ⟨q, hq⟩ := S.hx.sig_nonempty
  have hpp := D.sig_prime q hq
  have hcfg : s16h_H5Cfg (Mbar D.M V₀ V hV) (lBar V₀ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one V₀ V hV, ht, ht2, ht1, htr, hW, hcomp, hthin⟩
  rcases s16h_exc_dispatch hJP hcfg hZ hpp.1 hpp.2 (hall q hq) (hfix q hq) with
    ⟨hq3, hA5 | hA5⟩ | ⟨hq37, hL3⟩
  · exact s16h_e3_A5_two_concl D S hr3 hσ h880 hJP h1217 h hs2 ht ht2 ht1 htr hW hcomp hthin
      hZ (hq3 ▸ hq) hA5 hU
  · exact (hU (s16h_e3_A5_three_false D S hr3 hσ h880 hJP h1217 h hs2 ht ht2 ht1 htr hW
      hcomp hthin hZ (hq3 ▸ hq) hA5)).elim
  · exact s16h_e3_L3_three_concl D S hr3 hσ h880 hJP h1217 h hs2 ht ht2 ht1 htr hW hcomp
      hthin hZ hq hq37 hL3 hU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
