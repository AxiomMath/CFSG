module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPStC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenA
public import CFSG.CGT.Foote82.T66.MC2Quot
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Milestones.ASVolI.H10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowStAA
public import CFSG.Quasithin.Background.SmithB51Sp4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154DeltaComm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s168e3_st8_z_eq_bot {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8) :
    commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
      fixV (lBar V₀ V hV L) = ⊥ := by
  have hW2 : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  exact s16jp_row_St8 hW2 ⟨hL, h8⟩ hirr

theorem s168e3_st8_v1_eq (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8) :
    v1Sub D.M V₀ V hV L = V₀ :=
  s16e_v1Sub_eq_of_inf_fixV D hV (s168e3_st8_z_eq_bot hL hirr h8)

theorem s168e3_st8_gamma_eq_eight (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8) :
    gamma15 D.M V₀ V hV L = 8 := by
  rw [s16e_gamma15_eq_of_inf_fixV D hV (s168e3_st8_z_eq_bot hL hirr h8)]
  have h := h8
  rw [s168e3_st8_z_eq_bot hL hirr h8, CFSG.ASVolI.ChH.mQuot_bot_eq_rk] at h
  exact h


section BlockNormalizer

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem s16h_le_stabSub_commSub_inf_fixV (L : Subgroup (MulAut W)) :
    L ≤ stabSub (commSub (⊤ : Subgroup W) L ⊓ fixV L) := by
  rw [← commV_eq_commSub, inf_comm]
  exact B5.le_stabSub_fixV_inf_commV (G := L) (L := L)
    (fun g hg l hl => L.mul_mem (L.mul_mem hg hl) (L.inv_mem hg))
    (fun g hg => L.inv_mem hg)

theorem s16h_H5_card_autSub_eq_autSec_of_le_normalizer
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hc : s16h_H5Cfg A L t)
    {E : Subgroup (MulAut W)} (hEN : E ≤ normalizer (L : Set (MulAut W))) :
    Nat.card ↥(autSub E (commSub ⊤ L)) =
      Nat.card ↥(autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) := by
  have : Finite (MulAut W) := by
    exact Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g hh => MulEquiv.ext (congrFun hh))
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hEU : E ≤ stabSub U := by
    rw [hU]
    intro e he
    exact StabLat.mem_stabSub_commSub (X := L) (Y := ⊤)
      (mem_stabSub_top e) (hEN he)
  have hEZ : E ≤ stabSub Z := by
    rw [hZ, ← commV_eq_commSub, inf_comm]
    exact B5.le_stabSub_fixV_inf_commV (G := E) (L := L)
      (fun e he x hx => (Subgroup.mem_normalizer_iff.mp (hEN he) x).mp hx)
      (fun e he => E.inv_mem he)
  have hcent : E ⊓ centSec U Z = E ⊓ centSub U := by
    refine le_antisymm ?_ ?_
    · intro e he
      rw [Subgroup.mem_inf] at he ⊢
      refine ⟨he.1, ?_⟩
      rw [mem_centSub]
      intro w hw
      exact s16h_H5_triv_of_triv_quot hc.comp (hEN he.1) (mem_centSec.mp he.2).2 w hw
    · intro e he
      rw [Subgroup.mem_inf] at he ⊢
      exact ⟨he.1, centSub_le_centSec U Z he.2⟩
  have h1 := card_autSub_mul (A := E) (U := U) hEU
  have h2 := card_autSec_mul (A := E) (W := U) (U := Z) hEU hEZ
  rw [hcent] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

theorem s16h_H5_rowSt8_autSub_card_dvd {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
    (hirr : commSub ⊤ L ∈ irrSet L) {B : Subgroup (MulAut W)}
    (hB : B ≤ normalizer (L : Set (MulAut W))) :
    Nat.card ↥(autSub B (commSub ⊤ L)) ∣ 336 := by
  classical
  have : Finite (MulAut W) := by
    exact Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g hh => MulEquiv.ext (congrFun hh))
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := U ⊓ fixV L with hZ
  obtain ⟨hL3, h8⟩ := h
  have hLU : L ≤ stabSub U := by rw [hU]; exact s16h_dc_le_stabSub_commSub L
  have hLZ : L ≤ stabSub Z := by rw [hZ]; exact s16h_le_stabSub_commSub_inf_fixV L
  have hBN : B ≤ normalizer (L : Set (MulAut W)) := hB
  have hBU : B ≤ stabSub U := by
    rw [hU]
    intro b hb
    exact StabLat.mem_stabSub_commSub (X := L) (Y := ⊤)
      (mem_stabSub_top b) (hBN hb)
  have hBZ : B ≤ stabSub Z := by
    rw [hZ, hU, ← commV_eq_commSub, inf_comm]
    exact B5.le_stabSub_fixV_inf_commV (G := B) (L := L)
      (fun b hb x hx => (Subgroup.mem_normalizer_iff.mp (hBN hb) x).mp hx)
      (fun b hb => B.inv_mem hb)
  have hfaith : L ⊓ centSec U Z = ⊥ := by
    rw [hZ]
    exact s16h_H5_faithful_on_quotient hc (center_eq_bot_of_isL3 hL3)
  set Λ : Subgroup (MulAut (Sec U Z)) := autSec L U Z with hΛ
  let e : ↥L ≃* ↥Λ := CFSG.Quasithin.B5.secEquiv L hLU hLZ hfaith
  have hL3Λ : IsL3 ↥Λ 1 := CFSG.Blueprint.LieModel.of_mulEquiv e hL3
  have hcent : Subgroup.centralizer (Λ : Set (MulAut (Sec U Z))) = ⊥ := by
    rw [hΛ]
    exact s16h_H5_rowSt8_sec_centralizer_eq_bot hc ⟨hL3, h8⟩ hirr
  have hHe : (L ⊔ B) ≤ normalizer (L : Set (MulAut W)) := by
    refine sup_le Subgroup.le_normalizer fun b hb => hBN hb
  have hHstable : autSec (L ⊔ B) U Z ≤ normalizer (Λ : Set (MulAut (Sec U Z))) := by
    refine CFSG.Quasithin.FFC.Sp4Off.autSec_le_normalizer (L := L) (M := L ⊔ B)
      le_sup_left (sup_le hLU hBU) (sup_le hLZ hBZ) ?_
    intro g hg l hl
    exact (Subgroup.mem_normalizer_iff.mp (hHe hg) l).mp hl
  have hBle : autSec B U Z ≤ autSec (L ⊔ B) U Z := autSec_mono le_sup_right U Z
  have hBnorm : autSec B U Z ≤ normalizer (Λ : Set (MulAut (Sec U Z))) := by
    rw [hΛ]
    exact hBle.trans hHstable
  let ρ : ↥(autSec B U Z) →* MulAut Λ :=
    (Subgroup.normalizerMonoidHom Λ).comp (Subgroup.inclusion hBnorm)
  have hmem_ker : ∀ y : ↥(autSec B U Z),
      y ∈ ρ.ker ↔ (y : MulAut (Sec U Z)) ∈ Subgroup.centralizer (Λ : Set (MulAut (Sec U Z))) := by
    intro y
    rw [MonoidHom.mem_ker]
    change (Subgroup.normalizerMonoidHom Λ) (Subgroup.inclusion hBnorm y) = 1 ↔
      (y : MulAut (Sec U Z)) ∈ Subgroup.centralizer (Λ : Set (MulAut (Sec U Z)))
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  have hker_map : ρ.ker.map (Subgroup.subtype (autSec B U Z)) =
      autSec B U Z ⊓ Subgroup.centralizer (Λ : Set (MulAut (Sec U Z))) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hmem_ker y).mp hy⟩
    · rintro ⟨hx, hxc⟩
      exact ⟨⟨x, hx⟩, (hmem_ker ⟨x, hx⟩).mpr hxc, rfl⟩
  have hker_bot : ρ.ker = ⊥ :=
    Subgroup.map_injective (Subgroup.subtype_injective _)
      (by rw [hker_map, hcent, Subgroup.map_bot, inf_bot_eq])
  have hcard : Nat.card ↥(autSec B U Z) = Nat.card ↥ρ.range := by
    have h := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥(autSec B U Z)) ρ
    rw [Subgroup.map_top, top_inf_eq, hker_bot, Subgroup.card_bot, mul_one,
      Subgroup.card_top] at h
    exact h.symm
  have hrangeDvd : Nat.card ↥ρ.range ∣ Nat.card (MulAut Λ) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  have hautDvd : Nat.card (MulAut Λ) ∣ 336 := card_mulAut_dvd_of_isL3 hL3Λ
  have hsecDvd : Nat.card ↥(autSec B U Z) ∣ 336 := by
    rw [hcard]
    exact hrangeDvd.trans hautDvd
  rw [s16h_H5_card_autSub_eq_autSec_of_le_normalizer hc hB]
  exact hsecDvd

end BlockNormalizer


theorem s168e3_exists_H5Cfg {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1) :
    ∃ t : MulAut (Vtil V₀ V hV),
      s16h_H5Cfg (Mbar D.M V₀ V hV) (lBar V₀ V hV L) t := by
  obtain ⟨t, ht, ht2, ht1, htr, hW⟩ := c.conc
  have hW2 : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  refine ⟨t, hW2, ht, ht2, ht1, htr, hW, hcomp, ?_⟩
  have hcardH : Nat.card ↥(lBar V₀ V hV L) = 168 := card_eq_of_isL3 hL
  intro q hq hq2
  by_contra h
  have h2 : 2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L) := by omega
  have hdvd : q ^ 2 ∣ Nat.card ↥(lBar V₀ V hV L) :=
    CFSG.CGT.Foote82.MC2.sq_dvd_card_of_two_le_pRank hq.one_lt h2
  rw [hcardH] at hdvd
  have h336 : 2 ^ 3 * 3 * 7 = 168 := by norm_num
  rw [← h336] at hdvd
  have hq_dvd : q ∣ 2 ^ 3 * 3 * 7 :=
    dvd_trans (dvd_pow_self q (by norm_num : (2 : ℕ) ≠ 0)) hdvd
  have hqmem : q = 2 ∨ q = 3 ∨ q = 7 := by
    rcases hq.dvd_mul.1 hq_dvd with h' | h'
    · rcases hq.dvd_mul.1 h' with h'' | h''
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
          (hq.dvd_of_dvd_pow h''))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h''))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).1 h'))
  rcases hqmem with rfl | rfl | rfl
  · exact hq2 rfl
  · norm_num at hdvd
  · norm_num at hdvd

theorem s168e3_one_lt_s {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8) :
    1 < s15 D.M V₀ V hV L := by
  by_contra hle
  have hs1 : s15 D.M V₀ V hV L = 1 := by
    have hpos := s15_Eleven_pos_s D c.setting.hyp151 hV
    omega
  obtain ⟨t, hc⟩ := s168e3_exists_H5Cfg c hcomp hL
  have hWtop : wTil V₀ V hV L = ⊤ :=
    c8_wTil_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs1
  have hAN : Mbar D.M V₀ V hV ≤
      normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro φ hφ
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (c8_map_conj_lbar_eq D.M V₀ V hV L hs1 φ hφ)
  have hcardDvd : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 336 := by
    have h := s16h_H5_rowSt8_autSub_card_dvd hc ⟨hL, h8⟩ hirr
      (B := Mbar D.M V₀ V hV) hAN
    change Nat.card ↥(autSub (Mbar D.M V₀ V hV) (wTil V₀ V hV L)) ∣ 336 at h
    rw [hWtop] at h
    rwa [Nat.card_congr (CFSG.Quasithin.autSubTopEquiv (Mbar D.M V₀ V hV)).toEquiv] at h
  obtain ⟨q, hq⟩ := c.std.hx.sig_nonempty
  have hqprime := (D.sig_prime q hq).1
  have hq2 : q ≠ 2 := (D.sig_prime q hq).2
  have h2 : 2 ≤ CFSG.Open.pRank q (Mbar D.M V₀ V hV) := c.two_le_pRank_mbar hq
  have hqdvd := CFSG.CGT.Foote82.MC2.sq_dvd_card_of_two_le_pRank hqprime.one_lt h2
  have hq2dvd : q ^ 2 ∣ 336 := hqdvd.trans hcardDvd
  have h336 : 2 ^ 4 * 3 * 7 = 336 := by norm_num
  rw [← h336] at hq2dvd
  have hq_dvd : q ∣ 2 ^ 4 * 3 * 7 :=
    dvd_trans (dvd_pow_self q (by norm_num : (2 : ℕ) ≠ 0)) hq2dvd
  have hqmem : q = 2 ∨ q = 3 ∨ q = 7 := by
    rcases hqprime.dvd_mul.1 hq_dvd with h' | h'
    · rcases hqprime.dvd_mul.1 h' with h'' | h''
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).1
          (hqprime.dvd_of_dvd_pow h''))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).1 h''))
    · exact Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hqprime (by norm_num : Nat.Prime 7)).1 h'))
  rcases hqmem with rfl | rfl | rfl
  · exact hq2 rfl
  · norm_num at hq2dvd
  · norm_num at hq2dvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
