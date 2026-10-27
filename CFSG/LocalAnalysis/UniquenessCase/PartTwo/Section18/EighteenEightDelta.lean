module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightInputs
public import CFSG.Quasithin.Vol2.Ch10SecI1CovNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapesSzSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Nat18_8 (D : Data G) (V : Subgroup G) (L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Prop :=
  ¬ fixV (barSub ⊥ V hV (CFSG.LocalAnalysis.UniquenessCase.UC22.conjClosure D.M L)) = ⊥ →
    ∃ n : ℕ, 1 < n ∧ IsL2 ↥(barSub ⊥ V hV L) n ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        (FFModel.nat (StatedSL 2 K)).Realizes
          (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L)) ⊤
          (fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L)))

theorem delta15_eq_zero_of_fixV_eq_bot {D : Data G} {V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D ⊥ V p L) (h151 : Hyp151 D ⊥ V L)
    (hfix : fixV (barSub ⊥ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥) :
    delta15 D.M ⊥ V h.hyp125.isElemAbelian L = 0 := by
  classical
  have hV := h.hyp125.isElemAbelian
  set X : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    barSub ⊥ V hV (UC22.conjClosure D.M L) with hX
  set I : Subgroup (Vtil ⊥ V hV) :=
    imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) with hI
  have hIle : I ≤ fixV X := by
    have hMs : D.M ≤ stabTil ⊥ V :=
      le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
    have hXeq : X = ⨆ m : D.M, barSub ⊥ V hV (conjSubgroup L (m : G)⁻¹) := by
      rw [hX, UC22.uc22br4_conjClosure_eq]
      rw [barSub_iSup_of_le hV (K := fun g : D.M =>
        L.map (MulAut.conj (g : G)).toMonoidHom) (by
          intro g x hx
          obtain ⟨l, hl, rfl⟩ := hx
          simpa [MulAut.conj_apply] using
            hMs (D.M.mul_mem (D.M.mul_mem g.2 (h.hL.1.1.le hl)) (D.M.inv_mem g.2)))]
      exact iSup_congr fun g => by rw [conjSubgroup, inv_inv]
    have hIleV1 : I ≤ imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono V inf_le_left)
    intro w hw
    rw [hXeq, mem_fixV]
    intro g hg
    have hle : (⨆ m : D.M, barSub ⊥ V hV (conjSubgroup L (m : G)⁻¹)) ≤
        MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) w :=
      iSup_le fun m g' hg' =>
        MulAction.mem_stabilizer_iff.mpr
          ((mem_fixV.mp
            (s15_Core_imgTil_v1Sub_le_fixV h151 (D.M.inv_mem m.2) (hIleV1 hw))) g' hg')
    exact MulAction.mem_stabilizer_iff.mp (hle hg)
  have hIbot : I = ⊥ := le_bot_iff.1 (hIle.trans (le_of_eq hfix))
  have hrk : rk ↥I = delta15 D.M ⊥ V hV L := by
    have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V
      (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) hV
      (inf_le_right.trans (preTil_le ⊥ V hV _))
    have hzero : (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ⊓ ⊥ = ⊥ :=
      inf_eq_right.mpr bot_le
    rw [show imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) = I from rfl,
      hzero] at h
    have hzero' : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk]
    have h' : mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) = rk ↥I := by
      simpa [hzero'] using h
    rw [show delta15 D.M ⊥ V hV L =
      mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) from rfl]
    exact h'.symm
  rw [← hrk, hIbot]
  simp [rk]

theorem card_fixV_autSub_le_of_realizes {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    {n : ℕ} (hn : 1 < n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hcommW : commSub (wTil ⊥ V hV L) (barSub ⊥ V hV L) = wTil ⊥ V hV L)
    (hR : (FFModel.nat (StatedSL 2 K)).Realizes
      (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L)) ⊤
      (fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L)))) :
    Nat.card ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) ≤ 2 ^ n := by
  have : CharP K 2 := uc22p22d_charP_two (by omega) hK
  letI : Fintype K := Fintype.ofFinite K
  have hst : barSub ⊥ V hV L ≤ stabSub (wTil ⊥ V hV L) := by
    intro g hg
    exact StabLat.mem_stabSub_commSub (by intro u; exact Iff.rfl)
      (Subgroup.le_normalizer hg)
  have hcomm : commV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L)) = ⊤ := by
    refine Subgroup.map_injective (f := (wTil ⊥ V hV L).subtype)
      (Subgroup.subtype_injective _) ?_
    rw [B15P4.map_subtype_commV_autSub hst, hcommW, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hW2 : ∀ w : ↥(wTil ⊥ V hV L), w ^ 2 = 1 :=
    fun w => Subtype.ext (by
      simpa using s15_Infra_vtil_sq_eq_one ⊥ V hV (w : Vtil ⊥ V hV))
  exact CFSG.Quasithin.ASInputs.C10KH.sl2Cover_card_le (K := K) hW2 le_rfl hcomm hR
    (d := n) fun ρ hρ => by
      have hF : Fintype.card K = 2 ^ n := by rw [Fintype.card_eq_nat_card, hK]
      have h1 := JonesParshall.finrank_H1_SL2 (F := K) (Γ := ↥(StatedSL 2 K)) (W := _)
        (ρ := ρ) (a := n) hF hn hρ
      exact le_of_eq h1

theorem delta15_lt_of_p18_6_5_of_nat (D : Data G) {V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D ⊥ V p L) (h151 : Hyp151 D ⊥ V L)
    (hLb : barSub ⊥ V h.hyp125.isElemAbelian L ≠ ⊥)
    (hnat : Nat18_8 D V L h.hyp125.isElemAbelian) :
    delta15 D.M ⊥ V h.hyp125.isElemAbelian L <
      gamma15 D.M ⊥ V h.hyp125.isElemAbelian L - 1 := by
  classical
  have hV := h.hyp125.isElemAbelian
  by_cases hfix : fixV (barSub ⊥ V hV (UC22.conjClosure D.M L)) = ⊥
  ·
    have hδ0 := delta15_eq_zero_of_fixV_eq_bot h h151 hfix
    have hγ2 := two_le_gamma15 D h151 hV hLb
    omega
  ·
    obtain ⟨n, hn, -, K, hField, hFinite, hK, hR⟩ := hnat hfix
    letI : Field K := hField
    have : Finite K := hFinite
    have hcommW : commSub (wTil ⊥ V hV L) (barSub ⊥ V hV L) = wTil ⊥ V hV L := by
      have h1 := s15_Core_commSub_wTil_conj h151 (m := (1 : G)) D.M.one_mem
      simpa only [conjSubgroup_one] using h1
    have hZle := card_fixV_autSub_le_of_realizes hV hn hK hcommW hR
    obtain ⟨π, hRV⟩ := hR
    have hmod : Nat.card (FFModel.nat (StatedSL 2 K)).Mod = Nat.card K ^ 2 :=
      G64.card_natMod (StatedSL 2 K)
    have hcardV : Nat.card ↥(wTil ⊥ V hV L) =
        Nat.card (FFModel.nat (StatedSL 2 K)).Mod *
          Nat.card ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) := by
      have h := G64.RealizesVia.card_eq hRV
      simpa [Subgroup.card_top] using h
    have hW2 : ∀ w : ↥(wTil ⊥ V hV L), w ^ 2 = 1 :=
      fun w => Subtype.ext (by
        simpa using s15_Infra_vtil_sq_eq_one ⊥ V hV (w : Vtil ⊥ V hV))
    have hZ2 : ∀ z : ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))), z ^ 2 = 1 :=
      fun z => Subtype.ext (by
        have h := hW2 (z : ↥(wTil ⊥ V hV L))
        simpa using h)
    have hWpow : Nat.card ↥(wTil ⊥ V hV L) = 2 ^ rk ↥(wTil ⊥ V hV L) :=
      card_eq_two_pow_rk hW2
    have hZpow : Nat.card ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) =
        2 ^ rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) :=
      card_eq_two_pow_rk hZ2
    have h22 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
      rw [← pow_mul, Nat.mul_comm]
    have hpow : 2 ^ rk ↥(wTil ⊥ V hV L) =
        2 ^ (2 * n +
          rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L)))) := by
      calc 2 ^ rk ↥(wTil ⊥ V hV L) = Nat.card ↥(wTil ⊥ V hV L) := hWpow.symm
        _ = Nat.card (FFModel.nat (StatedSL 2 K)).Mod *
              Nat.card ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) := hcardV
        _ = Nat.card K ^ 2 *
              2 ^ rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) := by
              rw [hmod, hZpow]
        _ = (2 ^ n) ^ 2 *
              2 ^ rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) := by rw [hK]
        _ = 2 ^ (2 * n) *
              2 ^ rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) := by rw [h22]
        _ = 2 ^ (2 * n +
              rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L)))) := by rw [pow_add]
    have hrkW : rk ↥(wTil ⊥ V hV L) = 2 * n +
        rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    have hmSubW : mSub (wSub ⊥ V hV L) = rk ↥(wTil ⊥ V hV L) := by
      have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V (wSub ⊥ V hV L) hV
        (preTil_le ⊥ V hV _)
      have hzero : wSub ⊥ V hV L ⊓ ⊥ = ⊥ := inf_eq_right.mpr bot_le
      rw [hzero] at h
      have hzero' : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk]
      rw [hzero', add_zero, wSub, imgTil_preTil] at h
      exact h
    have hgamma : gamma15 D.M ⊥ V hV L + delta15 D.M ⊥ V hV L = 2 * n +
        rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) := by
      rw [← mSub_wSub D h.hyp125 hV, hmSubW, hrkW]
    have hδle : delta15 D.M ⊥ V hV L ≤
        rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) := by
      have hIeq : rk ↥(imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L)) =
          delta15 D.M ⊥ V hV L := by
        have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V
          (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) hV
          (inf_le_right.trans (preTil_le ⊥ V hV _))
        have hzero : (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ⊓ ⊥ = ⊥ :=
          inf_eq_right.mpr bot_le
        rw [hzero] at h
        have hzero' : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk]
        have h' : mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) =
            rk ↥(imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L)) := by
          simpa [hzero'] using h
        rw [show delta15 D.M ⊥ V hV L =
          mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) from rfl]
        exact h'.symm
      rw [← hIeq]
      have hIleW : imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤
          wTil ⊥ V hV L := by
        have h := Subgroup.map_mono (f := mkTil ⊥ V hV)
          (Subgroup.subgroupOf_mono V (inf_le_right :
            v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L ≤ wSub ⊥ V hV L))
        change imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤
          imgTil ⊥ V hV (wSub ⊥ V hV L) at h
        rwa [wSub, imgTil_preTil] at h
      have hIleFix : imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤
          fixV (barSub ⊥ V hV L) := by
        have h0 := Subgroup.map_mono (f := mkTil ⊥ V hV)
          (Subgroup.subgroupOf_mono V (inf_le_left :
            v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L ≤ v1Sub D.M ⊥ V hV L))
        change imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤
          imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) at h0
        exact h0.trans (by
          simpa only [conjSubgroup_one] using
            s15_Core_imgTil_v1Sub_le_fixV h151 (m := (1 : G)) D.M.one_mem)
      have hst : barSub ⊥ V hV L ≤ stabSub (wTil ⊥ V hV L) := by
        intro g hg
        exact StabLat.mem_stabSub_commSub (by intro u; exact Iff.rfl)
          (Subgroup.le_normalizer hg)
      calc rk ↥(imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L))
          ≤ rk ↥(wTil ⊥ V hV L ⊓ fixV (barSub ⊥ V hV L)) :=
            rk_mono (le_inf hIleW hIleFix)
        _ = rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) :=
            (rk_fixV_autSub hst).symm
    have hc : rk ↥(fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) ≤ n := by
      rw [hZpow] at hZle
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hZle
    omega


theorem fixV_or_classicalEvenAltG2Der (D : Data G) (h640 : UC6.R6_40_2 D)
    (hFF : W4Thm12McClurg) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hUL : UniqueMax D.M L)
    (hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥) :
    fixV (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ ∨
      (V₀ = ⊥ ∧ ClassicalEvenAltG2Der (UC22.Bar2 L) ∧
        ⁅barSub V₀ V h.hyp125.isElemAbelian (F12.jOf D.T),
          barSub V₀ V h.hyp125.isElemAbelian L⁆ ≠ ⊥) := by
  have hLM : L ≤ D.M := h.hL.1.1.le
  have hcomp : F12.IsComponentModO2 D.M (L ⊔ pCoreOf 2 D.M) :=
    isComponentModO2_sup_pCoreOf_of_mem_calC h.hL.1
  have hU : UniqueMax D.M ((L ⊔ pCoreOf 2 D.M) ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D
      ((le_sup_left : L ≤ L ⊔ pCoreOf 2 D.M).trans le_sup_left)
      (sup_le (sup_le hLM (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)) D.sylowM.le) hUL
  have hbar : barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) =
      barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) :=
    barSub_conjClosure_sup_pCoreOf h.hyp125 hLM
  have hH : barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) ≠ ⊥ := by
    rw [hbar]
    exact TwelveTwentyThree.barSub_conjClosure_ne_bot h.hyp125.isElemAbelian hLb
  rcases eq_or_ne V₀ ⊥ with rfl | hV0ne
  · rcases twelve_twentySix D h640 hFF h.hyp125 hcomp hU hH with hfix | ⟨-, hcl, hJ⟩
    · left
      rwa [hbar] at hfix
    · right
      refine ⟨rfl, ?_, ?_⟩
      · obtain ⟨e⟩ := bar2_sup_pCoreOf_mulEquiv_of_mem_calC h.hL.1
        exact S17.classicalEvenAltG2Der_of_mulEquiv e.symm hcl
      · have hKbar : barSub ⊥ V h.hyp125.isElemAbelian (L ⊔ pCoreOf 2 D.M) =
            barSub ⊥ V h.hyp125.isElemAbelian L :=
          barSub_sup_pCoreOf_eq_of_hyp125 h.hyp125 hLM
        rwa [hKbar] at hJ
  · left
    rcases twelve_twentySix D h640 hFF h.hyp125 hcomp hU hH with hfix | ⟨hbot, -⟩
    · rwa [hbar] at hfix
    · exact absurd hbot hV0ne

section CertifiedShape


theorem shape18_6_of_ne {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (h18_4 : R18_4At D V₀ V p L) (hXL : UC22.conjClosure D.M L ≠ L) :
    (IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L)) ∧
      2 < S17.nOf L ∧ (conjSetOf D.M L).ncard = 2 := by
  obtain ⟨n, x, hxM, hXsup, -, hshape, -⟩ :=
    S17.p42_alt2_of_ne (D := D) (V₀ := V₀) (V := V) h1742 (p := p) h.hp
      (L := L) h.hL.1 hXL
  have hncard : (conjSetOf D.M L).ncard = 2 :=
    S17.ncard_eq_two_of_p42 h.hL.1 hxM hXsup hXL
  refine ⟨?_, ?_, hncard⟩
  · rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
    · have hnof : S17.nOf L = n := S17.nOf_eq_of_isL2 hL2
      exact Or.inl (hnof.symm ▸ hL2)
    · have hnof : S17.nOf L = n := S17.nOf_eq_of_isSz hSz
      exact Or.inr (hnof.symm ▸ hSz)
  · rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
    · have hnof : S17.nOf L = n := S17.nOf_eq_of_isL2 hL2
      rw [hnof]
      have hadm := CFSG.Blueprint.LieModel.admissible hL2
      simp only [CFSG.Open.StatedLieAdmissible] at hadm
      obtain ⟨-, hnpos, -, hne1, -⟩ := hadm
      have hn1 : n ≠ 1 := by
        intro hn
        subst hn
        exact hne1 (by norm_num)
      have hn2 : n ≠ 2 := by
        intro hn
        subst hn
        have hSC : CFSG.Open.StatedClassicalModel (Bar2 L) .PSL 2 2 2 :=
          CFSG.Blueprint.LieModel.statedClassicalModel hL2 (by decide)
        have hsimple : IsSimpleGroup (Bar2 L) :=
          (CFSG.LieType.Simplicity.fam_PSL_simplicity (Bar2 L) 2 2 2 hSC).2
        have hcard : Nat.card (Bar2 L) = 60 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hSC
        exact h18_4
          (CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard)
      omega
    · have hnof : S17.nOf L = n := S17.nOf_eq_of_isSz hSz
      rw [hnof]
      have hadm := CFSG.Blueprint.LieModel.admissible hSz
      simp only [CFSG.Open.StatedLieAdmissible] at hadm
      obtain ⟨-, -, -, -, hodd, hge3⟩ := hadm
      omega

end CertifiedShape

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
