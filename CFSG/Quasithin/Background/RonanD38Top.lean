module

public import CFSG.Quasithin.Background.RonanD38Swap
public import CFSG.Quasithin.Background.RonanD38Pair

public section

namespace CFSG.Quasithin.RonanD38

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch10.SecA

section Top

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d38_qstar_pair
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Facts10_1) (hD : D3Std M Mp T L V)
    (htop : orbSup T V = ⊤) (htT : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) {n : ℕ} (hszL : CFSG.Blueprint.SuzukiModel ↥L 2 n)
    (hc : D36cConcl Mp T L V t) {A : Subgroup (MulAut W)} (hAT : A ≤ T) (hA : IsElemAbelian2 A)
    (hA3 : commSeries A 3 = ⊥) (hr : rAV A ≤ 2) : A ≤ stabSub V := by
  obtain ⟨hBN, -, hVU, hVfix, -⟩ := d38_pair hB45 hA21 hF hD htT htn hMp hszL hc
  have hL38 : A38Types ↥L := Or.inr (Or.inl ⟨n, hszL⟩)
  obtain ⟨hV0, ⟨hsum0, -⟩, hqU, -⟩ := hc
  have hUV : commSub (orbSup T V) L = V := hVU.symm
  have hcomm : commV L = V := by
    rw [commV_eq_commSub, ← htop]
    exact hUV
  have hN := insp5a_normalizes hD.hyp htT htn hMp hV0 hcomm hL38
  have hQ := insp5a_qsec hD.hyp htT htn hMp hV0 hcomm hL38 hN
  have hS := insp5a_sqtk hA21 hD.hyp hcomm hL38
  obtain ⟨e⟩ := insp5a_equiv hD.hyp hcomm hL38
  have hLs : IsSimpleGroup ↥L := insp5a_sec_isSimpleGroup hL38
  have hsK : IsSimpleGroup ↥(autSub L V) := e.symm.isSimpleGroup
  have hszK : ∃ n, CFSG.Blueprint.SuzukiModel ↥(autSub L V) 2 n :=
    ⟨n, H13.suzukiModel_congr e.symm hszL⟩
  have hexpV : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [← qhatOf_autSub_congr hUV]
    exact hqU
  have h2sec := H13.two_le_qhatOf_autSec_of_suzuki hB45 hF hexpV hQ hS hsK hszK hqV
  have hV'c : V.map t.toMonoidHom = commV (conjAutSub t L) := by
    rw [← hcomm, H13.map_commV_conjAutSub]
  have hmapV : ∀ g ∈ Mp ⊔ T, (V.map g.toMonoidHom = V ∧
      (V.map t.toMonoidHom).map g.toMonoidHom = V.map t.toMonoidHom) ∨
      (V.map g.toMonoidHom = V.map t.toMonoidHom ∧
        (V.map t.toMonoidHom).map g.toMonoidHom = V) := by
    intro g hg
    rcases H13.d38_conj_pair hD.hyp htT htn hMp hL38 g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      constructor
      · rw [← hcomm, H13.map_commV_conjAutSub, h1]
      · rw [hV'c, H13.map_commV_conjAutSub, h2]
    · right
      constructor
      · rw [← hcomm, H13.map_commV_conjAutSub, h1, ← hV'c, hcomm]
      · rw [hV'c, H13.map_commV_conjAutSub, h2, hcomm]
  have hsum : V ⊔ V.map t.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine orbSup_le fun s hs => ?_
    rcases hmapV s (Subgroup.mem_sup_right hs) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact le_sup_right
  have hDV : V ⊓ V.map t.toMonoidHom ≤ V ⊓ fixV Mp := by
    rintro x ⟨hxV, hxV'⟩
    rw [hUV] at hsum0
    exact ⟨hxV, (hsum0.2 ⟨Subgroup.mem_sup_left hxV, Subgroup.mem_sup_left hxV'⟩).2⟩
  have hfixVL : V ⊓ fixV Mp = V ⊓ fixV L := by
    rw [hMp, fixV_sup_eq_inf_fixV]
    exact le_antisymm (inf_le_inf_left _ inf_le_left)
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hVfix)))
  have hV3 : 3 + rk ↥(V ⊓ fixV Mp) ≤ rk ↥V := by
    rw [hfixVL]
    exact three_add_rk_le_of_binaryNaturalSz inf_le_left hBN
  by_contra hnot
  obtain ⟨a, haA, haV⟩ := SetLike.not_le_iff_exists.mp hnot
  have hperm : ∀ b ∈ A, (b ∈ stabSub V ∧ b ∈ stabSub (V.map t.toMonoidHom)) ∨
      (V.map b.toMonoidHom = V.map t.toMonoidHom ∧
        (V.map t.toMonoidHom).map b.toMonoidHom = V) := by
    intro b hb
    rcases hmapV b (Subgroup.mem_sup_right (hAT hb)) with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨H13.mem_stabSub_of_map_eq' h1, H13.mem_stabSub_of_map_eq' h2⟩
    · exact Or.inr h
  have hsub : ∀ B ≤ A, IsElemAbelian2 B ∧ commSeries B 3 = ⊥ ∧ B ≤ Mp ⊔ T := fun B hBA =>
    ⟨⟨fun a ha b hb => hA.1 a (hBA ha) b (hBA hb), fun a ha => hA.2 a (hBA ha)⟩,
      le_bot_iff.mp (hA3 ▸ commSeries_mono hBA 3), (hBA.trans hAT).trans le_sup_right⟩
  have hlt := two_mul_rk_lt_rkIdx_of_swap hsum hDV hA hperm haA haV hV3 fun B hBA hBV hne => by
    obtain ⟨hBe, hB3, hBX⟩ := hsub B hBA
    exact H13.two_mul_rk_autSub_le_sec hQ h2sec hBX hBV hBe hB3 hne
  have hAne : A ≠ ⊥ := fun h => by
    rw [h, Subgroup.mem_bot] at haA
    exact haV (by rw [haA]; exact (stabSub V).one_mem)
  have hpos := hA.rk_pos hAne
  have hpos' : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hpos
  unfold rAV at hr
  rw [div_le_iff₀ hpos'] at hr
  have hle : rkIdx (fixV A) ≤ 2 * rk ↥A := by exact_mod_cast hr
  omega

theorem d38_qstar_top
    (h38 : Vol2Native.A38ForSQTKCat) (h35 : D35) (h36 : D36c)
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Facts10_1) (hD : D3Std M Mp T L V)
    (htop : orbSup T V = ⊤) (hVne : V ≠ ⊤)
    (hsz : ∃ n, CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n)
    {A : Subgroup (MulAut W)} (hAT : A ≤ T) (hA : IsElemAbelian2 A) (hA3 : commSeries A 3 = ⊥)
    (hr : rAV A ≤ 2) : A ≤ stabSub V := by
  have hcases := H13.d38_mp_cases h38 hD.hyp
  obtain ⟨hLs, n, hszL⟩ := H13.d38_simple_sz hD.hyp hcases hsz
  rcases hcases with hMp | ⟨t, htT, htn, hMp⟩
  · exact absurd ((d38_VT_of_eq h35 hD hMp hLs hszL).trans htop) hVne
  · have hlt : V < orbSup T V := by
      rw [htop]
      exact lt_top_iff_ne_top.mpr hVne
    rcases h36 W M Mp T L V hD hlt t htT htn hMp with hc | hc
    · exact d38_qstar_pair hB45 hA21 hF hD htop htT htn hMp hszL hc hAT hA hA3 hr
    · have hMp' : Mp = conjAutSub t L ⊔ conjAutSub t⁻¹ (conjAutSub t L) := by
        rw [conjAutSub_inv_conjAutSub, sup_comm]
        exact hMp
      have hstd' : D3Std M Mp T (conjAutSub t L) V := ⟨hD.hyp.conj htT, hD.qhat, hD.irrT⟩
      let e := Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
      have hsz' : CFSG.Blueprint.SuzukiModel ↥(conjAutSub t L) 2 n :=
        H13.suzukiModel_congr e.symm hszL
      exact d38_qstar_pair hB45 hA21 hF hstd' htop (T.inv_mem htT)
        (not_mem_normalizer_conjAutSub htn) hMp' hsz' hc hAT hA hA3 hr

end Top

end CFSG.Quasithin.RonanD38
