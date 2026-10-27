module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121B
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3R136b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
import CFSG.GroupTheory.PGroup.PrimePartTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13
import CFSG.LocalAnalysis.UniquenessCase.UC22P20m
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3R847

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem s21_21B_three_of_r847E3
    (hSE : StronglyEmbeddedFive) (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hS : Standing G) (hUC : rankThreeUC G) (S : Setup G) {Ch : Choice2011 G}
    (h78 : R7_8R3p3 (PartTwo.Three.dataOfSetup hS S))
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h846 : F08.R846 (PartTwo.Three.dataOfSetup hS S))
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S))
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h216 : S21_16 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h218 : S21_18 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h2119 : S21_19 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h219 : S21_9Sig3 (PartTwo.Three.dataOfSetup hS S) Ch) :
    S21_21B (PartTwo.Three.dataOfSetup hS S) Ch := by
  intro h1930 c hB hH p hp
  have hSig := UC6S846.sigmaStd_dataOfSetup hS S
  have h61 := PartTwo.Three.r6_1_dataOfSetup hS S
  have hS13 := uc22s2121e3_setting13_r847E3 hThin hCyc hSig h61 h847T h211 h216 h218 h219 h2119
    hS.rank h1930 c hH
  obtain ⟨L, K, n, hL, hK, hne, hall, hpL, hpK, hn, hpn, hK2, hLs, hrB⟩ :=
    uc22s2121e3_r136b_r847E3 hSE hThin hCyc hS S hS13 hSig h847T h847S h78 h82
      (fun _ hL => uc22s2121e3_shape hThin hCyc hS13 hSig
        (PartTwo.Three.sigmaRankThree13_dataOfSetup hS hUC S) h846
        (uc22s2121e3_r847Four_of_r847E3Thin h847T h61 c hH) hL) hp
      (uc22s13xe_case136b hThin hCyc hSig hS13.hyp131.thinOrU3 hS13.hyp131.normal hS13.sig_eq
        h1930 c hB hH hp) c.hB.2.1
  obtain ⟨hpp, hp2⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  have hns : PartTwo.s13_NormalSimple (Bar2 S.M) := PartTwo.s13_normalSimple hThin _ hS13
  have hlay : CFSG.perfectResidual (Bar2 S.M) = CFSG.layer (Bar2 S.M) := hS13.hyp131.layer
  have hLc := PartTwo.s13_barImage_isComponent hL
  have hKc := PartTwo.s13_barImage_isComponent hK
  have hE2 : CFSG.layer (Bar2 S.M) = barImage S.M L ⊔ barImage S.M K := by
    refine le_antisymm ?_ (sup_le (CFSG.LocalCores.component_le_layer hLc)
      (CFSG.LocalCores.component_le_layer hKc))
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun J hJ => ?_
    rcases hall J hJ with rfl | rfl
    exacts [le_sup_left, le_sup_right]
  have hLp : barImage S.M (F13.Lp S.M p) = CFSG.layer (Bar2 S.M) := by
    refine le_antisymm (PartTwo.s13_barImage_Lp_le_layer S.M p) ?_
    rw [PartTwo.s13_barImage_Lp S.M hpp, PartTwo.s13_pElementSubgroup_layer_eq hns hpp, hE2]
    exact sup_le
      (le_iSup₂ (f := fun J (_ : J ∈ PartTwo.s13_compsP (Bar2 S.M) p) => J) _
        (PartTwo.s13_mem_compsP.mpr ⟨hLc, hpL⟩))
      (le_iSup₂ (f := fun J (_ : J ∈ PartTwo.s13_compsP (Bar2 S.M) p) => J) _
        (PartTwo.s13_mem_compsP.mpr ⟨hKc, hpK⟩))
  have hLpM := PartTwo.s13_Lp_le S.M p
  have hHM : (Hinf S.M).subgroupOf S.M = CFSG.perfectResidual ↥S.M :=
    Subgroup.comap_map_eq_self_of_injective S.M.subtype_injective _
  have hle1 : Hinf S.M ≤ F13.Lp S.M p := by
    refine uc22p20m_le_of_perfect_sup (uc22p21c_Hinf_perfect S.M) (fun x hx => ?_)
      ((uc22p21c_pCoreOf_le S.M).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hLpM).1 (PartTwo.s13_Lp_normal S.M p)))
      (uc22p21c_isPGroup_pCoreOf S.M)
    obtain ⟨hxM, hxE⟩ := uc22p21c_mem_barPreimage.1
      ((uc22p21c_Hinf_le_oTwoE_iff S.M).2 hlay.le hx)
    rw [← hLp] at hxE
    obtain ⟨l, hl, hlx⟩ := uc22p21c_mem_barImage.1 hxE
    obtain ⟨z, hz, hlz⟩ := (QuotientGroup.mk'_eq_mk' _).1 hlx
    have hx' : (l : G) * (z : G) = x := by
      rw [← Subgroup.coe_mul, hlz]
    rw [← hx']
    exact Subgroup.mul_mem_sup hl ((CFSG.mem_openPCoreOf_iff z).2 hz)
  have hle2 : F13.Lp S.M p ≤ Hinf S.M := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxX, k, hk⟩
    obtain ⟨hxM, hxE⟩ := (uc22p21c_mem_barPreimage (M := S.M)
      (Y := CFSG.layer (Bar2 S.M))).1 hxX
    refine PartTwo.s13_mem_of_barImage_of_pPart (uc22p21c_Hinf_le S.M)
      (by rw [hHM]; infer_instance) hpp hp2 hxM ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩ ?_
    rw [show barImage S.M (Hinf S.M) = CFSG.perfectResidual (Bar2 S.M) from
      (congrArg (Subgroup.map (uc22p21cPi S.M)) hHM).trans
        (uc22p21c_map_perfectResidual _ (uc22p21c_pi_surjective S.M)), hlay]
    exact hxE
  obtain ⟨e₁, -⟩ := uc22p20d_bar2Equiv hLpM
    (CFSG.Open.IsSubnormal.step hLpM (PartTwo.s13_Lp_normal S.M p) (.refl S.M))
  obtain ⟨e₃⟩ := RankThreeTheoremC.exists_mulEquiv_sup_prod (hns _ hLc).2
    (Subgroup.isPerfect_iff.mp hLc.1.1)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (PartTwo.s13_components_commute hns hLc hKc hne))
  obtain ⟨φL⟩ := PartTwo.s13_bar_equiv hL
  obtain ⟨φK⟩ := PartTwo.s13_bar_equiv hK
  have e : Bar2 (Opp p (oTwoEOf S.M)) ≃* Bar2 L × Bar2 K :=
    e₁.trans ((MulEquiv.subgroupCongr (hLp.trans hE2)).trans
      (e₃.trans (φL.symm.prodCongr φK.symm)))
  have hSp : F13.Sp S.M p = Opp p (barPreimage S.M (centE S.M)) :=
    congrArg (fun Y : Subgroup (Bar2 S.M) => Opp p (barPreimage S.M
      (Subgroup.centralizer (Y : Set (Bar2 S.M))))) hLp
  refine ⟨le_antisymm hle1 hle2, hS.rank, n, ?_, hn,
    PartTwo.S17.zmod_of_dvd_two_pow_add_one hpn, fun r hr => hrB r hr.1 hr.2⟩
  rcases hLs with ⟨hL2, h1⟩ | ⟨hU, h0⟩
  · have h1' : CFSG.Open.pRank p (Opp p (barPreimage S.M (centE S.M))) = 1 := by
      rw [← hSp]
      exact h1
    exact Or.inl ⟨⟨Bar2 L, Bar2 K, inferInstance, inferInstance, ⟨e⟩, hL2, hK2⟩, h1'⟩
  · have h0' : CFSG.Open.pRank p (Opp p (barPreimage S.M (centE S.M))) = 0 := by
      rw [← hSp]
      exact h0
    refine Or.inr ⟨⟨Bar2 L, Bar2 K, inferInstance, inferInstance, ⟨e⟩, hU, hK2⟩, ?_⟩
    by_contra hne0
    obtain ⟨s, hs, hso⟩ := PartTwo.s13_exists_orderOf_of_pElementSubgroup_ne_bot hpp hne0
    exact CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero hpp h0'
      ((dvd_of_eq hso.symm).trans (Subgroup.orderOf_dvd_natCard _ hs))

end CFSG.LocalAnalysis.UniquenessCase.UC22
