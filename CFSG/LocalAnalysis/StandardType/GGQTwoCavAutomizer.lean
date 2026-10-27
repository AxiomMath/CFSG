module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImageOrder
public import CFSG.LocalAnalysis.StandardType.GGQTwoB2Cav
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6Component
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartAutomizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoExceptionalComponent
public import CFSG.LocalAnalysis.StandardType.GGQTwoFullExclusions
public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryFullComponent
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavVacuous
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticFullAutomizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalCav

public section

namespace CFSG.StandardType.QTwoE6

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.NoOffTwE6Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J : Subgroup G} {x : G}

theorem four_dvd_original_automizer_of_full_label
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twE6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ 6) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  obtain ⟨K, instF, instFin, σ, hK, hσ, Fr, hFr, θ, hN, g, T, ι, b, i,
    hι, hrange, hq, hAlg, hρ, hb, hb1, hTb, hQ, hi, hιval, hg, hgn, hSlang, hScard⟩ :=
    exists_original_rational_component hS hp3 hq2 htag hmark hidx (by norm_num)
  letI : Field K := instF
  letI : Finite K := instFin
  have hY : (ggBeta L θ hN).range = TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g := by
    apply Subgroup.eq_of_le_of_card_ge hSlang
    rw [hScard, TwE6DD2.card_langCube (n := 1) le_rfl hK σ hσ Fr hFr
      (by norm_num) hg hgn]
  have hA : (ggBeta L θ hN).range ≤ (rgrpConjAut (n := 1) le_rfl hK σ hσ Fr hFr).range := by
    rw [hY, rgrpConjAut_range (n := 1) le_rfl hK σ hσ Fr hFr]
    exact TwE6DD2.langCube_le_range (n := 1) le_rfl hK σ hσ Fr hFr g
  have hcard := card_automizer_twisted_frame_eq hK σ hσ Fr hFr ι hιval
    ((J.subgroupOf L).map (ggQuotHom θ)) (ggBeta L θ hN).range hA
  rw [hi, hY, map_langCube_preimage_eq_fullThreeTorus hK σ hσ Fr hFr T hq hρ hg hgn] at hcard
  have hfour : 4 ∣ Nat.card (ggAutomizer
      (((J.subgroupOf L).map (ggQuotHom θ)).map
        (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _)) (ggBeta L θ hN).range) := by
    rw [hY, hcard]
    exact QTwoCav.four_dvd_aut_of_quasisimple_component T (Or.inl rfl) hq hAlg hρ hTb hb hb1 i hQ
  rw [QTwoCav.card_automizer_quotient_image_eq θ hS.2.1.1 hN,
    QTwoCav.card_automizer_inner_image_eq_of_setting hS
      (by rw [hp3]; exact Nat.prime_three) (by omega) hN] at hfour
  exact hfour

theorem four_dvd_original_automizer_of_heart_label
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twE6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ 5)
    (hsup : Bs ≤ L ⊔ Subgroup.zpowers x) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  obtain ⟨K, instF, instFin, σ, hK, hσ, Fr, hFr, θ, hN, g, T, ι, b, i,
    hι, hrange, hq, hAlg, hρ, hb, hb1, hTb, hQ, hi, hιval, hg, hgn, hSlang, hScard⟩ :=
    exists_original_rational_component hS hp3 hq2 htag hmark hidx le_rfl
  letI : Field K := instF
  letI : Finite K := instFin
  have hSS : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_le_centralizer hSS.2.2.2.1.1
  have hinner : (ggBeta L θ hN).range ≤
      (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _).range :=
    beta_image_inner_of_le_sup_zpowers hN hsup hxC θ
  have hY : (ggBeta L θ hN).range = TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g ⊓
      (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _).range :=
    eq_langCube_inf_inner_of_card hK σ hσ Fr hFr hg hgn hSlang hinner hScard
  have hA : (ggBeta L θ hN).range ≤ (rgrpConjAut (n := 1) le_rfl hK σ hσ Fr hFr).range := by
    rw [rgrpConjAut_range (n := 1) le_rfl hK σ hσ Fr hFr]
    exact hSlang.trans (TwE6DD2.langCube_le_range (n := 1) le_rfl hK σ hσ Fr hFr g)
  have hcard := card_automizer_twisted_frame_eq hK σ hσ Fr hFr ι hιval
    ((J.subgroupOf L).map (ggQuotHom θ)) (ggBeta L θ hN).range hA
  rw [hi, hY, map_langCube_inner_preimage_eq hK σ hσ Fr hFr T hq hρ hg hgn ι hιval hrange] at hcard
  have hfour : 4 ∣ Nat.card (ggAutomizer
      (((J.subgroupOf L).map (ggQuotHom θ)).map
        (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _)) (ggBeta L θ hN).range) := by
    rw [hY, hcard]
    exact QTwoCav.four_dvd_aut_innerFullThreeTorus_of_quasisimple_component
      T hq hAlg hρ hTb hb hb1 i hQ
  rw [QTwoCav.card_automizer_quotient_image_eq θ hS.2.1.1 hN,
    QTwoCav.card_automizer_inner_image_eq_of_setting hS
      (by rw [hp3]; exact Nat.prime_three) (by omega) hN] at hfour
  exact hfour

end CFSG.StandardType.QTwoE6

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGQ2CavOfTBFullImage : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ∀ lab : LargeEvenLabel,
      GGLabQTwo p lab → LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab) →
      ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ GGQ2LieRank lab →
      (lab.tag = .D ∨ lab.tag = .twD) → 4 ≤ lab.rank →
      ¬ CFSG.AGLEmbedding.IsAltTwoP 3 J →
      ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
        4 ∣ Nat.card (ggAutomizer
          ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
          (ggGamma L hN).range)

theorem ggQ2_cavOfTBFullImage_holds : GGQ2CavOfTBFullImage := by
  intro G _ _ p B Bs x L D J hS hp3 lab hq2 hM hidx htag hr _ hN
  subst p
  have hidx' : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank := by
    rcases htag with ht | ht <;> simpa only [GGQ2LieRank, ht] using hidx
  exact QTwoOrthogonalCav.four_dvd_image_of_full_orthogonal hS hq2 htag hr
    (QTwoCav.innerDiagOnLabel_of_setting hS hM) hidx' hN

theorem ggQ2_cavOfTBFull_of_image (h : GGQ2CavOfTBFullImage) : GGQ2CavOfTBFull := by
  intro G _ _ p B Bs x L D J hS hp3 hTB
  subst p
  obtain ⟨_, lab₀, _, hraw⟩ := hS.2.1
  obtain ⟨_, _, _, _, _, _, _, _, hN, _⟩ := largeEvenRawDatum_exists hraw
  by_cases hJ : CFSG.AGLEmbedding.IsAltTwoP 3 J
  · rw [QTwoB2Cav.card_automizer_original_of_setting hS rfl hN hJ]
  · obtain ⟨lab, hq2, hM, hidx⟩ := hTB
    have hmark := QTwoCav.innerDiagOnLabel_of_setting hS hM
    have hR : 3 ≤ GGQ2LieRank lab := QTwoCav.three_le_exponent_of_beta_index
      hS Nat.prime_three (MulEquiv.refl (L ⧸ Subgroup.center L)) hN hidx
    by_cases htw : lab.tag = .twE6
    · exact QTwoE6.four_dvd_original_automizer_of_full_label hS rfl hq2 htw hmark
        (by simpa only [GGQ2LieRank, htw] using hidx)
    · rw [← QTwoCav.card_automizer_inner_image_eq_of_setting hS Nat.prime_three (by omega) hN]
      cases ht : lab.tag with
      | A =>
          exact False.elim (QTwoCav.not_full_linear_of_marking hS hq2 (Or.inl ht) hmark
            (by simpa only [GGQ2LieRank, ht] using hidx) hN)
      | twA =>
          exact QTwoUnitaryCav.four_dvd_image_of_full_unitary hS hq2 ht hmark
            (by simpa only [GGQ2LieRank, ht] using hidx) hN
      | B =>
          exact QTwoSymplecticCav.four_dvd_image_of_full_symplectic hS hq2 (Or.inl ht) hmark
            (by simpa only [GGQ2LieRank, ht] using hidx) hN
      | C =>
          exact QTwoSymplecticCav.four_dvd_image_of_full_symplectic hS hq2 (Or.inr ht) hmark
            (by simpa only [GGQ2LieRank, ht] using hidx) hN
      | D =>
          by_cases hr3 : lab.rank = 3
          · exact False.elim (QTwoCav.not_full_linear_of_marking hS hq2 (Or.inr ⟨ht, hr3⟩)
              hmark (by simpa only [GGQ2LieRank, ht] using hidx) hN)
          · exact h hS rfl lab hq2 hM hidx (Or.inl ht)
              (by simp only [GGQ2LieRank, ht] at hR; omega) hJ hN
      | twD =>
          by_cases hr3 : lab.rank = 3
          · exact QTwoCav.four_dvd_image_of_full_twistedD_three hS hq2 ht hr3 hmark
              (by simpa only [GGQ2LieRank, ht] using hidx) hN
          · exact h hS rfl lab hq2 hM hidx (Or.inr ht)
              (by simp only [GGQ2LieRank, ht] at hR; omega) hJ hN
      | G2 => simp only [GGQ2LieRank, ht] at hR; omega
      | G2der => simp only [GGQ2LieRank, ht] at hR; omega
      | B2der => simp only [GGQ2LieRank, ht] at hR; omega
      | twB2 => simp only [GGQ2LieRank, ht] at hR; omega
      | F4 => exact QTwoCav.four_dvd_image_of_F4 hS hq2 ht hmark hidx hN
      | E6 => exact False.elim (QTwoCav.not_full_E6_of_marking hS hq2 ht hmark hidx)
      | E7 => exact QTwoCav.four_dvd_image_of_E7E8 hS hq2 (Or.inl ht) hmark hidx hN
      | E8 => exact QTwoCav.four_dvd_image_of_E7E8 hS hq2 (Or.inr ht) hmark hidx hN
      | twE6 => exact (htw ht).elim
      | triD4 =>
          exact False.elim (QTwoCav.not_full_triality_of_marking hS ht hmark
            (by simpa only [GGQ2LieRank, ht] using hidx) hN)
      | twF4der =>
          exact False.elim (QTwoCav.not_full_tits_of_marking hS ht hmark
            (by simpa only [GGQ2LieRank, ht] using hidx) hN)
      | twF4 =>
          obtain ⟨_, lab', hv, hr⟩ := hmark
          obtain ⟨_, _, _, _, _, _, _, hP⟩ := largeEvenRawDatum_exists hr
          have heq : lab' = lab := hP.1
          subst lab'
          simp only [LargeEvenInLambda2, ht] at hv
          change lab.n < 2 at hq2
          omega

theorem ggQ2_cavOfTBFull_holds : GGQ2CavOfTBFull :=
  ggQ2_cavOfTBFull_of_image ggQ2_cavOfTBFullImage_holds

end CFSG.StandardType

end
