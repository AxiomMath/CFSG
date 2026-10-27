module

public import CFSG.LocalAnalysis.Gross82.OrderThreeHolds

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91G211Layer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91G211Gross
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91G211Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91G211Local
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.ThreePart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22


theorem r891g211_gross_c {J0 : Type} [Group J0]
    [Finite J0] (hK : CFSG.Open.IsKGroup J0) (hO : CFSG.pPrimeCore 3 J0 = ⊥) {P : Subgroup J0}
    (hP : IsSylowOf 3 P ⊤) :
    ∀ c ∈ P, c ^ 3 = 1 → (∀ u ∈ P ⊓ CFSG.generalizedFitting J0, c * u = u * c) →
      c ∈ CFSG.generalizedFitting J0 := by
  have h3 : ∀ J : Subgroup J0, IsComponentOf J ⊤ → 3 ∣ Nat.card (↥J ⧸ center ↥J) :=
    fun J hJ =>
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.three_dvd_card_component_quotient
        (show CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := J0) 3 = ⊥ from hO)
        hJ
  exact r891g211_gross_c_of_components hP hO h3 fun J hJ c hcN hc3 hcP =>
    r891g211_gross_component Gross82.r891GrossCoreOrderThree_holds hK hP hJ (h3 J hJ) hcN hc3 hcP

theorem r891g211_component_lemma {J0 : Type}
    [Group J0] [Finite J0]
    (hK : CFSG.Open.IsKGroup J0) (hO : CFSG.pPrimeCore 3 J0 = ⊥)
    {P M0 X0 E T : Subgroup J0} (hP : IsSylowOf 3 P ⊤) (hPM : P ≤ M0) (hXM : X0 ≤ M0)
    (hXn : (X0.subgroupOf M0).Normal) (hXs : IsSolvable ↥X0) (hE : E = P ⊓ X0) (hE1 : E ≠ ⊥)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hEF : E ⊓ CFSG.pCore 3 J0 = ⊥) (hTX : T ≤ X0)
    (hTN : T ≤ normalizer (E : Set J0))
    (hIrr : ∀ W : Subgroup J0, W ≤ E → T ≤ normalizer (W : Set J0) → W = ⊥ ∨ W = E)
    (hInv : ∃ t ∈ ⁅T, T⁆, ∀ e ∈ E, t * e * t⁻¹ = e⁻¹)
    (hC : ∀ a ∈ E, a ≠ 1 → centralizer ({a} : Set J0) ≤ M0) :
    ∃ J : Subgroup J0, IsComponentOf J ⊤ ∧ E ≤ J ∧ ¬ J ≤ M0 ∧
      ¬ E ≤ centralizer (J : Set J0) := by
  have hXF := centralizes_pCore_of_inf_eq_bot hP hPM hXM hXn hE hEF
  have hEX : E ≤ X0 := hE ▸ inf_le_right
  have hEP : E ≤ P := hE ▸ inf_le_left
  have hGC := r891g211_gross_c hK hO hP
  have hEK := le_layer_of_irreducible_inverted hPM hXM hXn hE hE3 hO hTX hTN hIrr hInv hXF hGC
  have hAlt : ∀ J : Subgroup J0, IsComponentOf J ⊤ →
      E ≤ centralizer (J : Set J0) ∨ E ⊓ centralizer (J : Set J0) = ⊥ :=
    fun J hJ => component_alt_of_solvable_normal hXM hXn hXs hEX hC hJ
  have hdec : ∀ J : Subgroup J0, IsComponentOf J ⊤ → ∀ e ∈ E,
      ∃ q ∈ P ⊓ J, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (J : Set J0)), e = q * r :=
    fun J hJ e he => layer_decomp_of_isSylow hP hJ ⟨hEP he, hEK he⟩
  obtain ⟨J, hJ, hact, huniq⟩ :=
    unique_active_component hP hPM hXM hXn hE hE1 hO hEF hEK hTX hTN hInv hAlt hdec
  obtain ⟨hEJ, hJM⟩ :=
    le_component_of_unique_active hXM hXn hXs hEX hE3 hO hTX hTN hInv hXF hJ hact huniq
      (hdec J hJ)
  exact ⟨J, hJ, hEJ, hJM, hact⟩

theorem r891Gap211_holds {G : Type} [Group G] [Finite G] (D : Data G) :
    ∀ L S R A : Subgroup G, R891State D L S R A 1 → R891Gamma895 D L S R → R891Norm895 D L S 1 →
      R891Comp895 D L S 1 R := by
  intro L S R A hst hgam hnorm
  obtain ⟨hRH, hXH, hZ3, hR3, hZR⟩ := r891g211_basic D hst
  have huniq := r891g211_uniq D hst
  obtain ⟨P0, hP0, hRP0, hP0M⟩ := r891g211_sylow_le_M D hst huniq
  have hRX : R ≤ R891X L (R891Z L S) 1 := hst.ctx.xShape.rLe
  have hRextra := hst.ctx.xShape.rExtra
  have hzLe : R891Z L S ≤ R := hst.ctx.xShape.zLe
  have hSU : R891SU32 (Bar2 (R891X L (R891Z L S) 1)) := by
    rcases hst.ctx.xShape.xShape with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  obtain ⟨hRsyl, hXsol, T0, ψ, hT0X, hT0N, hψ, hker⟩ :=
    r891g211_su32_action hRX hRextra hSU fun K _ _ hK α hα =>
      aut_pow_three_eq_one_of_trivial_mod_center hK α hα
  obtain ⟨hirr, hinv⟩ := q8_extraspecial_irreducible_inverting hRextra hT0N ψ hψ hker
  obtain ⟨hPsyl, hPM0, hEeq, hX0s⟩ :=
    r891g211_star_sylow (Z := R891Z L S) (M := D.M) hXsol hRsyl hP0 hRP0 hP0M
  have hRK := r891g211_inf_ker (H := R891H L S) (Z := R891Z L S) le_rfl hR3 hzLe
  obtain ⟨hE1, -, hE3⟩ := r891g211_star_e hZR hRH hRextra hRK
  have hO := r891g211_pPrimeCore_star le_rfl hZ3
  have hEF := r891g211_e_inf_f D hst hgam huniq hP0 hRP0 hP0M
  have hK := r891g211_kgroup_star D hst.basic
  obtain ⟨hTX, hTN, hIrr, hInv⟩ :=
    r891g211_star_shape hZR hRH hT0X hXH hT0N hirr hinv
  have hC : ∀ a ∈ R891Img (R891H L S) (R891Z L S) R, a ≠ 1 →
      centralizer ({a} : Set (R891Star (R891H L S) (R891Z L S))) ≤
        R891Img (R891H L S) (R891Z L S) D.M :=
    fun a ha ha1 =>
      (centralizer_le_rankThreeGamma_of_pow_three ha ha1 (hE3 a ha)).trans hgam.1
  obtain ⟨J, hJ, hEJ, hJM, hnc⟩ :=
    r891g211_component_lemma hK hO hPsyl hPM0 hnorm.1 hnorm.2 hX0s hEeq hE1 hE3 hEF
      hTX hTN hIrr hInv hC
  obtain ⟨hRY, hZY, hYM⟩ :=
    r891g211_lift (M := D.M) hRextra hZR hRH le_rfl hJ hEJ hJM
  refine ⟨J, hJ, fun h => absurd h (by norm_num), hRY, hYM, hZY, fun _ hcomm => ?_⟩
  exact hnc (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
