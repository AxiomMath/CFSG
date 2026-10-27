module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeNineCell
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavHeartReduction
import CFSG.LocalAnalysis.StandardType.GGQ2GammaOfShape
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
import CFSG.LocalAnalysis.StandardType.GGQ2CavNbrHeart
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeI1Rank
import CFSG.LocalAnalysis.StandardType.GGQTwoTBDerive
import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem ggQ2_labQTwo_of_marking_twA (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    {labL : LargeEvenLabel} (htag : labL.tag = .twA)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL)) : GGLabQTwo p labL := by
  obtain ⟨lab₁, hl₁, hn₁, hH₁⟩ := FrameRoute.ggFrameQTwo_exists_hasLabel (P := fun lab => lab.n < 2)
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hS.2.1)
  obtain ⟨lab₂, hl₂, rfl, hH₂⟩ := FrameRoute.ggFrameQTwo_exists_hasLabel hmark
  have h1 : 1 ≤ lab₁.n := hl₁.1
  rcases FrameRoute.ggFrameQTwo_qTwoCompat_of_iso (by omega) (hRig lab₁ lab₂ _ hl₁ hl₂ hH₁ hH₂)
    with hn | ⟨ht, -, -⟩
  · show lab₂.n < 2
    omega
  · rw [htag] at ht
    cases ht

theorem ggQ2s08_tn9L_of_nbrData (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput)
    (hK : GGReflClassOmegaInput) (hCavH : GGQ2CavOfTBHeartInner)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J)
    (hrow : GGQ2S08PosTwA 9 p L J) (hx : x ∉ L)
    (hD : Nat.card Bs = 3 ^ 8 → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ∃ M : GGQ2LDatum p Bs K y, M.Shape) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  subst hp
  have hrow' : GGQ2S08RowTwA 3 9 L J := hrow
  obtain ⟨M, e, hC, hBC⟩ := ggQ2TwAHeartDatumInput_holds hRig hLB hP rfl hS hI1
    (Or.inl ⟨rfl, rfl⟩) (by norm_num) hrow' hx
  have hΛ : Fintype.card M.Λ = 9 - 1 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hB : M.ShapeB := ggQ2_shapeB_twA_of_I1 hRig hLB hS.1.1 hS.1.2.2.1 hI1 (Or.inl rfl)
    (by norm_num) hrow' M hΛ hBC
  have hdim : finrank (ZMod 3) M.V = 8 := by
    rw [ggQ2LD_dim_heart M (Or.inl hB), hΛ]
  have hcard : Nat.card Bs = 3 ^ 8 := by
    rw [M.card_eq_pow_finrank, hdim]
  have hCav : 4 ∣ Nat.card (ggAutomizer J Bs) := by
    obtain ⟨labX, labJ, hmX, -, -, htX, hrk, -, -, -, hNJ⟩ := hrow'
    have hTBH : GGQ2TBHeart 3 Bs L := by
      refine ⟨labX, ggQ2_labQTwo_of_marking_twA hRig hS htX hmX, hmX,
        Or.inl ⟨htX, by rw [hrk]; omega⟩, ?_⟩
      rw [M.index_centralizer_of_setting hS, hdim]
      simp only [GGQ2LieRank, htX]
      congr 1
      omega
    exact ggQ2_cav_of_tbHeart hCavH hS rfl hTBH M (Or.inl hB)
  refine ggQ2_tn9_holds_of_gammaNbr hLB hP hNC h5 hK hS hI1 M e hC hB hCav ?_
  intro y K hnb u hu
  obtain ⟨N, hsh⟩ := hD hcard hnb
  have hdimN : finrank (ZMod 3) N.V = 8 := by
    have h := N.card_eq_pow_finrank
    rw [hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  exact ggQ2_gammaNbr_of_tableBShape hLB hP h5 hS hI1 hnb N hsh
    (N.inner_of_even (by rw [hdimN]; decide) (by omega))
    (N.heartA_of_dim (by omega) (by omega)) hu

theorem ggQ2s08_tn9K_of_data (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput)
    (hK : GGReflClassOmegaInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hrow : GGQ2S08PosTwA 9 p K J) (hy : y ∉ K)
    (hDL : Nat.card Bs = 3 ^ 8 → ∃ M : GGQ2LDatum p Bs L x, M.Shape)
    (hDN : Nat.card Bs = 3 ^ 8 → ∀ {y' : G} {K' : Subgroup G}, GGNbr p B x D J y' K' →
      ∃ M : GGQ2LDatum p Bs K' y', M.Shape) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  subst hp
  have hrow' : GGQ2S08RowTwA 3 9 K J := hrow
  obtain ⟨MK, eK, hCK, hBCK⟩ := ggQ2TwAHeartDatumInput_holds hRig hLB hP rfl hS hI1
    (Or.inr hnb) (by norm_num) hrow' hy
  have hΛ : Fintype.card MK.Λ = 9 - 1 := by
    rw [← Fintype.card_congr eK, Fintype.card_fin]
  have hBK : MK.ShapeB := ggQ2_shapeB_twA_of_I1 hRig hLB hS.1.1 hS.1.2.2.1 hI1
    (Or.inr ⟨y, hnb⟩) (by norm_num) hrow' MK hΛ hBCK
  have hdim : finrank (ZMod 3) MK.V = 8 := by
    rw [ggQ2LD_dim_heart MK (Or.inl hBK), hΛ]
  have hcard : Nat.card Bs = 3 ^ 8 := by
    rw [MK.card_eq_pow_finrank, hdim]
  have hdim8 : ∀ {X : Subgroup G} {u : G} (N : GGQ2LDatum 3 Bs X u), finrank (ZMod 3) N.V = 8 := by
    intro X u N
    have h := N.card_eq_pow_finrank
    rw [hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  have hCav : 4 ∣ Nat.card (ggAutomizer J Bs) :=
    ggQ2_cav_nbr_twA_of_heart hRig hLB hS.1.1 hS.1.2.2.1 hnb (by norm_num) hrow' MK (Or.inl hBK)
  obtain ⟨ML, hshL⟩ := hDL hcard
  have hΓx : GGQ2GammaX 3 B Bs x L D J :=
    ggQ2_gammaX_of_tableBShape hLB hP hS hCav ML hshL
      (ML.inner_of_even (by rw [hdim8 ML]; decide) (by rw [hdim8 ML]; norm_num))
      (ML.heartA_of_dim (by rw [hdim8 ML]; norm_num) (by rw [hdim8 ML]; norm_num))
  refine ggQ2_tn9K_holds_of_gamma hLB hP hNC h5 hK hS hI1 hnb MK eK hCK hBK hCav hΓx ?_
  intro y' K' hnb' u hu
  obtain ⟨N, hsh⟩ := hDN hcard hnb'
  exact ggQ2_gammaNbr_of_tableBShape hLB hP h5 hS hI1 hnb' N hsh
    (N.inner_of_even (by rw [hdim8 N]; decide) (by rw [hdim8 N]; norm_num))
    (N.heartA_of_dim (by rw [hdim8 N]; norm_num) (by rw [hdim8 N]; norm_num)) hu

end CFSG.StandardType

end
