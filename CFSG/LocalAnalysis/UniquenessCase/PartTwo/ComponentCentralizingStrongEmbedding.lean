module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ImageOTwoQuotNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251j
public import CFSG.Quasithin.Background.C1PackImage
public import CFSG.GroupTheory.PCoreOfSubnormal
public import CFSG.GroupTheory.CoprimeSupPCore
public import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isStronglyPEmbedded_of_component_action_centralization
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) (h127 : R127 D) (h119 : F11.R119 D)
    (h869 : F08.R869 D)
    {B : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : IsComponentOf B (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥B)
    (hrank : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥B))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : p ∣ Nat.card D.M)
    (hcent : ∀ P : Subgroup G, IsPGroup p P → P ≤ D.M →
      barSub V₀ V hV P ≤
        Subgroup.centralizer (B : Set (MulAut (Vtil V₀ V hV)))) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M := by
  classical
  have hpFact : Fact p.Prime := ⟨hp⟩
  have hsimpleG : IsSimpleGroup G := D.standing.simple
  have hms : D.M ≤ stabTil V₀ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  obtain ⟨Y, hYcalC, hYbar, -⟩ :=
    exists_calC_cover_of_simple_component h125 h127 h119 hcomp hsimple
  have hYM : Y ≤ D.M := CFSG.Quasithin.A3.subnormal_le hYcalC.1
  have hYs : Y ≤ stabTil V₀ V := hYM.trans hms
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 h125
  let φ : ↥Y →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hYs
  have hφB : ∀ y : ↥Y, φ y ∈ B := by
    intro y
    rw [← hYbar]
    exact actTil_mem_barSub V₀ V hV y.2 (hYs y.2)
  let f : ↥Y →* ↥B := φ.codRestrict B hφB
  have hf : Function.Surjective f := by
    intro b
    have hb : (b : MulAut (Vtil V₀ V hV)) ∈ barSub V₀ V hV Y := by
      rw [hYbar]
      exact b.2
    obtain ⟨g, hgY, hgφ⟩ :=
      (mem_barSub V₀ V hV Y (b : MulAut (Vtil V₀ V hV))).1 hb
    refine ⟨⟨(g : G), hgY⟩, ?_⟩
    apply Subtype.ext
    change (actTil V₀ V hV) (⟨(g : G), hYs hgY⟩ : ↥(stabTil V₀ V)) =
      (b : MulAut (Vtil V₀ V hV))
    have hgg : (⟨(g : G), hYs hgY⟩ : ↥(stabTil V₀ V)) = g := rfl
    rw [hgg]
    exact hgφ
  have hYnotThin : ¬ F08.Thin8 Y := by
    intro hthin
    obtain ⟨q, hq, hq2, hqrank⟩ := hrank
    have hqY : 2 ≤ CFSG.Open.pRank q Y :=
      uc22p2214_two_le_pRank_of_surj (K := Y) (Y := ↥B) f hf hq hq2 hqrank
    have hle := hthin q hq hq2
    omega
  have hnormalizer_le : ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup p P → P ≤ D.M →
      normalizer (P : Set G) ≤ D.M := by
    intro P hPne hPp hPM
    set X : Subgroup G := Y ⊓ Subgroup.centralizer (P : Set G) with hX
    have hbarP : UC22.barImage D.M P ≤
        Subgroup.centralizer (UC22.barImage D.M Y : Set (Bar2 D.M)) := by
      intro x hx
      obtain ⟨m, hmP, rfl⟩ := hx
      exact mem_centralizer_barImage_of_map_mem_centralizer h125 hYcalC hYbar hsimple ψ hψ (by
        change ψ (QuotientGroup.mk m) ∈
          Subgroup.centralizer (B : Set (MulAut (Vtil V₀ V hV)))
        rw [hψ m]
        exact hcent P hPp hPM
          (actTil_mem_barSub V₀ V hV (Subgroup.mem_subgroupOf.mp hmP) (hms m.2)))
    have hPN : P ≤ Subgroup.normalizer (Y : Set G) := by
      intro t htP
      have htM : t ∈ D.M := hPM htP
      have htbarC : (QuotientGroup.mk ⟨t, htM⟩ : Bar2 D.M) ∈
          Subgroup.centralizer (UC22.barImage D.M Y : Set (Bar2 D.M)) :=
        hbarP (Subgroup.mem_map.mpr ⟨⟨t, htM⟩, htP, rfl⟩)
      have htbar : (QuotientGroup.mk ⟨t, htM⟩ : S17.Mbar9 D) ∈
          Subgroup.normalizer (S17.K1Nine D Y : Set (S17.Mbar9 D)) := by
        refine Subgroup.centralizer_le_normalizer (S17.K1Nine D Y : Set (S17.Mbar9 D)) ?_
        simpa [S17.K1Nine, CFSG.Quasithin.imageOTwoQuot, UC22.barImage] using htbarC
      exact S17.mem_normalizer_of_mem_normalizer_imageOTwoQuot hYcalC htM (by
        simpa [S17.K1Nine, CFSG.Quasithin.imageOTwoQuot, UC22.barImage] using htbar)
    have hcommMem : ∀ x ∈ P, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 Y := by
      intro x hx y hy
      have hxcy : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 D.M := by
        have hbar : ⁅CFSG.Quasithin.C1Pack.barImage D.M P,
            CFSG.Quasithin.C1Pack.barImage D.M Y⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          simpa [CFSG.Quasithin.C1Pack.barImage, CFSG.Quasithin.imageOTwoQuot,
            UC22.barImage] using hbarP
        exact CFSG.Quasithin.C1Pack.commutator_mem_pCoreOf_of_barImage hPM hYM hbar x hx y hy
      have hYmem : x * y * x⁻¹ * y⁻¹ ∈ Y := by
        have hxy : x * y * x⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hPN hx) y).mp hy
        exact Y.mul_mem hxy (Y.inv_mem hy)
      rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hYcalC.1]
      exact ⟨hYmem, hxcy⟩
    have hcomm : ⁅P, Y⁆ ≤ pCoreOf 2 Y :=
      Subgroup.commutator_le.mpr fun x hx y hy => by
        simpa [commutatorElement_def] using hcommMem x hx y hy
    have hsup : X ⊔ pCoreOf 2 Y = Y :=
      CFSG.GroupTheory.inf_centralizer_sup_pCoreOf_eq_of_commutator_le hp hp2 hPp hcomm
    have hN : calNOf X = {D.M} :=
      h869 Y (Or.inl hYcalC) X inf_le_left hsup hYnotThin
    have hXle : X ≤ Subgroup.normalizer (P : Set G) :=
      inf_le_right.trans (Subgroup.centralizer_le_normalizer (P : Set G))
    have hNproper : Subgroup.normalizer (P : Set G) ≠ ⊤ :=
      CFSG.RankThree.PartTwo.Sec14.normalizer_ne_top_of_isPGroup D.standing.simple
        D.standing.nonab hPne hPp
    exact UC22.P2251j.le_of_calNOf hN hXle hNproper
  have hM : D.M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top
      D.standing.nonab D.M D.maxLocal.1
  exact CFSG.LocalAnalysis.RankThreeUC.isStronglyPEmbedded_of_normalizer_le hM hpM
    hnormalizer_le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
