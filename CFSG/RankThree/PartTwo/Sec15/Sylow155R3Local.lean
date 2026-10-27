module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3CtxDefs
public import CFSG.RankThree.PartOne.N143.T2LargeAll
import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
import CFSG.LocalAnalysis.ComponentInitial.ComponentCentralLift
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)

section PPrimeCoreQuotient

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem sectionFourHyp_of_isQuasisimple_pPrimeCoreQuot
    (h41 : CFSG.RankThree.PartTwo.Sec4.Item4_1LargePrime) (hΓ : SectionFourHyp Γ)
    (X : Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ)) (hX : CFSG.IsQuasisimple ↥X) :
    SectionFourHyp ↥X := by
  let e := CFSG.LocalAnalysis.ComponentInitial.comapMkQuotientEquiv (CFSG.pPrimeCore 3 Γ) X
  have hN : ¬ 3 ∣ Nat.card ((CFSG.pPrimeCore 3 Γ).subgroupOf
      (X.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)))) := fun h3 =>
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card)
      (h3.trans (CFSG.RankThree.PartTwo.Sec4.Item41Narrow.card_subgroupOf_dvd _ _))
  exact CFSG.RankThree.PartTwo.Sec4.Census.sectionFourHyp_of_mulEquiv e
    (CFSG.RankThree.PartTwo.Sec4.Item41Narrow.sectionFourHyp_section h41 hΓ _ _ hN
      (hX.of_mulEquiv e))

theorem localRank_lt_of_layer_eq_top_pPrimeCoreQuot
    (h41 : CFSG.RankThree.PartTwo.Sec4.Item4_1LargeAll) (hΓ : SectionFourHyp Γ)
    (X : Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ)) (hX : CFSG.layer ↥X = ⊤) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : localRank p ↥X < 3 := by
  let e := CFSG.LocalAnalysis.ComponentInitial.comapMkQuotientEquiv (CFSG.pPrimeCore 3 Γ) X
  have hlay : CFSG.layer (↥(X.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ))) ⧸
      (CFSG.pPrimeCore 3 Γ).subgroupOf (X.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)))) =
        ⊤ := by
    rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective
        (CFSG.layer _), CFSG.WholeGroup.layer_map_mulEquiv e, hX, Subgroup.comap_top]
  have h := h41 Γ hΓ (X.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)))
    ((CFSG.pPrimeCore 3 Γ).subgroupOf (X.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)))) hlay p
    hp hp3
  rwa [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp] at h

end PPrimeCoreQuotient

variable {G : Type} [Group G] [Finite G]

namespace Res3Ctx

variable {A : Subgroup G} {c : G} {L : Subgroup G} {d : G} {K : Subgroup G}

theorem res3C_ne_top (h : Res3Ctx A c L d K) : res3C d ≠ ⊤ := by
  intro htop
  have hG := h.R.toTheoremFourHyp
  have := hG.isSimpleGroup
  obtain ⟨x, y, hxy⟩ := hG.nonabelian
  have hz : d ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ res3C d := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
  · rw [h', Subgroup.mem_bot] at hz
    exact h.d_ne hz
  · exact hxy (Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top x) y).symm

theorem sectionFourHyp_C (h : Res3Ctx A c L d K) : SectionFourHyp ↥(res3C d) :=
  h.R.toTheoremFourHyp.sectionFourHyp h.res3C_ne_top

theorem sectionFourHyp_of_isQuasisimple (h : Res3Ctx A c L d K)
    (h41 : CFSG.RankThree.PartTwo.Sec4.Item4_1LargePrime) :
    ∀ X : Subgroup (Res3Bar d), CFSG.IsQuasisimple ↥X → SectionFourHyp ↥X :=
  fun X hX => sectionFourHyp_of_isQuasisimple_pPrimeCoreQuot h41 h.sectionFourHyp_C X hX

theorem localRank_lt (h : Res3Ctx A c L d K) (h41 : CFSG.RankThree.PartTwo.Sec4.Item4_1LargeAll) :
    ∀ X : Subgroup (Res3Bar d), CFSG.layer ↥X = ⊤ →
      ∀ p : ℕ, p.Prime → 3 < p → localRank p ↥X < 3 :=
  fun X hX p hp hp3 =>
    localRank_lt_of_layer_eq_top_pPrimeCoreQuot h41 h.sectionFourHyp_C X hX hp hp3

end Res3Ctx

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
