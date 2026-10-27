module

public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestVac
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem ggTBRowV_two_dvd_natCard_of_isSimpleGroup {R : Type} [Group R]
    (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a) : 2 ∣ Nat.card R := by
  rcases finite_or_infinite R with hR | hR
  · obtain ⟨a, b, hab⟩ := hna
    by_contra h2
    have hodd : Odd (Nat.card R) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) a b)
  · rw [Nat.card_eq_zero_of_infinite]
    exact dvd_zero 2

theorem ggTBRowV_false
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR5V p lab) p Bs L) :
    False := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  let guard : LargeEvenRawCont := fun R _ I _ =>
    ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3
  have hInner : ∀ lab : LargeEvenLabel, (GGLabQFour p lab ∧ GGTBRowR5V p lab) →
      GGNbrInnerSmallLabel p lab := by
    rintro ⟨t, l, n⟩ ⟨-, hTwD, hRank, hDvd⟩
    dsimp only at hTwD hRank hDvd
    subst hTwD
    subst hRank
    exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hDvd⟩)))),
      Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hDvd⟩))⟩))
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (P' := guard) (S := fun lab => GGLabQFour p lab ∧ GGTBRowR5V p lab)
    (fun lab hlab hS => largeEvenLabelAll_card_lt_innerSmall hp hp2 hlab (hInner lab hS))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, hs, hna, θ, ⟨-, hBsN, h3I⟩, hBound⟩ := largeEvenRawDatum_exists hraw
  have hLift : GGTorusLift p 0 R :=
    TypeA.ggTorusLift_zero (ggTBRowV_two_dvd_natCard_of_isSimpleGroup hs hna)
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hLift
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3', -⟩ :=
    ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hXA : IsElemAbelian p (TypeA.inducedSub (ggQuotHom θ) (ggGamma L hBsN).range) :=
    TypeA.isElemAbelian_inducedSub hψ hAe
  have hXI : ((TypeA.inducedSub (ggQuotHom θ) (ggGamma L hBsN).range : Subgroup (MulAut R)) :
      Set (MulAut R)) ⊆ I := by
    rintro y ⟨a, ha, hya⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact TypeA.induced_unique (ggQuotHom θ) hψ hφa hya ▸ hφaI
  have hcardX : Nat.card (TypeA.inducedSub (ggQuotHom θ) (ggGamma L hBsN).range) =
      Nat.card (ggGamma L hBsN).range :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  have hlt := hBound _ hXI hXA
  rw [hcardX] at hlt
  omega

theorem ggExcReflTBWeylDatumQFourOn_rowR5V
    : GGExcReflTBWeylDatumQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5V p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  exact (ggTBRowV_false hHyp hL).elim

theorem ggTBJNoncommReflOn_rowR5V
    : GGTBJNoncommReflOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5V p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  exact (ggTBRowV_false hHyp hL).elim

end CFSG.StandardType

end
