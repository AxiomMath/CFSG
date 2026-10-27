module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.OddCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.UnitaryRow
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.RankThreeUC.TheoremDReductions
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F07

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC (le_sup_inf_normalizer_of_isSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem r71_odd_le_of_r6_3 (D : Data G) (h63 : UC6.R6_3 D) {p : ℕ} {H : Subgroup G}
    (h : Sec7Hyp D p H) :
    Odd (Nat.card (PPrimeCoreIn p H)) ∧ PPrimeCoreIn p H ≤ D.M := by
  obtain ⟨hp, hp2, hM, -, hHM, hrank⟩ := h
  refine ⟨?_, PartOne.Section7.pPrimeCore_le hM hp hrank⟩
  rw [PPrimeCoreIn, Subgroup.card_map_of_injective H.subtype_injective]
  exact PartOne.Section7.odd_card_pPrimeCore hM hp (fun _ hT hT2 hTr =>
    PartOne.Section7.normalizer_le_of_r6_3 D h63 hp hp2 hM hT hT2 hTr) hHM hrank

theorem pRank_pPrimeCoreIn_le_three {M H : Subgroup G} {p q : ℕ} (hHM : ¬ H ≤ M)
    (hKM : PPrimeCoreIn p H ≤ M) (hq : q.Prime)
    (hN : ∀ X : Subgroup G, X ≤ M → IsPGroup q X → 4 ≤ Open.pRank q X →
      normalizer (X : Set G) ≤ M) :
    Open.pRank q (PPrimeCoreIn p H) ≤ 3 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hlt
  have h4K : 4 ≤ Open.pRank q (PPrimeCoreIn p H) := by omega
  obtain ⟨E, hEK, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (PPrimeCoreIn p H)
  obtain ⟨S, hS, hES⟩ := UC6.exists_isSylowOf_ge hEK hEel.isPGroup
  have h4S : 4 ≤ Open.pRank q S :=
    h4K.trans (CFSG.SectionRank.le_pRank hq.one_lt hES hEel hEcard)
  have hNS : normalizer (S : Set G) ≤ M := hN S (hS.le.trans hKM) hS.isPGroup h4S
  have hfr : H ≤ PPrimeCoreIn p H ⊔ (H ⊓ normalizer (S : Set G)) :=
    le_sup_inf_normalizer_of_isSylowOf (Subgroup.map_subtype_le _)
      (CFSG.ABGLocalTools.le_normalizer_map_subtype H (CFSG.pPrimeCore p ↥H)) hS
  exact hHM (hfr.trans (sup_le hKM (inf_le_right.trans hNS)))

theorem r71_of_r6_3 (D : Data G) (h63 : UC6.R6_3 D)
    (hN : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ X : Subgroup G, X ≤ D.M → IsPGroup q X →
      4 ≤ Open.pRank q X → normalizer (X : Set G) ≤ D.M) :
    R71 D := by
  intro p H h
  obtain ⟨hodd, hKM⟩ := r71_odd_le_of_r6_3 D h63 h
  exact ⟨hodd, hKM, fun q hq hqdvd =>
    pRank_pPrimeCoreIn_le_three h.2.2.2.2.1 hKM hq (hN q hq (hodd.ne_two_of_dvd_nat hqdvd))⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F07
