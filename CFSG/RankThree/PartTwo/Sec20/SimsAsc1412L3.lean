module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Statements
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Star
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3NoSmall
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3OuterInput
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

theorem asc82Item1412L3_of_inputs (hgen : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G)
    [L.Normal], centralizer (L : Set G) = ⊥ → ∀ (p : ℕ) [Fact p.Prime], IsL3eps1412 ↥L p → ∀ b : G,
    b ∉ L → orderOf b = 2 → ∀ y ∈ L, orderOf y = 3 → L ≤ normalizer (zpowers y : Set G) ⊔
    omegaOut1412 L b)
    (h5 : haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩; ExclL3Model1412 5)
    (h17 : haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩; ExclL3Model1412 17)
    (h7 : ExclU3Model1412 7) (h31 : ExclU3Model1412 31) (h127 : ExclU3Model1412 127) :
    Asc82Item1412L3 := by
  intro X _ _ L S x h hK hL3 hxL hx3
  obtain ⟨p, hp, hp3, hcase⟩ := hL3
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have hLeps : IsL3eps1412 ↥(L.map π) p := ⟨hp3, hcase⟩
  have hZ := center_eq_bot_of_isL3eps1412 hLeps
  have hrank := twoRank_le_two_of_isL3eps1412 hLeps
  have hidx := index_map_le_two_of_isL3eps1412 h hLeps
  have hidx8 := relIndex_pCore_le_eight_of_isL3eps1412 h hLeps
  have hNS := noSmall1412_of_isL3eps1412 h hK hLeps h5 h17 h7 h31 h127
  have hLn : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  have hC := centralizer_map_eq_bot_of_hyp1411 h hZ
  have htop : ∀ i : Fin 4, (Sec18.fourChar S i).Normal →
      normalizer (zpowers x : Set X) ⊔ normalizer (Sec18.fourChar S i : Set X) = ⊤ := by
    intro i hi
    rw [normalizer_eq_top_iff.mpr hi, sup_top_eq]
  rcases two_fourChar_normal_or_star1412_of_hyp1411 h hidx8 hNS with
    ⟨i₁, i₂, hne, hn1, hn2⟩ | hstar
  · exact ⟨i₁, i₂, hne, htop i₁ hn1, htop i₂ hn2⟩
  · refine ⟨0, 3, by decide, htop 0 ?_, ?_⟩
    · rw [Sec18.Item181ThreeProof.fourChar_zero]
      exact hstar.1
    · exact sup_normalizer_fourChar_three_eq_top_of_star1412 hK h hstar hrank hidx
        (fun b hbL hb2 => outerInput1412_of_isL3eps1412 hC hLeps hbL hb2
          (hgen _ (L.map π) hC p hLeps b hbL hb2)) hxL hx3

end CFSG.RankThree.PartTwo.Sec20
