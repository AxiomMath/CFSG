module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2121_mem_uniqueSet_of_noncyclic {D : Data G} (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {X : Subgroup G} (hXM : X ≤ D.M) (hX : IsPGroup p X) (hnc : ¬ IsCyclic X) : X ∈ uniqueSet D.M := by
  have hUM : calMOf X = {D.M} := h61 p hp X hXM hX hnc
  refine mem_uniqueSet_of_forall D.maxLocal hXM fun H hH hXH => ?_
  have hmem : H ∈ calMOf X := ⟨hH, hXH⟩
  rw [hUM] at hmem
  exact Set.mem_singleton_iff.1 hmem

theorem uc22p2121_pRank_centE_le_one {D : Data G} {Ch : Choice2011 G} (h61 : UC6.R6_1 D) (c : Ctx21 D Ch)
    (hH : Hyp2120 D c) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p (barPreimage D.M (centE D.M)) ≤ 1 := by
  obtain ⟨-, -, h3, h4⟩ := hH
  obtain ⟨hpP, -⟩ := D.sig_prime p hp
  by_contra hlt
  obtain ⟨P, hPsyl, hPB⟩ := h3 p hp
  have hPM : P ≤ D.M := hPsyl.le.trans (Subgroup.map_subtype_le _)
  have hnc : ¬ IsCyclic P := fun hc => by
    have h1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hpP hc
    rw [PrimeRankSylowTransport.pRank_sylow hpP hPsyl] at h1
    exact hlt h1
  have hPU := uc22p2121_mem_uniqueSet_of_noncyclic h61 hp hPM hPsyl.isPGroup hnc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨t, _, _, _, ht⟩, _⟩ := c.hB
  exact h4 p hp (not_le.1 hlt) (uc22p21b_core (UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal) hpP
    hPsyl.isPGroup hPB ⟨hPU.1, fun g hg => hPU.2 g⁻¹ hg⟩ ht)

end CFSG.LocalAnalysis.UniquenessCase.UC22
