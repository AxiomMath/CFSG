module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagDefs
import CFSG.LocalAnalysis.StandardType.GGPresentationInputs
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank

section Tag

variable {G : Type} [Group G] [Finite G]

theorem ggTagFacts_PSL {n f : ℕ} (hadm : StatedLieAdmissible .PSL n 2 f)
    (hrank : 3 ≤ bnRank .PSL n) : GGTagFacts .PSL n f := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [bnRank] at hrank; omega⟩
  have hm2 : 2 ≤ m := by simp only [bnRank] at hrank; omega
  have hm0 : 0 < m := by simp only [bnRank] at hrank; omega
  obtain ⟨ν, hν⟩ := ggStandardCopy_PSL (m + 1) f hadm hrank
  refine ⟨?_, ggUniversalFacts_of_lift (D := SpecialLinear.rootDatum m (GaloisField 2 f))
    (n := SpecialLinear.weylRep m (GaloisField 2 f))
    (H := SpecialLinear.torus m (GaloisField 2 f)) ?_ ?_ ?_ ⟨ν, hν.1⟩⟩
  · exact (show 2 ≤ (ggU .PSL (m + 1) f).D.rank from hm2)
  · exact (show 0 < (SpecialLinear.rootDatum m (GaloisField 2 f)).rank from hm0)
  · exact SpecialLinear.isCTGroupDatum m (GaloisField 2 f)
  · exact SpecialLinear.steinbergExtras m (GaloisField 2 f)

theorem ggSecFivePres_of_psi_PSL {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hadm : StatedLieAdmissible .PSL n 2 f) (hrank : 3 ≤ bnRank .PSL n)
    (ψ : (ggU .PSL n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .PSL n f).K)
    (hrange : ψ.range = ggG0 p B x L D J) : GGSecFivePres p B x L D J .PSL n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_PSL hadm hrank) ψ hker hrange

theorem ggTagFacts_PSp {n f : ℕ} (hadm : StatedLieAdmissible .PSp n 2 f)
    (hrank : 3 ≤ bnRank .PSp n) : GGTagFacts .PSp n f := by
  have hn2 : 2 ≤ n := by simp only [bnRank] at hrank; omega
  have hn0 : 0 < n := by simp only [bnRank] at hrank; omega
  obtain ⟨ν, hν⟩ := ggStandardCopy_PSp n f hadm
  refine ⟨?_, ggUniversalFacts_of_lift (D := Symplectic.rootDatum n (GaloisField 2 f))
    (n := Symplectic.weylRep n (GaloisField 2 f))
    (H := Symplectic.torus n (GaloisField 2 f)) ?_ ?_ ?_ ⟨ν, hν.1⟩⟩
  · exact (show 2 ≤ (ggU .PSp n f).D.rank from hn2)
  · exact (show 0 < (Symplectic.rootDatum n (GaloisField 2 f)).rank from hn0)
  · exact Symplectic.isCTGroupDatum n (GaloisField 2 f)
  · exact Symplectic.steinbergExtras n (GaloisField 2 f)

theorem ggSecFivePres_of_psi_PSp {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hadm : StatedLieAdmissible .PSp n 2 f) (hrank : 3 ≤ bnRank .PSp n)
    (ψ : (ggU .PSp n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (hrange : ψ.range = ggG0 p B x L D J) : GGSecFivePres p B x L D J .PSp n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_PSp hadm hrank) ψ hker hrange

end Tag

end CFSG.StandardType

end
