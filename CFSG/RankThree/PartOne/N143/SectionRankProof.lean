module

public import CFSG.RankThree.PartOne.N143.SectionCover
public import CFSG.RankThree.PartOne.S11.SecTenEight
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank Subgroup
open CFSG.RankThree.PartOne (Sec6EightMultipliers TauCetiCatalogBridge)

theorem central_cover_quasisimple {Y S : Type} [Group Y] [Group S] [Finite S] [IsSimpleGroup S]
    (hperf : Group.IsPerfect Y) (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : Y →* S)
    (hφ : Function.Surjective φ) (hcent : φ.ker ≤ center Y) :
    center Y = φ.ker ∧ CFSG.IsQuasisimple Y ∧ Nonempty ((Y ⧸ center Y) ≃* S) := by
  have hcenter : center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  have hker : center Y = φ.ker := by
    refine le_antisymm (fun z hz => ?_) hcent
    have hz' : φ z ∈ center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hφ g
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subgroup.mem_center_iff.1 hz y)
    rw [hcenter, Subgroup.mem_bot] at hz'
    exact MonoidHom.mem_ker.2 hz'
  have hcongr : (Y ⧸ center Y) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  refine ⟨hker, ⟨hperf, hcongr.isSimpleGroup, ?_⟩, ⟨hcongr⟩⟩
  obtain ⟨a, b, hab⟩ := hnonab
  exact ⟨hcongr.symm a, hcongr.symm b, fun h => hab (by
    have := congrArg hcongr h
    simpa using this)⟩

end CFSG.RankThree.PartOne.N143
