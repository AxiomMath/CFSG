module

public import CFSG.RankThree.PartOne.SRC.Centralizer
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime
import CFSG.LieType.Chevalley.OddRootPairSL2
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LieType.Chevalley.RootDiagonalTorusWords
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.SRC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo.Census.Carrier TauCeti
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


theorem rankFourCover_adjointG2 {p e : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = p ^ e) (hp2 : p ≠ 2) (he : 4 ≤ e) :
    RankFourCover p (adjointGroup Tag.G2 K) := by
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨B, hB, -⟩ :=
    (CFSG.LieType.Chevalley.G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).1
  obtain ⟨-, -, hdC, -⟩ :=
    (CFSG.LieType.Chevalley.G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).2 B hB
      (signA K)
  have hneg : (-1 : Kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK2 (congrArg Units.val h)
  have hd1 : rootDiagUnit .G2 (signA K) ≠ 1 := by
    intro h
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_one] at h
    have h0 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) ⟨0, by decide⟩
    exact hneg h0
  have hd2 : rootDiagUnit .G2 (signA K) * rootDiagUnit .G2 (signA K) = 1 := by
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_one]
    congr 1
    funext i
    fin_cases i
    · change (-1 : Kˣ) * (-1) = 1
      rw [neg_mul_neg, one_mul]
    · change (1 : Kˣ) * 1 = 1
      rw [one_mul]
  have hα : IsRoot Tag.G2 rootA := CFSG.Quasithin.G2U.isRoot_iff_mem_rootList.mpr (by decide)
  obtain ⟨hQle, ⟨eα⟩, -⟩ :=
    CFSG.LieType.Chevalley.odd_arbitrary_root_pair_SL2_p_components .G2 K hK2 hα
  let t : adjointGroup Tag.G2 K := ⟨rootDiagUnit .G2 (signA K), hdC⟩
  let ι : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup Tag.G2 K :=
    (Subgroup.inclusion hQle).comp eα.toMonoidHom
  have hι : Function.Injective ι :=
    (Subgroup.inclusion_injective hQle).comp eα.injective
  have ht : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using hd2)
    · intro h
      exact hd1 (congrArg Subtype.val h)
  have hc : ∀ g, ι g * t = t * ι g := by
    intro g
    have hmem : (eα g : ModGL Tag.G2 K) ∈ CFSG.LieType.Chevalley.toralCentralizer Tag.G2 K (signA K) := by
      apply rootSpan_le_toralCentralizer (signA K)
      rw [rootSpan_signA hK2]
      exact Subgroup.mem_sup_left (eα g).2
    have h1 := Subgroup.mem_centralizer_iff.mp hmem.2 (rootDiagUnit .G2 (signA K))
      (Set.mem_singleton _)
    exact Subtype.ext h1.symm
  exact rankFourCover_of_SL2 hK hp2 he ι hι ht hc

end CFSG.RankThree.PartOne.SRC
