module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallDefs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

theorem svTransport_holds :
    ∀ F : LargeEvenLieTag → Prop, SVRank F →
      ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
        ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), ¬ DatumOn F X A δ J := by
  intro F hF X _ _ hX A δ J hD
  unfold SVRank at hF
  unfold DatumOn at hD
  obtain ⟨hK, -, h3, hmark⟩ := hD
  have hmark' := largeEvenMarking_and_labelAll_simple_imp
    (S := fun lab => F lab.tag)
    (P' := SCFourCover.GGInndiagThreeRankTwo) hF hmark
  obtain ⟨-, lab, R, hR, I, F', θ, hlab, hP⟩ := largeEvenMarking_exists' hmark'
  letI := hR
  have hAeb : CFSG.Open.IsElemAbelian 3 A := hK.1.1
  have hinn : GGInducedInn A θ I := hP.1.2.2
  have hrank : SCFourCover.GGInndiagThreeRankTwo R I F' := hP.2 hP.1.1
  unfold SCFourCover.GGInndiagThreeRankTwo at hrank
  set B : Subgroup (MulAut R) := A.map (ggInducedAut θ) with hBdef
  have hBeb : CFSG.Open.IsElemAbelian 3 B := by
    rw [hBdef]
    exact CFSG.Open.IsElemAbelian.map hAeb (ggInducedAut θ)
  have hBle : B ≤ Subgroup.closure I := by
    intro b hb
    rw [hBdef, Subgroup.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact Subgroup.subset_closure (hinn a ha)
  have hcard : Nat.card B = Nat.card A := by
    rw [hBdef]
    exact Subgroup.card_map_of_injective (K := A)
      (ggInducedAut_injective_of_perfect hX θ)
  have h9 : Nat.card B ≤ 9 := hrank B hBeb hBle
  have h27 : 27 ≤ Nat.card B := by
    rw [hcard]
    norm_num at h3
    exact h3
  omega

end CFSG.StandardType.TablePThreeKG

end
