module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTThreeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
import CFSG.LocalAnalysis.StandardType.GGE6RankFiveTorality
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.TableBExc.E6Three (zetaVec)

theorem twE6_residualPlace_of_toral {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    {X : Type} [Group X] [Finite X] {A B₁ D : Subgroup X} (hB₁A : B₁ ≤ A) (hDB : D ≤ B₁)
    (hB₁el : IsElemAbelian 3 B₁) (hB₁card : 3 ^ 4 ≤ Nat.card B₁)
    (Θ : ↥A →* ModGL (langTag .twistedE6) GGL) (hΘR : ∀ a : ↥A, Θ a ∈ ggFixGp .twistedE6 f)
    (hΘinj : Function.Injective Θ)
    (hXt : NoOffTwE6Three.IsToralE6 GGL ((B₁.subgroupOf A).map Θ)) :
    ∃ E : Subgroup (ModGL (langTag .twistedE6) GGL),
      (∀ a : ↥A, (a : X) ∈ D → Θ a ∈ E) ∧ TwE6LawPos 3 f E := by
  have hel : IsElemAbelian 3 ((B₁.subgroupOf A).map Θ) :=
    (hB₁el.subgroupOf A).map Θ
  have hcard : Nat.card ((B₁.subgroupOf A).map Θ) = Nat.card B₁ := by
    rw [Subgroup.card_map_of_injective hΘinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁A).toEquiv
  refine ⟨(B₁.subgroupOf A).map Θ, fun a ha => ⟨a, ?_, rfl⟩, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (hDB ha)
  · refine twE6LawPos_three_of_toral hf h3 ?_ hel (hcard ▸ hB₁card) hXt
    rintro _ ⟨a, -, rfl⟩
    exact hΘR a

end CFSG.StandardType.LieKnownR2.ExcPos
