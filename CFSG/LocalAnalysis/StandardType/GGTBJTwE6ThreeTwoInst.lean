module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoInstClass
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwE6Three_frameClass_of_tb_one
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* TwE6Delta.RecipeR K 1} (hodd : Odd (Nat.card ψ₀.ker))
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1) L' ψ₀ A) :
    ∃ κ : ↥A →* Multiplicative (Fin Tag.E6.rank → ZMod 3), GGE6ThreeFrameA A κ ∧
      ∀ (y : ↥A) (J : Subgroup L'), y ≠ 1 → IsComponentOf J (fixSubgroup (y : MulAut L')) →
        GGE6ThreeClassA A κ y J (∃ m : ℕ, 1 ≤ m ∧
          GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) := by
  obtain ⟨σ, hσ, ψ, hk, hTB'⟩ := tw1f_tbGroup_twisted hK hTB
  have hodd' : Odd (Nat.card ψ.ker) := hk ▸ hodd
  obtain ⟨hψ, hker, hperf, hA, hAH, h5, -, hsc⟩ := hTB'
  have hker3 := tw1f_ker_pow_three hK hσ hψ hker hperf hodd'
  obtain ⟨Fm⟩ := tw1f_frame_exists hK hσ hψ hker hperf hA hAH h5 hsc
  exact ⟨Fm.κ, tw1f_frameA hK hσ hψ hker hker3 hperf Fm,
    fun _ _ hy1 hJ => tw1i_classA hK hσ hψ hker hperf hker3 Fm hy1 hJ⟩

theorem ggTwE6Three_comp_invariant_one
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* TwE6Delta.RecipeR K 1} (hodd : Odd (Nat.card ψ₀.ker))
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1) L' ψ₀ A)
    (y : ↥A) (J : Subgroup L') (hy1 : y ≠ 1)
    (hJ : IsComponentOf J (fixSubgroup (y : MulAut L'))) :
    ∀ a ∈ A, ∀ x ∈ J, a x ∈ J := by
  obtain ⟨σ, hσ, ψ, -, hTB'⟩ := tw1f_tbGroup_twisted hK hTB
  obtain ⟨hψ, hker, hperf, hA, hAH, h5, -, hsc⟩ := hTB'
  obtain ⟨Fm⟩ := tw1f_frame_exists hK hσ hψ hker hperf hA hAH h5 hsc
  exact tw1i_comp_invariant hK hσ hψ hker hperf Fm hy1 hJ

end CFSG.StandardType

end
