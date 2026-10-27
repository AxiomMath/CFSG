module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeFrameA
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeClassA
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeKer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwE6Three_frameClass_of_tb
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* TwE6Delta.RecipeR K n} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ₀ A) :
    ∃ κ : ↥A →* Multiplicative (Fin Tag.E6.rank → ZMod 3), GGE6ThreeFrameA A κ ∧
      ∀ (y : ↥A) (J : Subgroup L'), y ≠ 1 → IsComponentOf J (fixSubgroup (y : MulAut L')) →
        GGE6ThreeClassA A κ y J (∃ m : ℕ, 1 ≤ m ∧
          GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) := by
  obtain ⟨σ, hσ, ψ, hk, hTB'⟩ := ggTwE6Three_tbGroup_twisted hn hK hTB
  have hker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 := hk ▸ ggTwE6Three_ker_pow_three hn h3 hK hTB
  obtain ⟨hψ, hker, hperf, hA, hAH, h5, -, hsc⟩ := hTB'
  obtain ⟨Fm⟩ := ggTwE6Three_frame_exists hn hK h3 hσ hψ hker hperf hA hAH h5 hsc
  exact ⟨Fm.κ, ggTwE6Three_frameA hn hK h3 hσ hψ hker hker3 Fm,
    fun _ _ hy1 hJ => ggTwE6Three_classA hn hK h3 hσ hψ hker hperf hker3 Fm hy1 hJ⟩

end CFSG.StandardType

end
