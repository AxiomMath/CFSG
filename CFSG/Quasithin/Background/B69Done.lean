module

public import CFSG.Quasithin.Background.B69Input
public import CFSG.Quasithin.Background.B69NonSolv

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_active (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4) {X T M : Subgroup (MulAut V)}
    (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hns : ¬ Group.IsSolvable ↥X) :
    ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X →
      ∃ A, IsFFStarMin X A ∧ ⁅L, A⁆ = L := by
  intro L hL
  obtain ⟨A₀, hA₀⟩ := (B1_7 hV hFF).1
  obtain ⟨L₀, hL₀, hLA₀⟩ := exists_component_of_nonsolvable hV hP4 h hO2 hns hA₀
  obtain ⟨t, ht, hconj⟩ := exists_conj_component h hL₀ hL
  refine ⟨B6.conjSub t A₀, isFFStarMin_conjSub hA₀ (h.isSylow.1 ht), ?_⟩
  rw [← hconj, commutator_conjSub, hLA₀]

theorem structConcl_of_nonsolvable (hP4 : AsB15Part4) (hComp : AsB69Component)
    (hG1 : AsB69AltBlock) (hG2 : AsB69GenByMin) (hV : ∀ v : V, v ^ 2 = 1)
    {X T M : Subgroup (MulAut V)}
    (hsq : ∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧
      CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f)
    (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hns : ¬ Group.IsSolvable ↥X) : ∃ 𝓗 : Finset (Subgroup (MulAut V)), StructConcl X T M 𝓗 := by
  have hctx : ShapeCtx X T M := shapeCtx_of_component hComp hV hsq h hO2 hFF hns
  have hact := exists_active hV hP4 h hO2 hFF hns
  have hffJ : ffJ X ≤ ⨆ (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X), blk X L := by
    refine (hG2 V hV X T M hsq h hO2 hFF hns).trans ?_
    refine iSup₂_le fun A hA => iSup_le fun _ => ?_
    obtain ⟨L, hL, hLA⟩ := exists_component_of_nonsolvable hV hP4 h hO2 hns hA
    exact (le_blk_of hA hLA).trans
      (le_iSup₂_of_le (f := fun (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X) =>
        blk X L) L hL le_rfl)
  have hG1' : ∀ A L : Subgroup (MulAut V), IsFFStarMin X A → CFSG.Open.IsComponentOf L X →
      ⁅L, A⁆ = L → AltShape M A L (commV L) → ∀ A' : Subgroup (MulAut V), IsFFStarMin X A' →
        ⁅L, A'⁆ = L → A' ≤ L ⊔ A := fun A L hA hL hLA hAlt A' hA' hLA' =>
    hG1 V hV X T M A L ⟨hsq, h, hO2, hFF, hns, hA, hL, hLA⟩ (commV L)
      (commV_mem_irrPlus hV hctx hA hL hLA) hAlt A' hA' hLA'
  exact ⟨blkFamily X, structConcl_of_blkCtx ⟨hV, hP4, hctx, hO2, hact, hffJ, hG1'⟩ h hFF⟩

theorem b69Struct_of_inputs (hP4 : AsB15Part4) (hComp : AsB69Component) (hG1 : AsB69AltBlock)
    (hG2 : AsB69GenByMin) : B69Struct := by
  rw [b69Struct_iff]
  intro V _ _ hV X T M hsq h hO2 hFF
  by_cases hsolv : Group.IsSolvable ↥X
  · exact structConcl_of_solvable hV h hO2 hFF hsolv
  · exact structConcl_of_nonsolvable hP4 hComp hG1 hG2 hV hsq h hO2 hFF hsolv

end B69

end CFSG.Quasithin
