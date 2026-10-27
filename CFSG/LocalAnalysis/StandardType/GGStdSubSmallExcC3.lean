module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3Hat
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3Bstar
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthBstar

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6 RecipeFieldE6
  TableBExc.E6Three


theorem ggStdSubTwoTorusSLTwoAut_E6_three (K : Type) [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) :
    GGStdSubTwoTorusSLTwoAut 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have hroot : ∀ S : (Fin Tag.E6.rank → ℤ) → Prop, S = IsRoot Tag.E6 →
      GGStdSubTwoTorusSLTwoAut 3 5
        (LargeEvenCenterQuot (MarkChev.chevH Tag.E6.cartan S K false))
        {φ | IsInnDiagOn (MarkChev.chevH Tag.E6.cartan S K false) (markDiagUnit S K) φ} := by
    rintro S rfl
    rw [markDiagUnit_isRoot]
    suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.E6) K), H = adjointGroup Tag.E6 K →
        GGStdSubTwoTorusSLTwoAut 3 5 (LargeEvenCenterQuot H)
          {φ | IsInnDiagOn H (rootDiagUnit Tag.E6) φ} from
      key _ (chevH_false_eq_adjointGroup K Tag.E6)
    intro H hH
    subst hH
    have hZ : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
    have hmk : Function.Injective (LargeEvenCenterMk (adjointGroup Tag.E6 K)) := by
      rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
    refine ggStdSubTwoTorusSLTwoAut_of_mulEquiv (centerQuotEquivOfBot hZ) (fun φ hφ => ?_)
      (ggStdSubTwoTorusSLTwoAut_hat hK h3)
    obtain ⟨g, hg, a, -, -, hφc⟩ := hφ
    refine ⟨⟨g * rootDiagUnit .E6 a, ⟨g, hg, a, rfl⟩⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    have h1 := hφc.2 h (hφc.1 h h.2)
    rw [congr_centerQuotEquivOfBot_mk hZ φ h] at h1
    rw [coe_hatAut_apply]
    exact (congrArg Subtype.val (hmk h1)).symm
  have h := hroot _ (largeEvenIsRoot_eq_isRoot Tag.E6)
  rw [← diagHom_eq_markDiagUnit] at h
  suffices key : ∀ H : Subgroup (LargeEvenChevGL Tag.E6.cartan K),
      H = MarkChev.chevH Tag.E6.cartan (LargeEvenIsRoot Tag.E6.cartan) K false →
      GGStdSubTwoTorusSLTwoAut 3 5 (LargeEvenCenterQuot H)
        (LargeEvenChevIDImage Tag.E6.cartan K H) from
    key _ (largeEvenChevH_eq _ K false)
  intro H hH
  subst hH
  intro Ab hAb hAbI
  exact h Ab hAb fun φ hφ => mem_chevID_iff_isInnDiagOn.mp (hAbI φ hφ)

theorem largeEvenLabelAll_innerSmall_e6Three {p : ℕ} {lab : LargeEvenLabel}
    (h : GGIOneMoreE6ThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, rfl, h3⟩ := h
  dsimp only at htag h3
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK, hl⟩ := TableBExc.recipeChevalleyE6_torusLift_three h3 hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQK, 5, hl,
    ggStdSubTwoTorusInnerSmall_of_slTwoAut Nat.prime_three (by norm_num)
      (ggStdSubTwoTorusSLTwoAut_E6_three K hK h3)⟩

theorem ggStdSubSmallInputOn_e6Three : GGStdSubSmallInputOn GGIOneMoreE6ThreeLabel :=
  ggStdSubSmallInputOn_of_labels_innerSmall ggLNoncyclicInput_holds fun _ _ _ hlab h _ =>
    largeEvenLabelAll_and (largeEvenLabelAll_bstarEq_e6Three hlab h)
      (largeEvenLabelAll_innerSmall_e6Three h)

end CFSG.StandardType.SmallExc

end
