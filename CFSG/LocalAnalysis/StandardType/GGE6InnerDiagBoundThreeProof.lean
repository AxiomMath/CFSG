module

public import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof5
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDE6Field
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6 RecipeFieldE6 TableBExc.E6Three

namespace E6IDB

@[expose] def E6InnerDiagBoundOn (K : Type) [Field K] (S : (Fin Tag.E6.rank → ℤ) → Prop) : Prop :=
  GGInnerDiagBound 3 5 (LargeEvenCenterQuot (MarkChev.chevH Tag.E6.cartan S K false))
    {φ | IsInnDiagOn (MarkChev.chevH Tag.E6.cartan S K false) (markDiagUnit S K) φ}

theorem E6InnerDiagBoundOn.of_eq {K : Type} [Field K] {S S' : (Fin Tag.E6.rank → ℤ) → Prop}
    (hS : S = S') (h : E6InnerDiagBoundOn K S) : E6InnerDiagBoundOn K S' :=
  hS ▸ h

section Cert


theorem e6InnerDiagBoundOn_isRoot (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) (h3n : 3 ∣ n) :
    E6InnerDiagBoundOn K (IsRoot Tag.E6) := by
  unfold E6InnerDiagBoundOn
  rw [markDiagUnit_isRoot]
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.E6) K), H = adjointGroup Tag.E6 K →
      GGInnerDiagBound 3 5 (LargeEvenCenterQuot H) {φ | IsInnDiagOn H (rootDiagUnit Tag.E6) φ} from
    key _ (chevH_false_eq_adjointGroup K Tag.E6)
  intro H hH
  subst hH
  have hZ : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hmk : Function.Injective (LargeEvenCenterMk (adjointGroup Tag.E6 K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  refine ggInnerDiagBound_of_mulEquiv (centerQuotEquivOfBot hZ) (fun φ hφ => ?_)
    (fun φ hφ => ?_) (ggInnerDiagBound_adjoint_E6 hn hK h3 h3n)
  · obtain ⟨g, hg, a, -, -, hφc⟩ := hφ
    refine ⟨⟨g * rootDiagUnit .E6 a, ⟨g, hg, a, rfl⟩⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    have h1 := hφc.2 h (hφc.1 h h.2)
    rw [congr_centerQuotEquivOfBot_mk hZ φ h] at h1
    rw [coe_hatAut_apply]
    exact (congrArg Subtype.val (hmk h1)).symm
  · obtain ⟨⟨_, g, hg, a, rfl⟩, hx⟩ := hφ
    refine ⟨g, hg, a, fun h hh => conj_rootDiagUnit_mem_adjointGroup a hh, fun h hh => ?_,
      fun h hh => (hatAut .E6 K ⟨_, g, hg, a, rfl⟩ ⟨h, hh⟩).2, fun h hh => ?_⟩
    · have := conj_rootDiagUnit_mem_adjointGroup (K := K) a⁻¹ hh
      rwa [rootDiagUnit_inv a⁻¹, inv_inv, ← rootDiagUnit_inv] at this
    · rw [congr_centerQuotEquivOfBot_mk hZ φ h, ← hx]
      rfl

theorem ggInnerDiagBound_recipe_E6 (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) (h3n : 3 ∣ n) :
    GGInnerDiagBound 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have h := (e6InnerDiagBoundOn_isRoot K hn hK h3 h3n).of_eq
    (largeEvenIsRoot_eq_isRoot Tag.E6).symm
  unfold E6InnerDiagBoundOn at h
  rw [← diagHom_eq_markDiagUnit] at h
  suffices key : ∀ H : Subgroup (LargeEvenChevGL Tag.E6.cartan K),
      H = MarkChev.chevH Tag.E6.cartan (LargeEvenIsRoot Tag.E6.cartan) K false →
      GGInnerDiagBound 3 5 (LargeEvenCenterQuot H) (LargeEvenChevIDImage Tag.E6.cartan K H) from
    key _ (largeEvenChevH_eq _ K false)
  intro H hH
  subst hH
  have hI : LargeEvenChevIDImage Tag.E6.cartan K
        (MarkChev.chevH Tag.E6.cartan (LargeEvenIsRoot Tag.E6.cartan) K false) =
      {φ | IsInnDiagOn (MarkChev.chevH Tag.E6.cartan (LargeEvenIsRoot Tag.E6.cartan) K false)
        (TableB.diagHom Tag.E6.cartan K) φ} :=
    Set.ext fun _ => mem_chevID_iff_isInnDiagOn
  rw [hI]
  exact h

end Cert

end E6IDB

section Main


theorem ggE6InnerDiagBoundThreeInput_holds : GGE6InnerDiagBoundThreeInput := by
  intro K _ _ n hn hK h3 h3n
  exact E6IDB.ggInnerDiagBound_recipe_E6 K hn hK h3 h3n

end Main

end CFSG.StandardType

end
