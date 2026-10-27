module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviFiveCell
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem tw5g_two_le_of_dvd_sub {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (h : p ∣ 2 ^ n - 1) :
    2 ≤ n := by
  by_contra hlt
  have : n = 1 := by omega
  subst this
  have h1 : p ∣ 1 := by simpa using h
  exact hp.ne_one (Nat.dvd_one.mp h1)

theorem ggTBJTwE6LeviL_geFive
     (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (5 ≤ p ∧ ¬ 3 ∣ 2 ^ n + 1) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ n hΛ hL _ _ _ _ _ hnc
  have hP : 5 ≤ p ∧ ¬ 3 ∣ 2 ^ n + 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp5, h3⟩ := hP
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  have heq : labs = (⟨.twE6, 0, n⟩ : LargeEvenLabel) :=
    eq_of_ggLabelIso_of_excTag (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (hRig ⟨.twE6, 0, n⟩ labs _ hΛ hlabs hL hhass)
  have hs : LargeEvenSplit p (⟨.twE6, 0, n⟩ : LargeEvenLabel) := heq ▸ hPs.1
  have hpn : p ∣ 2 ^ n + 1 := by
    rcases hs with ⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨ht, -⟩ | ⟨-, h3'⟩
    · exact absurd hu (by simp [LargeEvenUntwisted])
    · exact h
    · simp at ht
    · omega
  exact ggTBJTwE6LeviL_ge5 hRig hH hΛ hL hp5 hpn h3

theorem ggTBJTwE6LeviK_geFive
     (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviK .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (5 ≤ p ∧ ¬ 3 ∣ 2 ^ n + 1) := by
  intro G _ _ p B Bs x L D J y K hH hJK _ _ _ n hΛ hK hreg _ _ _ _ hnc
  have hP : 5 ≤ p ∧ ¬ 3 ∣ 2 ^ n + 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp5, h3⟩ := hP
  rcases hreg with hm | hpn
  · have hn2 : 2 ≤ n := tw5g_two_le_of_dvd_sub Fact.out hΛ.1 hm
    have hinn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
    have hZ : Subgroup.center ↥K = ⊥ :=
      ggTwE6_center_eq_bot hn2 h3 (P := fun lab _ _ _ _ _ =>
        lab = (⟨.twE6, 0, n⟩ : LargeEvenLabel) ∧ _)
        (fun _ _ _ _ _ _ h => h.1) (ggInnerDiagOn_relabel hRig hinn hΛ hK)
    exact ggTBJTwE6LeviK_minus_ge5 hRig hH hJK hΛ hK hp5 hm hZ
  · exact ggTBJTwE6LeviK_ge5 hRig hH hJK hΛ hK hp5 hpn h3

end CFSG.StandardType

end
