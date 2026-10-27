module

public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBJTwE6LeviKFoldCover : Prop :=
  GGTBJETypeLeviK .twE6 fun p n labJ =>
    ggTBJTwE6RowCand p n labJ ∨ ¬ (5 < p ∧ p ∣ 2 ^ n - 1 ∧ 3 ∣ 2 ^ n + 1)

theorem ggTBJLeftOnLab_twE6_foldCover (hRig : GGLabelRigidInput) :
    GGTBJLeftOnLab ggTBJTwE6LabelFoldCover := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨⟨ht, hphi⟩, hp5, h3, hm⟩ := hS
  have ht' : t = .twE6 := ht
  subst ht'
  have hr : r = 0 := hΛ.2
  subst hr
  have hL' : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1.1, hP.2⟩) hL
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  have heq : labs = (⟨.twE6, 0, n⟩ : LargeEvenLabel) :=
    eq_of_ggLabelIso_of_excTag (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (hRig ⟨.twE6, 0, n⟩ labs _ hΛ hlabs hhas hhass)
  have hs : LargeEvenSplit p (⟨.twE6, 0, n⟩ : LargeEvenLabel) := heq ▸ hPs.1
  have hn1 : 1 ≤ n := hΛ.1
  have hpn : p ∣ 2 ^ n + 1 := by
    rcases hs with ⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨ht, -⟩ | ⟨-, h3'⟩
    · exact absurd hu (by simp [LargeEvenUntwisted])
    · exact h
    · simp at ht
    · omega
  exfalso
  have hm' : p ∣ 2 ^ n - 1 := hm
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hdiv : p ∣ 2 := by
    have h1 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpn hm'
    have : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rwa [this] at h1
  have := Nat.le_of_dvd (by norm_num) hdiv
  omega

theorem ggTBJNbrOnLab_twE6_foldCover (hI3 : GGNbrSubcomponentInput)
    (hK : GGTBJTwE6LeviKFoldCover) : GGTBJNbrOnLab ggTBJTwE6LabelFoldCover := by
  intro G _ _ p B Bs x L D J y K hH hp hK' hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨⟨ht, hphi⟩, hp5, h3, hm⟩ := hS
  have ht' : t = .twE6 := ht
  subst ht'
  have hr : r = 0 := hΛ.2
  subst hr
  have hreg : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := Or.inl hm
  have hK'' : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1.1, hP.2⟩) hK'
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hH.2.2.2.2.1
  have hnc : ¬ (ggTBJTwE6RowCand p n labJ ∨ ¬ (5 < p ∧ p ∣ 2 ^ n - 1 ∧ 3 ∣ 2 ^ n + 1)) := by
    rintro (h | h)
    · rcases h with ⟨-, -, hp3, -⟩ | ⟨-, hp3, -⟩ | ⟨-, -, hp3, -⟩ <;> omega
    · exact h ⟨hp5, hm, h3⟩
  exact (hK G p B Bs x L D J y K hH hJK hK'' hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hnc).imp id
    Or.inl

theorem GGTBJOrdinaryOutside.of_twE6_foldCover {E : ℕ → LargeEvenLabel → Prop}
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput)
    (hK : GGTBJTwE6LeviKFoldCover)
    (h : GGTBJOrdinaryOutside fun p lab => E p lab ∨ ggTBJTwE6LabelFoldCover p lab) :
    GGTBJOrdinaryOutside E :=
  GGTBJOrdinaryOutside.of_proved ((ggTBJLeftOnLab_twE6_foldCover hRig).toLeftOn hTCJ)
    ((ggTBJNbrOnLab_twE6_foldCover hI3 hK).toNbrOn hTCJ hI3) h

end CFSG.StandardType

end
