module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6CompLabCat
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLMarking
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Bridge
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Labels
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6UniqueCompLabelMarking

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Certificates

private theorem e6eps_rawDatum_elim_const'
    {lab : LargeEvenLabel} {Q : Prop}
    (h : LargeEvenRawDatum lab (fun _ _ _ _ => Q)) : Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear, LargeEvenRecipeUnitary,
    LargeEvenRecipeSymplectic, LargeEvenRecipeOmegaPlus, LargeEvenRecipeOmegaMinus,
    LargeEvenRecipeChevalley, LargeEvenRecipeTwisted, LargeEvenRecipeSuzuki,
    LargeEvenRecipeG2Derived, LargeEvenRecipeTwF4Inherited] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact hq)

private theorem e6eps_index
    {G : Type} [Group G] {t : CFSG.Open.StatedLieTag} {p f : ℕ}
    (ht : t = .E6 ∨ t = .twistedE6)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel G t p f) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      d.1.characteristic = p ∧
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = p ^ f ∧
      ((∃ q : TauCeti.PrimePower, d.1 = .E6 q) ∨
        (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q)) ∧
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  rcases ht with rfl | rfl
  · obtain ⟨hadm, hm⟩ := h
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
    obtain ⟨b⟩ := hB.e6 q hv K (by rw [hK, hq])
    exact ⟨⟨TauCeti.LieTypeIndex.E6 q, hv⟩, by simp [q],
      by show q.card = p ^ f; rw [hq], Or.inl ⟨q, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨hadm, hm⟩ := h
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
    obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨b⟩ := hB.twistedE6 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩, by simp [q],
      by show q.card = p ^ f; rw [hq], Or.inr ⟨q, rfl⟩, ⟨e.trans b⟩⟩

theorem ggTorsion_E6eps_unique_label
    {X : Type} [Group X] [Finite X] {δ : MulAut X} {J : Subgroup X}
    (hdat : GGTorsionDatum (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6) 3 δ J)
    (hq : LargeEvenMarking X fun lab _ _ _ _ _ => 2 ≤ lab.n)
    (huniq : ∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) :
    LargeEvenMarking X fun lab _ _ _ _ _ =>
      (lab.tag = .E6 ∨ lab.tag = .twE6) ∧
        ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧ GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) ∧
          E6CompLabel (2 ^ lab.n) lab' := by
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .E6 ∨ lab.tag = .twE6 :=
    e6eps_rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh.1) hraw)
  have h2le : 2 ≤ lab.n := by
    obtain ⟨-, lab1, hlab1, hraw1⟩ := hq
    have hHas1 : GGHasLabel lab1 (X ⧸ Subgroup.center X) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw1
    have hHas : GGHasLabel lab (X ⧸ Subgroup.center X) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw
    have hq1 : 2 ≤ lab1.n :=
      e6eps_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hraw1)
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso lab lab1 := hrigid lab lab1 _ hlab hlab1 hHas hHas1
    have heq : lab = lab1 := eq_of_ggLabelIso_of_e6Tag hIso htag
    rw [heq]
    exact hq1
  have hdat' : GGTorsionDatum (fun lab => (lab.tag = .E6 ∨ lab.tag = .twE6) ∧ 2 ≤ lab.n) 3 δ J :=
    ⟨hp, hp2, hδp, hδ1, hcomp,
      ⟨hXc, lab, hlab,
        largeEvenRawDatum_mono
          (fun R _ I F h =>
            ⟨h.1, h.2.1, h.2.2.elim fun θ hθ => ⟨θ, ⟨hθ.1, h2le⟩, hθ.2⟩⟩)
          hraw⟩⟩
  have hQ : ∀ lab : LargeEvenLabel, ((lab.tag = .E6 ∨ lab.tag = .twE6) ∧ 2 ≤ lab.n) →
      lab.tag = .E6 ∨ lab.tag = .twE6 := fun _ h => h.1
  have hcat : ∀ lab : LargeEvenLabel, ((lab.tag = .E6 ∨ lab.tag = .twE6) ∧ 2 ≤ lab.n) →
      ∀ (R : Type) [Group R],
        CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n →
          UniqueCompLabelAt (fun lab' => E6CompLabel (2 ^ lab.n) lab') R := by
    rintro lab ⟨htaglab, h2lelab⟩ R _ hchev
    have ht2 : markTag lab = .E6 ∨ markTag lab = .twistedE6 := by
      rcases htaglab with h | h
      · exact Or.inl (by simp [markTag, h])
      · exact Or.inr (by simp [markTag, h])
    obtain ⟨d, hdchar, hk, hd, he⟩ := e6eps_index (p := 2) (f := lab.n) ht2 hchev
    obtain ⟨e⟩ := he
    have hq4 : 4 ≤ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 := by
      rw [hk, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) h2lelab
    have hh : UniqueCompLabelAt
        (fun lab' => E6CompLabel (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1) lab') R :=
      uniqueCompLabelAt_of_mulEquiv e.symm (compLabE6_cat_of_lang d hdchar hd hq4)
    exact hk ▸ hh
  have hmark := ggTorsion_E6eps_uniqueCompLabel
    (Q := fun lab : LargeEvenLabel => (lab.tag = .E6 ∨ lab.tag = .twE6) ∧ 2 ≤ lab.n)
    (P := fun (lab lab' : LargeEvenLabel) => E6CompLabel (2 ^ lab.n) lab') hQ hcat hdat' huniq
  obtain ⟨hXc', lab', hlab', hraw'⟩ := hmark
  refine ⟨hXc', lab', hlab', largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨hs, hna, θ, hQlab, hExists⟩
  exact ⟨hs, hna, θ, hQlab.1, hExists⟩

end Certificates

end CFSG.StandardType.TablePThreeKG

end
