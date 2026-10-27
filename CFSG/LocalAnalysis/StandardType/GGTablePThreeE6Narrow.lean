module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6NotG2
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6D4Odd
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Labels
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6KG5c
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6KG5f
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableZ

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem rawDatum_elim_const' {lab : LargeEvenLabel} {Q : Prop}
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

private theorem datumOn_mono {F F' : LargeEvenLieTag → Prop}
    (hFF : ∀ t, F t → F' t) {X : Type} [Group X]
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (h : DatumOn F X A δ J) : DatumOn F' X A δ J :=
  ⟨h.1, h.2.1, h.2.2.1,
    largeEvenMarking_mono
      (fun lab R _ I F'' θ ⟨hF, hs3, hin⟩ => ⟨hFF lab.tag hF, hs3, hin⟩) h.2.2.2⟩

private theorem twE6_marking_tag
    {X : Type} [Group X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .twE6) X A δ J) :
    GGMarkingAll (K := X) (fun lab _ _ _ _ _ => LargeEvenSplit 3 lab → lab.tag = .twE6) := by
  obtain ⟨-, lab0, hlab0, hraw0⟩ := hD.2.2.2
  have htag0 : lab0.tag = .twE6 :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh.1) hraw0)
  have hHas0 : GGHasLabel lab0 (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw0
  have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
  intro P hP
  obtain ⟨-, lab, hlab, hraw⟩ := hP
  have hHas : GGHasLabel lab (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw
  have hEq : lab0 = lab :=
    eq_of_ggLabelIso_of_e6Tag (hrigid lab0 lab _ hlab0 hlab hHas0 hHas) (Or.inr htag0)
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hPθ⟩
  exact ⟨hs, hna, θ, hPθ, fun _ => by rw [← hEq]; exact htag0⟩

private theorem kg5e_twE6_concl
    {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .twE6) X A δ J)
    (hq : LargeEvenMarking X (fun lab _ _ _ _ _ => 2 ≤ lab.n)) :
    GGMarkingAll (K := X) (fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twD ∧ lab.rank = 5) ∨
        (lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) ∨
        (lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1)) := by
  have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
    datumOn_mono (fun t ht => Or.inr ht) hD
  have hq' : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .E6 → 2 ≤ lab.n) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h2 => fun _ => h2) hq
  have hsix : GGMarkingAll (K := X)
      (fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
        (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)) :=
    e6eps_marking_labels hX hD6 hq'
  have htagall : GGMarkingAll (K := X)
      (fun lab _ _ _ _ _ => LargeEvenSplit 3 lab → lab.tag = .twE6) :=
    twE6_marking_tag hX hD
  refine ggMarkingAll_mono (fun lab R _ I F θ h hsplit => ?_)
    (ggMarkingAll_and hsix htagall)
  obtain ⟨h6, htag6⟩ := h
  rcases h6 hsplit with hE6 | hTw
  · have htw := htag6 hsplit
    rw [hE6.1] at htw
    exact absurd htw (by decide)
  · exact Or.inl hTw

private theorem knownOverSix_of_cover {Dall : DatumPred} {ι : Type} {D : ι → DatumPred}
    (hcover : ∀ (X : Type) [Group X] (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X),
      Dall X A δ J → ∃ i, D i X A δ J)
    (h : ∀ i, KnownOverSix (D i)) : KnownOverSix Dall := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.2.2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.2.2.2 X hX A δ J hi

@[expose] def E6SmallOn (i : Fin 11) : DatumPred := fun X [Group X] A δ J =>
  DatumOn (fam i) X A δ J ∧ LargeEvenMarking X (fun lab _ _ _ _ _ => lab.n < 2)

@[expose] def E6LargeOn (i : Fin 11) : DatumPred := fun X [Group X] A δ J =>
  DatumOn (fam i) X A δ J ∧ LargeEvenMarking X (fun lab _ _ _ _ _ => 2 ≤ lab.n)

private theorem e6SmallOrLarge_cover {i : Fin 11} {X : Type} [Group X]
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam i) X A δ J) :
    E6SmallOn i X A δ J ∨ E6LargeOn i X A δ J := by
  obtain ⟨hXc, lab0, hlab0, hraw0⟩ := hd.2.2.2
  rcases Nat.lt_or_ge lab0.n 2 with hn | hn
  · left
    refine ⟨hd, hXc, lab0, hlab0, largeEvenRawDatum_mono ?_ hraw0⟩
    rintro R _ I F ⟨hs, hna, θ, -, -, -⟩
    exact ⟨hs, hna, θ, hn⟩
  · right
    refine ⟨hd, hXc, lab0, hlab0, largeEvenRawDatum_mono ?_ hraw0⟩
    rintro R _ I F ⟨hs, hna, θ, -, -, -⟩
    exact ⟨hs, hna, θ, hn⟩

theorem knownOverSix_E6Large
    (hZ : TwE6A2CentreInput) (i : Fin 11) (hi : i = 5 ∨ i = 6) : KnownOverSix (E6LargeOn i) := by
  rcases hi with rfl | rfl
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro X _ _ hX A δ J hD
      obtain ⟨hDatum, _hq⟩ := hD
      exact kg5a_exc hX (datumOn_mono (fun t ht => Or.inl ht) hDatum)
    · intro X _ _ hX A δ J hD _hJ _hZJ
      obtain ⟨hDatum, hq⟩ := hD
      have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
        datumOn_mono (fun t ht => Or.inl ht) hDatum
      have hq' : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .E6 → 2 ≤ lab.n) :=
        largeEvenMarking_mono (fun _ _ _ _ _ _ h2 => fun _ => h2) hq
      refine ggMarkingAll_mono (fun lab R _ I F θ h hsplit => ?_)
        (e6eps_marking_labels hX hD6 hq')
      rcases h hsplit with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · intro X _ _ hX A δ J hD hJ hZJ
      obtain ⟨hDatum, hq⟩ := hD
      have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
        datumOn_mono (fun t ht => Or.inl ht) hDatum
      exact absurd ⟨hJ, hZJ⟩ (kg5c_E6eps hZ hX hD6 hq)
    · intro X _ _ hX A δ J hD _hJ
      obtain ⟨hDatum, hq⟩ := hD
      have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
        datumOn_mono (fun t ht => Or.inl ht) hDatum
      have hq' : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .E6 → 2 ≤ lab.n) :=
        largeEvenMarking_mono (fun _ _ _ _ _ _ h2 => fun _ => h2) hq
      exact e6eps_marking_labels hX hD6 hq'
    · intro X _ _ hX A δ J hD hJ
      obtain ⟨hDatum, hq⟩ := hD
      have hE6 : DatumOn (fun t => t = .E6) X A δ J :=
        datumOn_mono (fun t ht => ht) hDatum
      exact absurd hJ (kg5e_E6 hX hE6 hq)
    · intro X _ _ hX A δ J hD hJ
      obtain ⟨hDatum, hq⟩ := hD
      have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
        datumOn_mono (fun t ht => Or.inl ht) hDatum
      exact absurd hJ (kg5f_E6eps hX hD6 hq)
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro X _ _ hX A δ J hD
      obtain ⟨hDatum, _hq⟩ := hD
      exact kg5a_exc hX (datumOn_mono (fun t ht => Or.inr (Or.inl ht)) hDatum)
    · intro X _ _ hX A δ J hD _hJ _hZJ
      obtain ⟨hDatum, hq⟩ := hD
      have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
        datumOn_mono (fun t ht => Or.inr ht) hDatum
      have hq' : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .E6 → 2 ≤ lab.n) :=
        largeEvenMarking_mono (fun _ _ _ _ _ _ h2 => fun _ => h2) hq
      refine ggMarkingAll_mono (fun lab R _ I F θ h hsplit => ?_)
        (e6eps_marking_labels hX hD6 hq')
      rcases h hsplit with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · intro X _ _ hX A δ J hD hJ hZJ
      obtain ⟨hDatum, hq⟩ := hD
      have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
        datumOn_mono (fun t ht => Or.inr ht) hDatum
      exact absurd ⟨hJ, hZJ⟩ (kg5c_E6eps hZ hX hD6 hq)
    · intro X _ _ hX A δ J hD _hJ
      obtain ⟨hDatum, hq⟩ := hD
      have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
        datumOn_mono (fun t ht => Or.inr ht) hDatum
      have hq' : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .E6 → 2 ≤ lab.n) :=
        largeEvenMarking_mono (fun _ _ _ _ _ _ h2 => fun _ => h2) hq
      exact e6eps_marking_labels hX hD6 hq'
    · intro X _ _ hX A δ J hD _hJ
      obtain ⟨hDatum, hq⟩ := hD
      have hTw : DatumOn (fun t => t = .twE6) X A δ J :=
        datumOn_mono (fun t ht => ht) hDatum
      exact kg5e_twE6_concl hX hTw hq
    · intro X _ _ hX A δ J hD hJ
      obtain ⟨hDatum, hq⟩ := hD
      have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
        datumOn_mono (fun t ht => Or.inr ht) hDatum
      exact absurd hJ (kg5f_E6eps hX hD6 hq)

theorem knownOverSix_E6
    (hZ : TwE6A2CentreInput) (i : Fin 11) (hi : i = 5 ∨ i = 6) (hsmall : KnownOverSix (E6SmallOn i)) :
    KnownOverSix (DatumOn (fam i)) := by
  refine knownOverSix_of_cover
    (D := fun b : Bool => match b with | false => E6SmallOn i | true => E6LargeOn i) ?_ ?_
  · intro X _ A δ J hd
    rcases e6SmallOrLarge_cover hd with hl | hr
    · exact ⟨false, hl⟩
    · exact ⟨true, hr⟩
  · intro b
    cases b
    · exact hsmall
    · exact knownOverSix_E6Large hZ i hi

end CFSG.StandardType.TablePThreeKG

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTablePThreeKnownRestSixLow : Prop :=
  TablePThreeKG.KnownSixOn (fun i => i ≠ 0 ∧ i ≠ 10 ∧ i ≠ 5 ∧ i ≠ 6) ∧
    TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 5) ∧
    TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 6) ∧ TablePThreeKG.TwE6A2CentreInput

theorem ggTablePThreeKnownRestSix_of_low
    (h : GGTablePThreeKnownRestSixLow) : GGTablePThreeKnownRestSix := by
  obtain ⟨hLow, hSmall5, hSmall6, hZ⟩ := h
  intro i hi
  by_cases h5 : i = 5
  · subst h5
    exact TablePThreeKG.knownOverSix_E6 hZ 5 (Or.inl rfl) hSmall5
  · by_cases h6 : i = 6
    · subst h6
      exact TablePThreeKG.knownOverSix_E6 hZ 6 (Or.inr rfl) hSmall6
    · exact hLow i ⟨hi.1, hi.2, h5, h6⟩

end CFSG.StandardType

end
