module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeA
public import CFSG.LocalAnalysis.StandardType.GGInnLocal
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSymplectic
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeB2der
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthLinear
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNode

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTableBOrthSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

theorem ggBstarInputOn_orthSplit : GGBstarInputOn GGTableBOrthSplitLabel :=
  ggBstarInputOn_of_labels
    (fun _ _ h => h.1.elim (fun h' => Or.inr (Or.inr (Or.inr (Or.inl h'))))
      fun h' => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h', by have := h.2.1; omega⟩)))))
    fun _ _ hp hlab h => (largeEvenLabelAll_tableB_orthogonal h.1 hlab h.2.1 hp h.2.2).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_orthSplit : GGStdSubPreInputOn GGTableBOrthSplitLabel :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_orthogonal h.1 hlab h.2.1 hp h.2.2).mono
      fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

@[expose] def GGBstarDeltaUnitaryInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
    GGTableBUnitaryLiftLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
        GGBstarBoundInn p (ggUnitaryTorusRank p (lab.rank + 1)) R I ∧
        (GGDeltaLocal p (ggUnitaryTorusRank p (lab.rank + 1)) R I ∨
          GGBstarBoundDelta p (ggUnitaryTorusRank p (lab.rank + 1)) R I)

section Unitary

theorem largeEvenLabelAll_torusLift_unitaryLift {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBUnitaryLiftLabel p lab) :
    LargeEvenLabelAll lab fun R _ _ _ =>
      GGTorusLift p (ggUnitaryTorusRank p (lab.rank + 1)) R := by
  rcases h.1 with ht | ⟨ht, hl⟩
  · exact largeEvenLabelAll_torusLift_twA hlab ht hp h.2
  · rw [hl]
    exact largeEvenLabelAll_torusLift_twD3 hlab ht hl hp h.2

theorem ggBstarInputOn_unitaryLift_delta (ha₀ : GGLNoncyclicInput)
    (h : GGBstarDeltaUnitaryInput) : GGBstarInputOn GGTableBUnitaryLiftLabel :=
  ggBstarInputOn_of_labels_delta ha₀ fun p lab hp hlab hS _ =>
    ((largeEvenLabelAll_torusLift_unitaryLift hp hlab hS).and (h p lab hp hlab hS)).mono
      fun _ _ _ _ hh => ⟨hh.2.1, _, hh.1, hh.2.2.1, hh.2.2.2⟩

end Unitary

@[expose] def GGTableBDoneLabel3 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBProvedLabel p lab ∨ GGTableBLinearLabel lab ∨ GGTableBOrthSplitLabel p lab ∨
    GGB2derThreeLabel p lab ∨ GGTableBUnitaryLiftLabel p lab

@[expose] def GGTableBRest3 (F : LargeEvenLabel → Prop) (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  F lab ∧ ¬ GGTableBDoneLabel3 p lab

theorem ggTableB_rest3_cover (p : ℕ) (lab : LargeEvenLabel) :
    ((GGTableBDoneLabel3 p lab ∨ GGTableBRest3 GGTableBUnitaryLabel p lab) ∨
      GGTableBRest3 GGTableBOrthLabel p lab) ∨ GGTableBRest3 GGTableBOtherLabel p lab := by
  by_cases hD : GGTableBDoneLabel3 p lab
  · exact Or.inl (Or.inl (Or.inl hD))
  · rcases ggTableB_family_cover lab with h | h | h | h
    · exact absurd (Or.inr (Or.inl h)) hD
    · exact Or.inl (Or.inl (Or.inr ⟨h, hD⟩))
    · exact Or.inl (Or.inr ⟨h, hD⟩)
    · exact Or.inr ⟨h, hD⟩

theorem not_ggTableBProvedLabelB_of_linear {p : ℕ} {lab : LargeEvenLabel}
    (hL : GGTableBLinearLabel lab) (hP : ¬ GGTableBProvedLabel p lab) :
    ¬ GGTableBProvedLabelB p lab := by
  obtain ⟨t, l, n⟩ := lab
  rintro (h | h | h | h)
  · exact hP h
  all_goals cases t <;>
    simp_all [GGTableBLinearLabel, GGTableBUnitaryLiftLabel, GGTableBOrthPlusLiftLabel,
      GGTableBOrthMinusLiftLabel]

section Unitary

theorem ggBstarInputOn_done3 (ha₀ : GGLNoncyclicInput) (hUD : GGBstarDeltaUnitaryInput) :
    GGBstarInputOn GGTableBDoneLabel3 :=
  (((((ggBstarInputOn_typeA_split_holds.or ggBstarInputOn_symplectic).or
    ggBstarInputOn_linearRest).or ggBstarInputOn_orthSplit).or ggBstarInputOn_b2der).or
    (ggBstarInputOn_unitaryLift_delta ha₀ hUD)).mono fun p lab _ _ h => by
      rcases h with hP | hL | hO | hB | hU
      · exact Or.inl (Or.inl (Or.inl (Or.inl hP)))
      · by_cases hP : GGTableBProvedLabel p lab
        · exact Or.inl (Or.inl (Or.inl (Or.inl hP)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hL, hP⟩)))
      · exact Or.inl (Or.inl (Or.inr hO))
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hU

theorem ggStdSubPreInputOn_done3 (ha₀ : GGLNoncyclicInput)
    (hEUd : GGEndNodeAdmUnitaryDvdInput) (hEUs : GGEndNodeAdmUnitarySmallInput) :
    GGStdSubPreInputOn GGTableBDoneLabel3 :=
  (((((ggStdSubPreInputOn_typeA_split_holds.or ggStdSubPreInputOn_symplectic).or
    ggStdSubPreInputOn_linearRest).or ggStdSubPreInputOn_orthSplit).or ggStdSubPreInputOn_b2der).or
    (ggStdSubPreInputOn_unitaryLift ha₀ (ggEndNodeAdmUnitaryInput_of_parts hEUd hEUs))).mono
    fun p lab _ _ h => by
      rcases h with hP | hL | hO | hB | hU
      · exact Or.inl (Or.inl (Or.inl (Or.inl hP)))
      · by_cases hP : GGTableBProvedLabel p lab
        · exact Or.inl (Or.inl (Or.inl (Or.inl hP)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hL, not_ggTableBProvedLabelB_of_linear hL hP⟩)))
      · exact Or.inl (Or.inl (Or.inr hO))
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hU

theorem ggBstarInput_of_round3 (ha₀ : GGLNoncyclicInput) (hUD : GGBstarDeltaUnitaryInput)
    (hU : GGBstarInputOn (GGTableBRest3 GGTableBUnitaryLabel))
    (hO : GGBstarInputOn (GGTableBRest3 GGTableBOrthLabel))
    (hX : GGBstarInputOn (GGTableBRest3 GGTableBOtherLabel)) : GGBstarInput :=
  ggBstarInput_of_cover ((((ggBstarInputOn_done3 ha₀ hUD).or hU).or hO).or hX)
    fun p lab _ _ => ggTableB_rest3_cover p lab

theorem ggStdSubPreInput_of_round3 (ha₀ : GGLNoncyclicInput)
    (hEUd : GGEndNodeAdmUnitaryDvdInput) (hEUs : GGEndNodeAdmUnitarySmallInput)
    (hU : GGStdSubPreInputOn (GGTableBRest3 GGTableBUnitaryLabel))
    (hO : GGStdSubPreInputOn (GGTableBRest3 GGTableBOrthLabel))
    (hX : GGStdSubPreInputOn (GGTableBRest3 GGTableBOtherLabel)) : GGStdSubPreInput :=
  ggStdSubPreInput_of_cover ((((ggStdSubPreInputOn_done3 ha₀ hEUd hEUs).or hU).or hO).or hX)
    fun p lab _ _ => ggTableB_rest3_cover p lab

end Unitary

@[expose] def GGStdSubTwoTorusSpInput : Prop :=
  ∀ (l n p : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → p.Prime → p ≠ 2 →
    p ∣ 2 ^ n - 1 → 3 ≤ l →
      GGStdSubTwoTorus p l (LargeEvenProj (LargeEvenSpGroup K l))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l))

@[expose] def GGStdSubSmallRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGTypeASplitLabel p lab ∧ ¬ GGTableBSympLabel p lab

theorem ggStdSubSmallInput_of_round3 (hsp : GGStdSubTwoTorusSpInput)
    (hrest : GGStdSubSmallInputOn GGStdSubSmallRestLabel) : GGStdSubSmallInput :=
  ggStdSubSmallInput_of_cover ((ggStdSubSmallInputOn_typeA_split_holds.or
    (ggStdSubSmallInputOn_symplectic_of_sp hsp)).or hrest) fun p lab _ _ => by
      by_cases h1 : GGTypeASplitLabel p lab
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : GGTableBSympLabel p lab
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨h1, h2⟩

theorem ggTableBCxInput_of_rest (h : GGTableBCxInputOn GGCorFourTwoRestLabel) :
    GGTableBCxInput :=
  ggTableBCxInput_of_on (S := fun p lab => GGTypeALabel p lab ∨ GGCorFourTwoRestLabel p lab)
    (fun p lab _ _ => em (GGTypeALabel p lab)) (ggTableBCxInputOn_typeA.or h)

theorem ggTableBModuleInput_of_rest (h : GGTableBModuleInputOn GGCorFourTwoRestLabel) :
    GGTableBModuleInput :=
  ggTableBModuleInput_of_on (S := fun p lab => GGTypeALabel p lab ∨ GGCorFourTwoRestLabel p lab)
    (fun p lab _ _ => em (GGTypeALabel p lab)) (ggTableBModuleInputOn_typeA.or h)

theorem ggTableBActionInput_of_rest (h : GGTableBActionInputOn GGCorFourTwoRestLabel) :
    GGTableBActionInput :=
  ggTableBActionInput_of_on (S := fun p lab => GGTypeALabel p lab ∨ GGCorFourTwoRestLabel p lab)
    (fun p lab _ _ => em (GGTypeALabel p lab)) (ggTableBActionInputOn_typeA.or h)

end CFSG.StandardType
