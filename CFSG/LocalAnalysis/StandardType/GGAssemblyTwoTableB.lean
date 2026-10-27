module

public import CFSG.LocalAnalysis.StandardType.GGStdSubExist
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplectic
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeADvd
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGBstarInputOn.or {S T : ℕ → LargeEvenLabel → Prop} (hS : GGBstarInputOn S)
    (hT : GGBstarInputOn T) : GGBstarInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B x L hI hM
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hST, -⟩ := largeEvenRawDatum_exists hraw
  rcases hST with h | h
  · exact hS G p B x L hI ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩
  · exact hT G p B x L hI ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩

theorem GGStdSubPreInputOn.or {S T : ℕ → LargeEvenLabel → Prop} (hS : GGStdSubPreInputOn S)
    (hT : GGStdSubPreInputOn T) : GGStdSubPreInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B x L hI hM
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hST, -⟩ := largeEvenRawDatum_exists hraw
  rcases hST with h | h
  · exact hS G p B x L hI ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩
  · exact hT G p B x L hI ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩

theorem ggBstarInput_of_cover {S : ℕ → LargeEvenLabel → Prop} (hS : GGBstarInputOn S)
    (hcov : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab) :
    GGBstarInput := by
  intro G _ _ p B x L hT
  obtain ⟨hperf, lab, hlab, hraw⟩ := hT.2.2.2.2.2.2.2.1
  exact hS G p B x L hT ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hcov p lab hlab hP.1, hP⟩) hraw⟩

theorem ggStdSubPreInput_of_cover {S : ℕ → LargeEvenLabel → Prop} (hS : GGStdSubPreInputOn S)
    (hcov : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab) :
    GGStdSubPreInput := by
  intro G _ _ p B x L hT
  obtain ⟨hperf, lab, hlab, hraw⟩ := hT.2.2.2.2.2.2.2.1
  exact hS G p B x L hT ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hcov p lab hlab hP.1, hP⟩) hraw⟩

@[expose] def GGTableBSympLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1

theorem ggBstarInputOn_symplectic : GGBstarInputOn GGTableBSympLabel :=
  ggBstarInputOn_of_labels
    (fun _ _ h => h.1.elim (fun h' => Or.inr (Or.inl h')) fun h' => Or.inr (Or.inr (Or.inl h')))
    fun _ _ hp hlab h => (largeEvenLabelAll_tableB_symplectic h.1 hlab hp h.2).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_symplectic : GGStdSubPreInputOn GGTableBSympLabel :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_symplectic h.1 hlab hp h.2).mono
      fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

@[expose] def GGTableBProvedLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTypeASplitLabel p lab ∨ GGTableBSympLabel p lab

@[expose] def GGTableBRest (F : LargeEvenLabel → Prop) (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  F lab ∧ ¬ GGTableBProvedLabel p lab

@[expose] def GGTableBLinearLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ lab.rank = 3)

@[expose] def GGTableBUnitaryLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)

@[expose] def GGTableBOrthLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∧ lab.rank ≠ 3) ∨ (lab.tag = .twD ∧ lab.rank ≠ 3)

@[expose] def GGTableBOtherLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag ≠ .A ∧ lab.tag ≠ .twA ∧ lab.tag ≠ .B ∧ lab.tag ≠ .C ∧ lab.tag ≠ .D ∧ lab.tag ≠ .twD

theorem ggTableB_family_cover (lab : LargeEvenLabel) :
    GGTableBLinearLabel lab ∨ GGTableBUnitaryLabel lab ∨ GGTableBOrthLabel lab ∨
      GGTableBOtherLabel lab := by
  obtain ⟨t, l, n⟩ := lab
  by_cases hl : l = 3 <;> cases t <;>
    simp [GGTableBLinearLabel, GGTableBUnitaryLabel, GGTableBOrthLabel, GGTableBOtherLabel, hl]

theorem ggTableB_rest_cover (p : ℕ) (lab : LargeEvenLabel) :
    ((((GGTypeASplitLabel p lab ∨ GGTableBSympLabel p lab) ∨
      GGTableBRest GGTableBLinearLabel p lab) ∨ GGTableBRest GGTableBUnitaryLabel p lab) ∨
        GGTableBRest GGTableBOrthLabel p lab) ∨ GGTableBRest GGTableBOtherLabel p lab := by
  by_cases hP : GGTableBProvedLabel p lab
  · exact Or.inl (Or.inl (Or.inl (Or.inl hP)))
  · rcases ggTableB_family_cover lab with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h, hP⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨h, hP⟩))
    · exact Or.inl (Or.inr ⟨h, hP⟩)
    · exact Or.inr ⟨h, hP⟩

theorem ggBstarInput_of_families (htor : GGPGLToralityInput)
    (hL : GGBstarInputOn (GGTableBRest GGTableBLinearLabel))
    (hU : GGBstarInputOn (GGTableBRest GGTableBUnitaryLabel))
    (hO : GGBstarInputOn (GGTableBRest GGTableBOrthLabel))
    (hX : GGBstarInputOn (GGTableBRest GGTableBOtherLabel)) : GGBstarInput :=
  ggBstarInput_of_cover
    (((((ggBstarInputOn_typeA_split htor).or ggBstarInputOn_symplectic).or hL).or hU).or hO |>.or
      hX)
    fun p lab _ _ => ggTableB_rest_cover p lab

theorem LargeEvenLabelAll.and {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (h : LargeEvenLabelAll lab P) (h' : LargeEvenLabelAll lab P') :
    LargeEvenLabelAll lab fun R _ I F => P R I F ∧ P' R I F := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ ⟨⟨hq, hp⟩, hp'⟩ => ⟨hq, hp, hp'⟩) (h' _ (h Q hQ))

theorem ggStdSubPreInputOn_of_labels_adm {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGEndNodeAdm p r R I) :
    GGStdSubPreInputOn S := by
  intro G _ _ p B x L hT hM
  have hnc := ha₀ G p B x L hT
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT
  have hp : p.Prime := hβ.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, r, hlift, hend⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hA, hAI, hr, h3'⟩ := ggGamma_range_props hp hS hβ.2.2.2 hL θ hBN h3 hlift
  have hadm := ggAdmissible_of_clauseFour hp hS hnc hBN hst.2.1
  obtain ⟨a, haA, ha1, hcomp, hcent⟩ := hend L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hL _ hA hAI hr h3' hadm
  exact exists_stdSubPre_of_endNode hp hS hBN haA ha1 hcomp hcent

@[expose] def GGTableBUnitaryLiftLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGTableBOrthPlusLiftLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTableBOrthMinusLiftLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGEndNodeAdmUnitaryInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
    GGTableBUnitaryLiftLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGEndNodeAdm p (ggUnitaryTorusRank p (lab.rank + 1)) R I

@[expose] def GGEndNodeAdmOrthPlusInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
    GGTableBOrthPlusLiftLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGEndNodeAdm p lab.rank R I

@[expose] def GGEndNodeAdmOrthMinusInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
    GGTableBOrthMinusLiftLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGEndNodeAdm p (lab.rank - 1) R I

theorem ggStdSubPreInputOn_orthPlusLift (ha₀ : GGLNoncyclicInput)
    (hE : GGEndNodeAdmOrthPlusInput) : GGStdSubPreInputOn GGTableBOrthPlusLiftLabel :=
  ggStdSubPreInputOn_of_labels_adm ha₀ fun p lab hp hlab h =>
    ((largeEvenLabelAll_torusLift_D h.1 hlab h.2.1 hp h.2.2).and (hE p lab hp hlab h)).mono
      fun _ _ _ _ hh => ⟨_, hh.1, hh.2⟩

theorem ggStdSubPreInputOn_orthMinusLift (ha₀ : GGLNoncyclicInput)
    (hE : GGEndNodeAdmOrthMinusInput) : GGStdSubPreInputOn GGTableBOrthMinusLiftLabel :=
  ggStdSubPreInputOn_of_labels_adm ha₀ fun p lab hp hlab h =>
    ((largeEvenLabelAll_torusLift_twD h.1 hlab h.2.1 hp h.2.2).and (hE p lab hp hlab h)).mono
      fun _ _ _ _ hh => ⟨_, hh.1, hh.2⟩

section Unitary

theorem ggStdSubPreInputOn_unitaryLift (ha₀ : GGLNoncyclicInput)
    (hE : GGEndNodeAdmUnitaryInput) : GGStdSubPreInputOn GGTableBUnitaryLiftLabel :=
  ggStdSubPreInputOn_of_labels_adm ha₀ fun p lab hp hlab h => by
    have hlift : LargeEvenLabelAll lab fun R _ _ _ =>
        GGTorusLift p (ggUnitaryTorusRank p (lab.rank + 1)) R := by
      rcases h.1 with ht | ⟨ht, hl⟩
      · exact largeEvenLabelAll_torusLift_twA hlab ht hp h.2
      · rw [hl]
        exact largeEvenLabelAll_torusLift_twD3 hlab ht hl hp h.2
    exact (hlift.and (hE p lab hp hlab h)).mono fun _ _ _ _ hh => ⟨_, hh.1, hh.2⟩

@[expose] def GGTableBProvedLabelB (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBProvedLabel p lab ∨ GGTableBUnitaryLiftLabel p lab ∨ GGTableBOrthPlusLiftLabel p lab ∨
    GGTableBOrthMinusLiftLabel p lab

@[expose] def GGTableBRestB (F : LargeEvenLabel → Prop) (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  F lab ∧ ¬ GGTableBProvedLabelB p lab

theorem ggStdSubPreInput_of_families (ha₀ : GGLNoncyclicInput) (htor : GGPGLToralityInput)
    (hEU : GGEndNodeAdmUnitaryInput) (hEOp : GGEndNodeAdmOrthPlusInput)
    (hEOm : GGEndNodeAdmOrthMinusInput)
    (hL : GGStdSubPreInputOn (GGTableBRestB GGTableBLinearLabel))
    (hU : GGStdSubPreInputOn (GGTableBRestB GGTableBUnitaryLabel))
    (hO : GGStdSubPreInputOn (GGTableBRestB GGTableBOrthLabel))
    (hX : GGStdSubPreInputOn (GGTableBRestB GGTableBOtherLabel)) : GGStdSubPreInput :=
  ggStdSubPreInput_of_cover
    ((((((((ggStdSubPreInputOn_typeA_split htor).or ggStdSubPreInputOn_symplectic).or
      (ggStdSubPreInputOn_unitaryLift ha₀ hEU)).or (ggStdSubPreInputOn_orthPlusLift ha₀ hEOp)).or
      (ggStdSubPreInputOn_orthMinusLift ha₀ hEOm)).or hL).or hU).or hO |>.or hX)
    fun p lab _ _ => by
      by_cases hP : GGTableBProvedLabelB p lab
      · rcases hP with h | h | h | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · rcases ggTableB_family_cover lab with h | h | h | h
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h, hP⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨h, hP⟩))
        · exact Or.inl (Or.inr ⟨h, hP⟩)
        · exact Or.inr ⟨h, hP⟩

end Unitary

end CFSG.StandardType
