module

public import CFSG.LocalAnalysis.StandardType.GGKOnlyE6Normalization

public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrConj

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrth

public import CFSG.LocalAnalysis.StandardType.GGReflExtE6

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6ConsumerK

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport

public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer

public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbrBasic

public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

public import CFSG.LocalAnalysis.StandardType.GGResExact2KReverse

public import CFSG.LocalAnalysis.StandardType.GGDepAConfig

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb

public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds

public import CFSG.LocalAnalysis.StandardType.GGResUnitaryExactTwo

public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGResE6DepFieldK
public import CFSG.LocalAnalysis.StandardType.GGResE6DepFieldL
public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabelEq
public import CFSG.LocalAnalysis.StandardType.GGResSchurDvd
public import CFSG.LocalAnalysis.StandardType.GGResE6DepJ
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResE6DepLabelInput_of_inputs
    (hT1 : GGTBE6OrderInput) (hT2 : GGE6DepJInput)
    (hTP : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G), GGNbrTablePConfig p B Bs x L D J)
    (hI3 : GGNbrSubcomponentInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) :
    GGResE6DepLabelInput := by
  intro G _ _ p B Bs x L D J y K hH _ hS
  have hT3 : GGSchurDvdInput := ggSchurDvdInput_holds
  obtain ⟨labL, labK, hL2, hK2, hL, hK, hlL, hlK⟩ := ggResE6Dep_labels hT1 hH hS
  obtain ⟨labJ, hJ2, hJ, hlJ⟩ := hT2 G p B Bs x L D J y K hH hS
  have h1 : labK.n = labJ.n :=
    ggResE6Dep_K_field (hTP G p B Bs x L D J) hI3 hRig hT3 hH hJ2 hK2 hJ hK hlJ hlK
  have h2 : labL.n = labJ.n := ggResE6Dep_L_field hTCJ hRig hT3 hH hL2 hJ2 hL hJ hlL hlJ
  have hEq : labK = labL := ggResE6Dep_label_eq hK2 hL2 hK hL (h1.trans h2.symm)
  subst hEq
  refine ⟨labK, hK, ?_, ?_⟩
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1)
      (ggInnerDiagOn_relabel hRig hH.2.2.1.1 hL2 hlL)
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1)
      (ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hK2 hlK)

theorem ggResE6DepLabelInput_of_b36
    (hTP : GGNbrTablePNbrInputOnL GGRegimeB36L) (hLB : GGLBalanceInput) :
    GGResE6DepLabelInput := by
  intro G _ _ p B Bs x L D J y K hH _ hS
  have hp3 : p = 3 := hS.1
  subst hp3
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hLMark : LargeEvenMarking L (fun lab _ _ _ _ _ => GGE6DepLabel lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) (hS.e6_marking hH (Or.inl rfl))
  have hKMark : LargeEvenMarking K (fun lab _ _ _ _ _ => GGE6DepLabel lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) (hS.e6_marking hH (Or.inr rfl))
  obtain ⟨labL, hLΛ, hlL, _, _, _, _, _, hL⟩ := largeEvenMarking_exists_hasLabel hLMark
  obtain ⟨labK, hKΛ, hlK, _, _, _, _, _, hK⟩ := largeEvenMarking_exists_hasLabel hKMark
  have hmL : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1)
      (ggInnerDiagOn_relabel hRig hH.2.2.1.1 hLΛ hlL)
  obtain ⟨hlJ, _, hJp⟩ := hS.j_label hH hL hmL
  have hJΛ : LargeEvenInLambda2 (ggTPJLabel labL) := by
    rcases hL with ⟨ht, _⟩ | ⟨ht, _⟩ <;>
      simp [ggTPJLabel, ht, LargeEvenInLambda2] <;> exact hLΛ.1
  have hJA : GGA5Label (ggTPJLabel labL) := by
    rcases hL with ⟨ht, hdiv⟩ | ⟨ht, hdiv⟩
    · simp [ggTPJLabel, ht, GGA5Label, hdiv]
    · simp [ggTPJLabel, ht, GGA5Label, hdiv]
  have hreg : GGRegimeB36L 3 (Nat.card Bs) labL (ggTPJLabel labL) labK :=
    ⟨rfl, hS.2.1, by rcases hL with h | h; exact Or.inl h.1; exact Or.inr h.1⟩
  have hrow := hTP G 3 B Bs x L D J y K hH.1 hH.2.2.1.1
    (hH.2.2.1.2 y K hH.2.2.2.2.1) hH.2.2.2.2.1
    labL (ggTPJLabel labL) labK hLΛ hJΛ hKΛ hreg hlL hlJ hlK
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hJp hH.2.2.2.2.1
  have hfield : labK.n = (ggTPJLabel labL).n :=
    ggResE6Dep_K_field_of_tablePRow hRig ggSchurDvdInput_holds hH
      hJΛ hKΛ hJA hK hlJ hlK hJK hrow
  have hfield' : labK.n = labL.n := by
    simpa [ggTPJLabel, apply_ite] using hfield
  have hEq : labK = labL := ggResE6Dep_label_eq hKΛ hLΛ hK hL hfield'
  subst hEq
  refine ⟨labK, hK, hmL, ?_⟩
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1)
    (ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hKΛ hlK)

section Certs


private theorem not_tablePRow_twA4_E6_narrow {X : LargeEvenLabel}
    (hX : GGE6DepLabel X) :
    ¬ GGTablePRow 3 (⟨.twA, 4, 1⟩ : LargeEvenLabel) X := by
  rcases X with ⟨tag, rank, n⟩
  rcases hX with ⟨ht, hdiv⟩ | ⟨ht, hdiv⟩ <;> subst ht <;> simp [GGTablePRow]

private theorem GGLabelIso.eq_of_twA4_narrow {lab : LargeEvenLabel}
    (h : GGLabelIso (⟨.twA, 4, 1⟩ : LargeEvenLabel) lab) :
    lab = ⟨.twA, 4, 1⟩ := by
  rcases h with rfl | hBC | hD3 | hA3 | htwD3 | htwA3 | hD2 | hA1
  all_goals simp_all

private theorem GGLabelIso.eq_of_E6_narrow {lab lab' : LargeEvenLabel}
    (h : GGLabelIso lab lab') (hl : GGE6DepLabel lab) : lab' = lab := by
  rcases hl with ⟨ht, -⟩ | ⟨ht, -⟩
  · rcases h with rfl | hBC | hD3 | hA3 | htwD3 | htwA3 | hD2 | hA1
    · rfl
    · rcases hBC with ⟨hbc, -⟩; rw [ht] at hbc; simp at hbc
    · rw [hD3.1] at ht; simp at ht
    · rw [hA3.1] at ht; simp at ht
    · rw [htwD3.1] at ht; simp at ht
    · rw [htwA3.1] at ht; simp at ht
    · rw [hD2.1] at ht; simp at ht
    · rw [hA1.2] at ht; simp at ht
  · rcases h with rfl | hBC | hD3 | hA3 | htwD3 | htwA3 | hD2 | hA1
    · rfl
    · rcases hBC with ⟨hbc, -⟩; rw [ht] at hbc; simp at hbc
    · rw [hD3.1] at ht; simp at ht
    · rw [hA3.1] at ht; simp at ht
    · rw [htwD3.1] at ht; simp at ht
    · rw [htwA3.1] at ht; simp at ht
    · rw [hD2.1] at ht; simp at ht
    · rw [hA1.2] at ht; simp at ht

private theorem tablePRow_twA4_candidates {X : LargeEvenLabel}
    (h : GGTablePRow 3 (⟨.twA, 4, 1⟩ : LargeEvenLabel) X) :
    X = (⟨.twA, 5, 1⟩ : LargeEvenLabel) ∨ X = (⟨.C, 5, 1⟩ : LargeEvenLabel) ∨
      X = (⟨.twD, 5, 1⟩ : LargeEvenLabel) ∨ X = (⟨.twD, 6, 1⟩ : LargeEvenLabel) := by
  simp [GGTablePRow] at h
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases h with ⟨hodd, -⟩; norm_num at hodd
  · rcases h with ⟨hodd, -⟩; norm_num at hodd
  · exact Or.inr (Or.inr (Or.inl h.2))
  · exact Or.inr (Or.inr (Or.inr h.2))

theorem exists_K_E6Label_of_endpoint_facts
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK)
    (e : Fin 6 ≃ Idx)
    (he : ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j)
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpairK : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hφ : ∀ i, φ i ∈ ggAutomizer K Bs) :
    ∃ labK : LargeEvenLabel, GGE6DepLabel labK ∧ LargeEvenInLambda2 labK ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMK : MK = CoxeterMatrix.E₆.reindex e :=
    ggIntCartan_E6_coxeter_reindex hCKK e he
  have hE6 : GGIsTypeE6 MK := ⟨e, hMK⟩
  have hcardK : Nat.card ↥(ggAutomizer K Bs) = 51840 :=
    card_ggAutomizer_of_typeE6 hE6 fK
  have h5 : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
      3 ^ 5 ≤ Nat.card ↥(ggGamma K hN).range := by
    intro hN
    exact five_le_card_range_of_e6_datum hN ι φ h α hCKK hE6 hlin hpairK hφ
  have hMarkK : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs K :=
    GGResHyp.e6_marking_of_endpoint_facts hH (Or.inr rfl) hcardBs h5 hcardK
  obtain ⟨labK, hK2, hlK, R, _, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hMarkK
  exact ⟨labK, hP.1, hK2, hlK⟩

theorem narrowK_labels_of_row
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (hres : GGTwE6ExactTwoPSU5Residual Bs L J)
    (hcardBs : Nat.card Bs = 3 ^ 6) :
    ∃ labK : LargeEvenLabel, LargeEvenInLambda2 labK ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) ∧
      (labK = (⟨.twA, 5, 1⟩ : LargeEvenLabel) ∨
        labK = (⟨.C, 5, 1⟩ : LargeEvenLabel) ∨
        labK = (⟨.twD, 5, 1⟩ : LargeEvenLabel) ∨
        labK = (⟨.twD, 6, 1⟩ : LargeEvenLabel)) := by
  obtain ⟨labL, labJ, hlabL, hlabJ, hL2, hlL, hMarkL, hJ2, hlJ, hMarkJ⟩ := hres
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨labK0, hK02, hlK0, R, _, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hInnK
  have hR : GGRegimeB36L 3 (Nat.card Bs) labL labJ labK0 := by
    refine ⟨rfl, hcardBs, ?_⟩
    rw [hlabL]
    exact Or.inr rfl
  obtain ⟨labJ', labK', hJ2', hK2', hrow, hlJ', hlK'⟩ :=
    hB36 G 3 B Bs x L D J y K hH.1 hH.2.2.1.1 hInnK hnb
      labL labJ labK0 hL2 hJ2 hK02 hR hlL hlJ hlK0
  have hisoJ : GGLabelIso (⟨.twA, 4, 1⟩ : LargeEvenLabel) labJ' := by
    simpa [hlabJ] using ggLabelRigidInput_holds _ _ _ hJ2 hJ2' hlJ hlJ'
  have hJeq : labJ' = (⟨.twA, 4, 1⟩ : LargeEvenLabel) :=
    GGLabelIso.eq_of_twA4_narrow hisoJ
  rw [hJeq] at hrow
  exact ⟨labK', hK2', hlK', tablePRow_twA4_candidates hrow⟩

theorem narrow_tableP_excludes_twA4_twE6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (hres : GGTwE6ExactTwoPSU5Residual Bs L J)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK)
    (e : Fin 6 ≃ Idx)
    (he : ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j)
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpairK : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hφ : ∀ i, φ i ∈ ggAutomizer K Bs) :
    False := by
  obtain ⟨labK, hKE6, hK2, hlK⟩ :=
    exists_K_E6Label_of_endpoint_facts hH hcardBs hCKK e he fK ι φ h α hlin hpairK hφ
  obtain ⟨labL, labJ, hlabL, hlabJ, hL2, hlL, hMarkL, hJ2, hlJ, hMarkJ⟩ := hres
  have hR : GGRegimeB36L 3 (Nat.card Bs) labL labJ labK := by
    refine ⟨rfl, hcardBs, ?_⟩
    rw [hlabL]
    exact Or.inr rfl
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hrow := hB36 G 3 B Bs x L D J y K hH.1 hH.2.2.1.1
    (hH.2.2.1.2 y K hnb) hnb labL labJ labK hL2 hJ2 hK2 hR hlL hlJ hlK
  obtain ⟨labJ', labK', hJ2', hK2', hrow, hlJ', hlK'⟩ := hrow
  have hisoJ : GGLabelIso (⟨.twA, 4, 1⟩ : LargeEvenLabel) labJ' := by
    simpa [hlabJ] using ggLabelRigidInput_holds _ _ _ hJ2 hJ2' hlJ hlJ'
  have hJeq : labJ' = ⟨.twA, 4, 1⟩ := GGLabelIso.eq_of_twA4_narrow hisoJ
  have hisoK : GGLabelIso labK labK' :=
    ggLabelRigidInput_holds _ _ _ hK2 hK2' hlK hlK'
  have hKeq : labK' = labK := GGLabelIso.eq_of_E6_narrow hisoK hKE6
  rw [hJeq, hKeq] at hrow
  exact not_tablePRow_twA4_E6_narrow hKE6 hrow



theorem GGResHyp.false_of_twE6_K_E6_exact2_card_six
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (hMarkL : GGInnerDiagOnLabel
      (fun _ lab => GGE6DepLabel lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hnoRowL : ¬ GGResRowAt ggRowTwoNode 3 J L)
    (hcardBs : Nat.card Bs = 3 ^ 6) : False := by
  classical
  have hres : GGTwE6ExactTwoPSU5Residual Bs L J :=
    hH.twE6_exactTwo_either_classification hMarkL (Or.inr hD) hnoRowL
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, hE6, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  obtain ⟨e, he⟩ := hE6
  have hCLstd : ∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j :=
    ggIntCartan_E6_entries_of_type hCL e he
  have hφmem : ∀ i, φ (Sum.inl i) ∈ ggAutomizer K Bs := by
    intro i
    rw [hclosL]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  exact narrow_tableP_excludes_twA4_twE6 hH hB36 hres hcardBs hCL e hCLstd fL ι
    (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    (fun i v => hlin (Sum.inl i) v) hpair hφmem


end Certs

section Certs


theorem actual_K_card_of_torRow
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {lab0 : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab0)
    (hHas : GGHasLabel lab0 (↥K ⧸ Subgroup.center ↥K))
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hrow : GGTBTorRowAt 3 lab0 r m N C M)
    {P : ∀ (_r _m N : ℕ), Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop}
    (hP : P r m N C M) :
    ∃ (r' m' N' : ℕ) (C' : Matrix (Fin N') (Fin N') ℤ)
      (M' : CoxeterMatrix (Fin N')),
      P r' m' N' C' M' ∧ Nat.card ↥(ggAutomizer K Bs) = Nat.card M'.Group := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hmark0 := ggInnerDiagOn_relabel ggLabelRigidInput_holds
    (hH.2.2.1.2 y K hnb) hΛ hHas
  have hKrow : GGInnerDiagOnLabel
      (fun _ lab => ∃ r m N C M, GGTBTorRowAt 3 lab r m N C M ∧ P r m N C M) 3 Bs K := by
    refine largeEvenMarking_mono ?_ hmark0
    intro lab R _ I F θ hQ
    exact ⟨by rw [hQ.1]; exact ⟨r, m, N, C, M, hrow, hP⟩, hQ.2⟩
  exact GGResHyp.exists_row_card_automizer_K (P := P)
    (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds hH hKrow

theorem actual_K_card_C5
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hΛ : LargeEvenInLambda2 (⟨.C, 5, 1⟩ : LargeEvenLabel))
    (hHas : GGHasLabel (⟨.C, 5, 1⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K)) :
    Nat.card ↥(ggAutomizer K Bs) = 3840 := by
  have hrow : GGTBTorRowAt 3 (⟨.C, 5, 1⟩ : LargeEvenLabel)
      (5 - ggTorEnn 3 (⟨.C, 5, 1⟩ : LargeEvenLabel))
      (ggTorMpm 3 (⟨.C, 5, 1⟩ : LargeEvenLabel)) 5
      (CartanMatrix.C 5) (CoxeterMatrix.B 5) :=
    GGTBTorRowAt.c (Or.inr rfl) (by norm_num)
  obtain ⟨r', m', N', C', M', hP, hcard⟩ := actual_K_card_of_torRow hH hΛ hHas hrow
    (P := fun _ _ _ _ M => Nat.card M.Group = 3840) (by
      rw [ggCoxeterB_card 5 (by norm_num)]
      norm_num [Nat.factorial])
  rw [hcard]
  exact hP

theorem actual_K_card_twD5
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hΛ : LargeEvenInLambda2 (⟨.twD, 5, 1⟩ : LargeEvenLabel))
    (hHas : GGHasLabel (⟨.twD, 5, 1⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K)) :
    Nat.card ↥(ggAutomizer K Bs) = 1920 := by
  have hrow : GGTBTorRowAt 3 (⟨.twD, 5, 1⟩ : LargeEvenLabel)
      (5 - ggTorEnn 3 (⟨.twD, 5, 1⟩ : LargeEvenLabel))
      (ggTorMpm 3 (⟨.twD, 5, 1⟩ : LargeEvenLabel)) 5
      (CartanMatrix.D 5) (ggCoxeterMatrixD 5) :=
    GGTBTorRowAt.d (Or.inr ⟨rfl, by norm_num, by norm_num⟩)
  obtain ⟨r', m', N', C', M', hP, hcard⟩ := actual_K_card_of_torRow hH hΛ hHas hrow
    (P := fun _ _ _ _ M => Nat.card M.Group = 1920) (by
      rw [OrthF3.card_coxeterD_eq 5 (by norm_num)]
      norm_num [Nat.factorial])
  rw [hcard]
  exact hP

theorem actual_K_card_twD6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hΛ : LargeEvenInLambda2 (⟨.twD, 6, 1⟩ : LargeEvenLabel))
    (hHas : GGHasLabel (⟨.twD, 6, 1⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K)) :
    Nat.card ↥(ggAutomizer K Bs) = 3840 := by
  have hrow : GGTBTorRowAt 3 (⟨.twD, 6, 1⟩ : LargeEvenLabel)
      (6 - 1) (ggTorMpm 3 (⟨.twD, 6, 1⟩ : LargeEvenLabel)) 5
      (CartanMatrix.B 5) (CoxeterMatrix.B 5) :=
    GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩)
  obtain ⟨r', m', N', C', M', hP, hcard⟩ := actual_K_card_of_torRow hH hΛ hHas hrow
    (P := fun _ _ _ _ M => Nat.card M.Group = 3840) (by
      rw [ggCoxeterB_card 5 (by norm_num)]
      norm_num [Nat.factorial])
  rw [hcard]
  exact hP


end Certs

section Certs



theorem GGResHyp.twE6_exactTwo_K_five_of_card_six
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (hMarkL : GGInnerDiagOnLabel
      (fun _ lab => GGE6DepLabel lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6)
    (hnoRowL : ¬ GGResRowAt ggRowTwoNode 3 J L)
    (hno3K : ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny)
    (hcardBs : Nat.card Bs = 3 ^ 6) :
    GGResLeviDatumExact2 3 Bs L J K ggSelAny
      (fun {Λ} {Λ'} ML MK => ggTypLE6 ML MK ∧ Nat.card Λ' = 5) := by
  classical
  have hres : GGTwE6ExactTwoPSU5Residual Bs L J :=
    hH.twE6_exactTwo_either_classification hMarkL (Or.inl hD) hnoRowL
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ, hAa, hCases, hBs, hE6⟩ :=
    hH.twE6_exactTwo_K_refinement hMarkL hD hnoRowL hno3K
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  have hNot6 : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) ≠ 6 := by
    intro h6
    obtain ⟨e, he⟩ := hE6 hcardBs h6
    obtain ⟨fK, hfK⟩ := hfKx
    have hφmem : ∀ i : {i : Λ // i ∉ S} ⊕ Λa,
        φ (i.map Subtype.val id) ∈ ggAutomizer K Bs := by
      intro i
      rw [hclosK]
      apply Subgroup.subset_closure
      cases i with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    exact narrow_tableP_excludes_twA4_twE6 hH hB36 hres hcardBs hCKK e he fK ι
      (fun i => φ (i.map Subtype.val id)) (fun i => h (i.map Subtype.val id))
      (fun i => α (i.map Subtype.val id))
      (fun i v => hlin (i.map Subtype.val id) v) hpairK hφmem
  have h5 : Nat.card ({i : Λ // i ∉ S} ⊕ Λa) = 5 := by
    rw [Nat.card_eq_fintype_card]
    rcases hCases with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · simpa using (Fintype.card_congr e).symm
    · simpa using (Fintype.card_congr e).symm
    · simpa using (Fintype.card_congr e).symm
    · exact False.elim (hNot6 (by simpa using (Fintype.card_congr e).symm))
    · exact False.elim (hNot6 (by simpa using (Fintype.card_congr e).symm))
    · exact False.elim (hNot6 (by simpa using (Fintype.card_congr e).symm))
    · exact False.elim (hNot6 (by simpa using (Fintype.card_congr e).symm))
  exact ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, ⟨htyp, h5⟩,
    hlin, hrefl, hpairL, hpairK, hsel, hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩



open CFSG CFSG.StandardType.Line63.H5

theorem actual_K_card_twA5
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel)) 3 Bs K)
    (hLB : GGLBalanceInput) :
    Nat.card ↥(ggAutomizer K Bs) = 720 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpJ : 3 ∣ Nat.card J := hH.prime_dvd_card_J
  obtain ⟨lab0, hlab0, hhas0, _R0, _instR0, _I0, _F0, _θ0, hP0⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hlab5 : LargeEvenInLambda2 (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
    simpa [hP0.1] using hlab0
  have hhas5 : GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K) := by
    simpa [hP0.1] using hhas0
  obtain ⟨_, _, _, hKperf⟩ := hH.data_K
  obtain ⟨_, lab, hlab, hraw⟩ := hM
  obtain ⟨R₁, _instR₁, _I₁, _F₁, _hs₁, _hna₁, _θ₁, hP₁⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₁
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  have hF : Nat.card F = 4 := by simpa using hFK
  have : CharP F 2 := charP_two_of_card (by simpa using hF : Nat.card F = 2 ^ 2)
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN', hBsI⟩ := hP
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hBs3 : IsElemAbelian 3 Bs := by
    simpa using hH.1.tableB_facts.2.1
  have hInn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hInn.le_normalizer
  have hγcard : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range := by
    exact four_le_card_ggGamma_of_unitary_six_side hRig hLB hH (Or.inr rfl)
      hpq hhas5 hlab5 hpJ hN
  obtain ⟨hNbar, φ, hMφ, hdiagφ⟩ :=
    exists_diagonal_cover_of_unitary_six_two_red hF hKperf θ hN' hBs3 hBsI hγcard
  let Xbar : Subgroup (RedGrp K) := (redMkL K).range
  let Bbar : Subgroup (RedGrp K) := (redMkB hN).range
  obtain ⟨_VK, _hVKadd, _hVKmod, _ιK, _ρK, _φK, _hK, _αK, _hNP,
    _hρK, _hφK, _hlinK, _hreflK, _hpairK, ⟨eKbar, _heKbar⟩, _hclosK⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (f := 1) (r := 5)
      (Bs := Bbar) (X := Xbar)
      (by simpa using hF) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num : 3 ≤ 5) (isElemAbelian_redB hN hBs3)
      (redSC hN hBs3 (by simpa using hH.1.2.1.2.2.2)) hNbar hMφ hdiagφ
  let eB : ↥Bs ≃* ↥Bbar := MonoidHom.ofInjective (redMkB_injective hN hBs3)
  have hKrange : Xbar =
      (K.subgroupOf (Subgroup.normalizer (K : Set G))).map (redMk K) := by
    dsimp only [Xbar, redMkL]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hmap : ggAutomizer Xbar Bbar =
      (ggAutomizer K Bs).map (MulAut.congr eB).toMonoidHom := by
    rw [hKrange]
    exact ggAutomizer_redMk_eq (X := K) (Bs := Bs) (H := K) hBs3 hN
      Subgroup.le_normalizer hN
  let eMap := Subgroup.equivMapOfInjective (ggAutomizer K Bs)
    (MulAut.congr eB).toMonoidHom (MulAut.congr eB).injective
  let eAut : ↥(ggAutomizer K Bs) ≃* ↥(ggAutomizer Xbar Bbar) :=
    eMap.trans (MulEquiv.subgroupCongr hmap.symm)
  have hcard : Nat.card ↥(ggAutomizer K Bs) = Nat.card (CoxeterMatrix.A 5).Group := by
    calc
      Nat.card ↥(ggAutomizer K Bs) = Nat.card ↥(ggAutomizer Xbar Bbar) :=
        Nat.card_congr eAut.toEquiv
      _ = Nat.card (CoxeterMatrix.A 5).Group :=
        (Nat.card_congr eKbar.toEquiv).symm
  rw [hcard, l05nK3a_card_coxeterA 5]
  norm_num [Nat.factorial]

theorem actual_K_K5_label_order_cases
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (hres : GGTwE6ExactTwoPSU5Residual Bs L J)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hLB : GGLBalanceInput) :
    ∃ labK : LargeEvenLabel,
      LargeEvenInLambda2 labK ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) ∧
      ((labK = (⟨.twA, 5, 1⟩ : LargeEvenLabel) ∧
        Nat.card ↥(ggAutomizer K Bs) = 720) ∨
      (labK = (⟨.C, 5, 1⟩ : LargeEvenLabel) ∧
        Nat.card ↥(ggAutomizer K Bs) = 3840) ∨
      (labK = (⟨.twD, 5, 1⟩ : LargeEvenLabel) ∧
        Nat.card ↥(ggAutomizer K Bs) = 1920) ∨
      (labK = (⟨.twD, 6, 1⟩ : LargeEvenLabel) ∧
        Nat.card ↥(ggAutomizer K Bs) = 3840)) := by
  obtain ⟨labK, hK2, hlK, hcases⟩ :=
    narrowK_labels_of_row hH hB36 hres hcardBs
  refine ⟨labK, hK2, hlK, ?_⟩
  rcases hcases with rfl | rfl | rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
    have hM : GGInnerDiagOnLabel
        (fun _ lab => lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel)) 3 Bs K := by
      unfold GGInnerDiagOnLabel
      refine largeEvenMarking_mono ?_
        (ggInnerDiagOn_relabel ggLabelRigidInput_holds
          (hH.2.2.1.2 y K hnb) hK2 hlK)
      intro lab R _ I F θ hP
      exact ⟨hP.1, hP.2⟩
    exact actual_K_card_twA5 hH ggLabelRigidInput_holds hM hLB
  · right; left
    exact ⟨rfl, actual_K_card_C5 hH hK2 hlK⟩
  · right; right; left
    exact ⟨rfl, actual_K_card_twD5 hH hK2 hlK⟩
  · right; right; right
    exact ⟨rfl, actual_K_card_twD6 hH hK2 hlK⟩

end Certs

open Module Matrix

theorem kOnlyE6_alpha_y_zero
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod 3) V}
    (hφ : ∀ j w, ggLin (p := 3) ι (φ j) w = w - α j w • h j)
    (hL : ∀ i j : Λ, α i (h j) = (CK i j : ZMod 3))
    (hCK : GGIntCartan MK CK)
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ∀ j : Λ, α j (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 := by
  intro j
  have hfix := ggRC_automizer_fixes_y hy hH.2.2.2.2.1.1.2.2.2.1
  have hmem : φ j ∈ ggAutomizer K Bs := by
    rw [hAK]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hlin_fix : ggLin (p := 3) ι (φ j) (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
      ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) :=
    (ggLin_fix_iff (p := 3) ι (φ j) ⟨y, hy⟩).mp (hfix (φ j) hmem)
  have h1 := hφ j (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)))
  rw [hlin_fix] at h1
  have h2 : α j (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) • h j = 0 :=
    sub_eq_self.mp h1.symm
  have h3 : α j (α j (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) • h j) = 0 := by
    rw [h2, map_zero]
  have hpair : α j (h j) = (2 : ZMod 3) := by
    rw [hL j j, hCK.1 j]
    norm_num
  rw [map_smul, smul_eq_mul, hpair] at h3
  exact (mul_eq_zero.mp h3).resolve_right (zmod_two_ne_zero (p := 3) (by norm_num))


open CFSG.Assembly


theorem kOnlyE6_actual_d5_two_models
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hTBF : GGTBFixInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny))
    (hy : y ∈ Bs)
    {Λ Λa : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs}
    {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpair : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hCL : GGIntCartan ML CL) (htyp : GGIsTypeE6 ML)
    (hclosK : ggAutomizer K Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e) :
    (∃ c : Fin 5 → ZMod 3,
      h (Sum.inl (e 0)) = ∑ i : Fin 5, c i • h (Sum.inl (e (Fin.succ i)))) ∨
      (∃ (y' : V) (c : Fin 5 → ZMod 3),
        y' ≠ 0 ∧
          (∀ i : Fin 6, α (Sum.inl (e i)) y' = 0) ∧
          h (Sum.inl (e 0)) = y' + ∑ i : Fin 5, c i • h (Sum.inl (e (Fin.succ i)))) := by
  classical
  let h' : Fin 6 → V := fun i => h (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let yV : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  have hpair' : ∀ i j : Fin 6,
      α' i (h' j) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML]
  have hy1 : y ≠ 1 := (hH.data_K).2.1
  have hyV : yV ≠ 0 := by
    intro h0
    have h0' : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = 0 := by simpa [yV] using h0
    have h2 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 :=
      ι.injective (h0'.trans (map_zero ι).symm)
    have h1 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      simpa using (Additive.ofMul.injective h2)
    exact hy1 (congrArg (fun z : ↥Bs => (z : G)) h1)
  have hker : ∀ i : Fin 6, α' i yV = 0 := by
    intro i
    exact kOnlyE6_alpha_y_zero (hH := hH) (hy := hy) (ι := ι)
      (φ := fun j : Λ => φ (Sum.inl j))
      (h := fun j : Λ => h (Sum.inl j))
      (α := fun j : Λ => α (Sum.inl j))
      (fun j w => hlin (Sum.inl j) w) (fun i j => hpair i j) hCL hclosK (e i)
  have hcard : Nat.card Bs = 3 ^ 6 :=
    GGResHyp.card_Bs_six_of_K_only_E6 hH hTBF hD hno
  have hVcard : Nat.card V = 3 ^ 6 := by
    rw [← Nat.card_congr ι.toEquiv, Nat.card_congr Additive.toMul, hcard]
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hVpow : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V))
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hpow : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 6 := hVpow.symm.trans hVcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have hmodels := d5_two_models (h := h') (α := α') (y := yV) hpair' hyV hker hdim
  simpa only [h', α', d5Index] using hmodels



def d5Coeff : Fin 5 → ZMod 3 := ![0, 1, 0, 2, 1]

theorem d5Coeff_spec :
    ∀ j : Fin 5,
      ∑ i : Fin 5, d5Coeff i *
        (CartanMatrix.E 6 (d5Index j) (d5Index i) : ZMod 3) =
        (CartanMatrix.E 6 (d5Index j) 0 : ZMod 3) := by
  intro j
  fin_cases j <;> decide +kernel

theorem d5Coeff_spec0 :
    ∑ i : Fin 5, d5Coeff i * (CartanMatrix.E 6 0 (d5Index i) : ZMod 3) =
      (CartanMatrix.E 6 0 0 : ZMod 3) := by
  decide +kernel

theorem d5_coeff_unique {c : Fin 5 → ZMod 3}
    (hc : ∀ j : Fin 5,
      ∑ i : Fin 5, c i *
        (CartanMatrix.E 6 (d5Index j) (d5Index i) : ZMod 3) =
        (CartanMatrix.E 6 (d5Index j) 0 : ZMod 3)) :
    c = d5Coeff := by
  have hc' : ∀ j : Fin 5,
      ∑ i : Fin 5, (CartanMatrix.E 6 (d5Index j) (d5Index i) : ZMod 3) * c i =
        (CartanMatrix.E 6 (d5Index j) 0 : ZMod 3) := by
    intro j
    simpa only [mul_comm] using hc j
  have hcoeff' : ∀ j : Fin 5,
      ∑ i : Fin 5, (CartanMatrix.E 6 (d5Index j) (d5Index i) : ZMod 3) * d5Coeff i =
        (CartanMatrix.E 6 (d5Index j) 0 : ZMod 3) := by
    intro j
    simpa only [mul_comm] using d5Coeff_spec j
  have hzero : d5Cartan3 *ᵥ (c - d5Coeff) = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.zero_apply,
      d5Cartan3, d5Cartan, mul_sub, Finset.sum_sub_distrib]
    rw [hc' j, hcoeff' j, sub_self]
  have hd0 : c - d5Coeff = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero d5Cartan3_det_ne_zero hzero
  exact sub_eq_zero.mp hd0

def modelRoot (t : ZMod 3) (c : Fin 5 → ZMod 3) :
    Fin 6 → (Option (Fin 5) → ZMod 3) :=
  Fin.cases (t • Pi.single none (1 : ZMod 3) +
      ∑ i : Fin 5, c i • Pi.single (some i) 1)
    (fun i => Pi.single (some i) 1)

def modelAlpha (i : Fin 6) :
    Module.Dual (ZMod 3) (Option (Fin 5) → ZMod 3) where
  toFun v := ∑ j : Fin 5, v (some j) *
    (CartanMatrix.E 6 i (d5Index j) : ZMod 3)
  map_add' v w := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    congr 1
    ext j
    ring_nf

theorem d5_coordinates
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {y : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hy : y ≠ 0) (hker : ∀ i, α i y = 0)
    (hdim : Module.finrank (ZMod 3) V = 6) :
    ∃ (t : ZMod 3) (b : Basis (Option (Fin 5)) (ZMod 3) V),
      b none = (if t = 0 then y else t • y) ∧
      (∀ i : Fin 5, b (some i) = h (d5Index i)) ∧
      (∀ i : Fin 6, b.equivFun (h i) =
        modelRoot (if t = 0 then 0 else 1) d5Coeff i) ∧
      (∀ i : Fin 6, ∀ v : V, α i v = modelAlpha i (b.equivFun v)) := by
  classical
  obtain ⟨c, t, hdec⟩ := d5_decomposition hpair hy hker hdim
  have hc : c = d5Coeff := by
    apply d5_coeff_unique
    intro j
    exact d5_decomposition_cartan hpair hker hdec j
  rw [hc] at hdec
  let tn : ZMod 3 := if t = 0 then 0 else 1
  let y0 : V := if t = 0 then y else t • y
  have hy0 : y0 ≠ 0 := by
    by_cases ht : t = 0
    · simp [y0, ht, hy]
    · simp only [y0, ht, if_false]
      exact smul_ne_zero ht hy
  have hker0 : ∀ i, α i y0 = 0 := by
    intro i
    by_cases ht : t = 0
    · simp [y0, ht, hker i]
    · simp only [y0, ht, if_false, map_smul, hker i, smul_zero]
  have hLI : LinearIndependent (ZMod 3) (fun o : Option (Fin 5) =>
      o.casesOn' y0 (fun i => h (d5Index i))) :=
    d5_axis_linearIndependent hpair hy0 hker0
  let b : Basis (Option (Fin 5)) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank hLI (by
      simp only [Fintype.card_option, Fintype.card_fin]
      omega)
  have hb : ⇑b = fun o : Option (Fin 5) =>
      o.casesOn' y0 (fun i => h (d5Index i)) :=
    coe_basisOfLinearIndependentOfCardEqFinrank hLI _
  have hb_none : b none = y0 := by
    simpa using congrFun hb none
  have hb_some : ∀ i : Fin 5, b (some i) = h (d5Index i) := by
    intro i
    simpa using congrFun hb (some i)
  have hb_self : ∀ o : Option (Fin 5), b.equivFun (b o) = Pi.single o 1 := by
    intro o
    funext j
    rw [b.equivFun_self]
    by_cases hoj : o = j
    · simp [hoj]
    · simp [hoj]
  have h0_eq : h 0 = tn • y0 + ∑ i : Fin 5, d5Coeff i • h (d5Index i) := by
    by_cases ht : t = 0
    · simp [tn, y0, ht, hdec]
    · simp [tn, y0, ht, hdec]
  have hroot0 : b.equivFun (h 0) = modelRoot tn d5Coeff 0 := by
    rw [h0_eq]
    simp only [map_add, map_smul, map_sum, ← hb_none, ← hb_some, hb_self]
    rfl
  have hroot_succ : ∀ i : Fin 5,
      b.equivFun (h (d5Index i)) = modelRoot tn d5Coeff (Fin.succ i) := by
    intro i
    rw [← hb_some i, hb_self]
    rfl
  have hroot : ∀ i : Fin 6, b.equivFun (h i) = modelRoot tn d5Coeff i := by
    intro i
    exact Fin.cases hroot0 (fun j => hroot_succ j) i
  have hα_none : ∀ i : Fin 6, α i (b none) = 0 := by
    intro i
    rw [hb_none]
    exact hker0 i
  have hα_some : ∀ i : Fin 6, ∀ j : Fin 5,
      α i (b (some j)) = (CartanMatrix.E 6 i (d5Index j) : ZMod 3) := by
    intro i j
    rw [hb_some]
    exact hpair i (d5Index j)
  have hα : ∀ i : Fin 6, ∀ v : V, α i v = modelAlpha i (b.equivFun v) := by
    intro i v
    calc
      α i v = α i (∑ o : Option (Fin 5), b.equivFun v o • b o) := by
        rw [b.sum_equivFun]
      _ = ∑ o : Option (Fin 5), b.equivFun v o * α i (b o) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = modelAlpha i (b.equivFun v) := by
        rw [Fintype.sum_option]
        simp only [hα_none i, mul_zero, zero_add, hα_some i]
        rfl
  refine ⟨t, b, hb_none, hb_some, ?_, hα⟩
  intro i
  simpa [tn] using hroot i

theorem kOnlyE6_actual_d5_coordinates
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hTBF : GGTBFixInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny))
    (hy : y ∈ Bs)
    {Λ Λa : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs}
    {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpair : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hCL : GGIntCartan ML CL) (htyp : GGIsTypeE6 ML)
    (hclosK : ggAutomizer K Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e) :
    ∃ (t : ZMod 3) (b : Basis (Option (Fin 5)) (ZMod 3) V),
      b none = (if t = 0 then ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
        else t • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) ∧
      (∀ i : Fin 5, b (some i) = h (Sum.inl (e (d5Index i)))) ∧
      (∀ i : Fin 6, b.equivFun (h (Sum.inl (e i))) =
        modelRoot (if t = 0 then 0 else 1) d5Coeff i) ∧
      (∀ i : Fin 6, ∀ v : V,
        α (Sum.inl (e i)) v = modelAlpha i (b.equivFun v)) := by
  classical
  let h' : Fin 6 → V := fun i => h (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let yV : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  have hpair' : ∀ i j : Fin 6,
      α' i (h' j) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML]
  have hyV : yV ≠ 0 := by
    intro h0
    have h0' : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = 0 := by simpa [yV] using h0
    have h2 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 :=
      ι.injective (h0'.trans (map_zero ι).symm)
    have h1 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      simpa using (Additive.ofMul.injective h2)
    exact (hH.data_K).2.1 (congrArg (fun z : ↥Bs => (z : G)) h1)
  have hker : ∀ i : Fin 6, α' i yV = 0 := by
    intro i
    exact kOnlyE6_alpha_y_zero (hH := hH) (hy := hy) (ι := ι)
      (φ := fun j : Λ => φ (Sum.inl j))
      (h := fun j : Λ => h (Sum.inl j))
      (α := fun j : Λ => α (Sum.inl j))
      (fun j w => hlin (Sum.inl j) w) (fun i j => hpair i j) hCL hclosK (e i)
  have hcard : Nat.card Bs = 3 ^ 6 :=
    GGResHyp.card_Bs_six_of_K_only_E6 hH hTBF hD hno
  have hVcard : Nat.card V = 3 ^ 6 := by
    rw [← Nat.card_congr ι.toEquiv, Nat.card_congr Additive.toMul, hcard]
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hVpow : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V))
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hpow : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 6 := hVpow.symm.trans hVcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  simpa only [h', α', yV] using
    (d5_coordinates (h := h') (α := α') (y := yV) hpair' hyV hker hdim)

theorem oneNode_attachment_coordinates
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Basis (Option (Fin 5)) (ZMod 3) V) (tn : ZMod 3) (c : Fin 5 → ZMod 3)
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {a : V}
    {β : Module.Dual (ZMod 3) V} {J : Finset (Fin 6)} {κ κ' : Fin 6 → ZMod 3}
    (hroot : ∀ i : Fin 6, b.equivFun (h i) = modelRoot tn c i)
    (hα : ∀ i : Fin 6, ∀ v : V, α i v = modelAlpha i (b.equivFun v))
    (hcrossβ : ∀ j ∈ J, β (h j) = κ j)
    (hcrossα : ∀ j ∈ J, α j a = κ' j)
    (hself : β a = 2) :
    ∃ (w f : Option (Fin 5) → ZMod 3) (a₀ b₀ : ZMod 3),
      b.equivFun a = w ∧
      (∀ v : V, β v = ∑ o : Option (Fin 5), f o * b.equivFun v o) ∧
      w none = a₀ ∧ f none = b₀ ∧
      (∀ j ∈ J, ∑ o : Option (Fin 5), f o * modelRoot tn c j o = κ j) ∧
      (∀ j ∈ J, modelAlpha j w = κ' j) ∧
      (∑ o : Option (Fin 5), f o * w o = 2) := by
  classical
  let w : Option (Fin 5) → ZMod 3 := b.equivFun a
  let β' : Module.Dual (ZMod 3) (Option (Fin 5) → ZMod 3) :=
    β.comp (b.equivFun.symm : (Option (Fin 5) → ZMod 3) →ₗ[ZMod 3] V)
  let f : Option (Fin 5) → ZMod 3 := fun o => β' (Pi.single o 1)
  have hf : ∀ v : V, β v = ∑ o : Option (Fin 5), f o * b.equivFun v o := by
    intro v
    have hv : b.equivFun v =
        ∑ o : Option (Fin 5), b.equivFun v o • Pi.single o (1 : ZMod 3) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    calc β v = β' (b.equivFun v) := by simp [β']
      _ = β' (∑ o : Option (Fin 5), b.equivFun v o • Pi.single o 1) := congrArg β' hv
      _ = ∑ o : Option (Fin 5), b.equivFun v o * f o := by
        simp only [map_sum, map_smul, smul_eq_mul, f]
      _ = ∑ o : Option (Fin 5), f o * b.equivFun v o := by
        simp only [mul_comm]
  refine ⟨w, f, w none, f none, rfl, hf, rfl, rfl, ?_, ?_, ?_⟩
  · intro j hj
    rw [← hcrossβ j hj, hf (h j), hroot j]
  · intro j hj
    rw [← hcrossα j hj, hα j a]
  · rw [← hself, hf a]

theorem kOnlyE6_actual_attachment_coordinates
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hTBF : GGTBFixInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny))
    (hy : y ∈ Bs)
    {Λ Λa : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λa] [DecidableEq Λa]
    {S : Finset Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs}
    {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpair : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hCL : GGIntCartan ML CL) (htyp : GGIsTypeE6 ML)
    (hCK : GGIntCartan MK CK)
    (hclosK : ggAutomizer K Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e)
    (a₀ : Λa) :
    ∃ (t : ZMod 3) (b : Basis (Option (Fin 5)) (ZMod 3) V)
      (w f : Option (Fin 5) → ZMod 3) (rootAxis dualAxis : ZMod 3),
      b none = (if t = 0 then ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
        else t • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) ∧
      (∀ i : Fin 5, b (some i) = h (Sum.inl (e (d5Index i)))) ∧
      (∀ i : Fin 6, b.equivFun (h (Sum.inl (e i))) =
        modelRoot (if t = 0 then 0 else 1) d5Coeff i) ∧
      (∀ i : Fin 6, ∀ v : V,
        α (Sum.inl (e i)) v = modelAlpha i (b.equivFun v)) ∧
      b.equivFun (h (Sum.inr a₀)) = w ∧
      (∀ v : V, α (Sum.inr a₀) v =
        ∑ o : Option (Fin 5), f o * b.equivFun v o) ∧
      w none = rootAxis ∧ f none = dualAxis ∧
      (∀ i : Fin 6, (hi : e i ∉ S) →
        ∑ o : Option (Fin 5), f o *
          modelRoot (if t = 0 then 0 else 1) d5Coeff i o =
            (CK (Sum.inr a₀) (Sum.inl ⟨e i, hi⟩) : ZMod 3)) ∧
      (∀ i : Fin 6, (hi : e i ∉ S) →
        modelAlpha i w =
          (CK (Sum.inl ⟨e i, hi⟩) (Sum.inr a₀) : ZMod 3)) ∧
      (∑ o : Option (Fin 5), f o * w o = 2) := by
  classical
  obtain ⟨t, b, hb, hsome, hroot, hα⟩ :=
    kOnlyE6_actual_d5_coordinates hH hTBF hD hno hy hlin hpair hCL htyp hclosK e hML
  let h' : Fin 6 → V := fun i => h (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let Jset : Finset (Fin 6) := Finset.univ.filter (fun i => e i ∉ S)
  let κ : Fin 6 → ZMod 3 := fun i =>
    if h : e i ∉ S then (CK (Sum.inr a₀) (Sum.inl ⟨e i, h⟩) : ZMod 3) else 0
  let κ' : Fin 6 → ZMod 3 := fun i =>
    if h : e i ∉ S then (CK (Sum.inl ⟨e i, h⟩) (Sum.inr a₀) : ZMod 3) else 0
  have hcrossβ : ∀ j ∈ Jset, α (Sum.inr a₀) (h' j) = κ j := by
    intro j hj
    have hj' : e j ∉ S := (Finset.mem_filter.mp hj).2
    simp only [h', κ, hj', dif_pos]
    exact hpairK (Sum.inr a₀) (Sum.inl ⟨e j, hj'⟩)
  have hcrossα : ∀ j ∈ Jset, α' j (h (Sum.inr a₀)) = κ' j := by
    intro j hj
    have hj' : e j ∉ S := (Finset.mem_filter.mp hj).2
    simp only [α', κ', hj', dif_pos]
    exact hpairK (Sum.inl ⟨e j, hj'⟩) (Sum.inr a₀)
  have hself : α (Sum.inr a₀) (h (Sum.inr a₀)) = 2 := by
    have hdiag : (CK (Sum.inr a₀) (Sum.inr a₀) : ZMod 3) = 2 := by
      rw [hCK.1 (Sum.inr a₀)]
      norm_num
    exact (hpairK (Sum.inr a₀) (Sum.inr a₀)).trans hdiag
  have hres := oneNode_attachment_coordinates (b := b)
    (tn := (if t = 0 then 0 else 1)) (c := d5Coeff)
    (h := h') (α := α') (a := h (Sum.inr a₀)) (β := α (Sum.inr a₀))
    (J := Jset) (κ := κ) (κ' := κ') hroot hα hcrossβ hcrossα hself
  obtain ⟨w, f, rootAxis, dualAxis, hw, hf, hw0, hf0, hcrossβ', hcrossα', hself'⟩ := hres
  refine ⟨t, b, w, f, rootAxis, dualAxis, hb, hsome, hroot, hα,
    hw, hf, hw0, hf0, ?_, ?_, hself'⟩
  · intro i hi
    have hi' : e i ∉ S := hi
    have hmem : i ∈ Jset := by simp [Jset, hi]
    have h := hcrossβ' i hmem
    simpa only [κ, dif_pos hi'] using h
  · intro i hi
    have hi' : e i ∉ S := hi
    have hmem : i ∈ Jset := by simp [Jset, hi]
    have h := hcrossα' i hmem
    simpa only [κ', dif_pos hi'] using h

section ActualKOnlyE6Containment

variable {G : Type} [Group G] [Finite G]

theorem card_ggAutomizer_dvd {H Bs : Subgroup G} :
    Nat.card (ggAutomizer H Bs) ∣ Nat.card H := by
  classical
  let N : Subgroup G := H ⊓ Subgroup.normalizer (Bs : Set G)
  let f : ↥N →* ↥(ggAutomizer H Bs) :=
    { toFun := fun g => ⟨ggConjAut Bs g.2.2, ggConjAut_mem_ggAutomizer g.2.1 g.2.2⟩
      map_one' := by
        ext b
        simp [ggConjAut_apply]
      map_mul' := by
        intro a b
        ext c
        simp [ggConjAut_apply, mul_assoc] }
  have hsurj : Function.Surjective f := by
    intro φ
    obtain ⟨g, hgH, hgN, hgapp⟩ := mem_ggAutomizer_iff.mp φ.2
    refine ⟨⟨g, ⟨hgH, hgN⟩⟩, ?_⟩
    ext b
    change ((ggConjAut Bs hgN b : ↥Bs) : G) = ((φ.1 b : ↥Bs) : G)
    rw [ggConjAut_apply, hgapp]
  have hdvdN : Nat.card ↥(ggAutomizer H Bs) ∣ Nat.card ↥N :=
    Subgroup.card_dvd_of_surjective (f := f) hsurj
  exact hdvdN.trans (Subgroup.card_dvd_of_le (inf_le_left : N ≤ H))

theorem GGResHyp.J_le_K_of_K_exact2_E6
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hLB : GGLBalanceInput) :
    J ≤ K := by
  have hcard := ggResLeviDatumExact2_E6_automizerJ_card hD
  have hdiv : 3 ∣ Nat.card J := by
    have hdvd := card_ggAutomizer_dvd (H := J) (Bs := Bs)
    rcases hcard with h | h
    · rw [h] at hdvd
      exact (by norm_num : 3 ∣ 120).trans hdvd
    · rw [h] at hdvd
      exact (by norm_num : 3 ∣ 192).trans hdvd
  exact le_of_ggNbr hLB hH.1.1 hH.1.2.2 hdiv hH.2.2.2.2.1

theorem GGResHyp.J_le_K_inf_centralizer_x_of_K_exact2_E6
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hLB : GGLBalanceInput) :
    J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) := by
  refine le_inf (hH.J_le_K_of_K_exact2_E6 hD hLB) ?_
  intro j hj
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp
      (hH.1.D_le_inf_centralizer (hH.1.2.2.1.2.2.2.1)).2 j hj)

theorem GGResHyp.AJ_le_fixed_x_centralizer_of_K_exact2_E6
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hLB : GGLBalanceInput) :
    ggAutomizer J Bs ≤ ggAutomizer (K ⊓ Subgroup.centralizer ({x} : Set G)) Bs :=
  ggAutomizer_mono Bs (hH.J_le_K_inf_centralizer_x_of_K_exact2_E6 hD hLB)

theorem GGResHyp.K_only_E6_Bs_six_and_fixed_x_containment
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hTBF : GGTBFixInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny))
    (hLB : GGLBalanceInput) :
    Nat.card Bs = 3 ^ 6 ∧ J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) ∧
      ggAutomizer J Bs ≤ ggAutomizer (K ⊓ Subgroup.centralizer ({x} : Set G)) Bs := by
  have hcardBs := hH.card_Bs_six_of_K_only_E6 hTBF hD hno
  have hJ : J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) :=
    hH.J_le_K_inf_centralizer_x_of_K_exact2_E6 hD hLB
  exact ⟨hcardBs, hJ, ggAutomizer_mono Bs hJ⟩




end ActualKOnlyE6Containment

theorem kOnlyE6_iOne
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hTBF : GGTBFixInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact ggResLeviDatumExact2_E6_iOne_of_card_six hH (hH.card_Bs_six_of_K_only_E6 hTBF hD hno) hD

theorem kOnlyE6_reverse_card_one
    {G : Type} [Group G] {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)) :
    GGResLeviDatumCard 1 3 Bs L J K ggSelAny ggTypAny := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have hΛa1 : Nat.card Λa = 1 := by
    by_contra hne
    have h2 : 2 ≤ Nat.card Λa := by omega
    have hrev := ggResLeviDatumCard_reverse_of_witness (p := 3) (Bs := Bs) (L := K) (J := J)
      (K := L) (S := S) (Λa := Λa) (ML := ML) (CL := CL) (MK := MK) (CK := CK)
      (V := V) (ι := ι) (φ := φ) (h := h) (α := α) (by omega) (by omega)
      hML hCL hMK hCK hlin hrefl hpair hpairK ⟨fL, hfL⟩ ⟨fK, hfK⟩ hclosL hclosK hconn hclosJ
    have hc : Nat.card Λa = 2 ∨ Nat.card Λa = 3 := by omega
    rcases hc with hc | hc
    · exact hno (Or.inl (by simpa only [hc] using hrev))
    · exact hno (Or.inr (by simpa only [hc] using hrev))
  have hrev := ggResLeviDatumCard_reverse_of_witness (p := 3) (Bs := Bs) (L := K) (J := J)
    (K := L) (S := S) (Λa := Λa) (ML := ML) (CL := CL) (MK := MK) (CK := CK)
    (V := V) (ι := ι) (φ := φ) (h := h) (α := α) (by omega) (by omega)
    hML hCL hMK hCK hlin hrefl hpair hpairK ⟨fL, hfL⟩ ⟨fK, hfK⟩ hclosL hclosK hconn hclosJ
  simpa only [hΛa1] using hrev

theorem GGResHyp.K_only_E6_actual_component_and_I1
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hTBF : GGTBFixInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny))
    (hLB : GGLBalanceInput) :
    Nat.card Bs = 3 ^ 6 ∧
      Bs ⊓ Subgroup.centralizer (J : Set G) = D ∧
      IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) ∧
      ggAutomizer J Bs ≤ ggAutomizer (K ⊓ Subgroup.centralizer ({x} : Set G)) Bs := by
  obtain ⟨hcard, hJ, hAJ⟩ := hH.K_only_E6_Bs_six_and_fixed_x_containment hTBF hD hno hLB
  have hSStar : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
  have hComponent := isComponentOf_inf_centralizer_of_ggNbr hSStar hH.1.2.2
    hH.2.2.2.2.1 (hJ.trans inf_le_left)
  exact ⟨hcard, ggResLeviDatumExact2_E6_iOne_of_card_six hH hcard hD, hComponent, hAJ⟩

section AschbacherKOnlyIndependentContext

variable {G : Type} [Group G] [Finite G]

theorem GGResHyp.K_only_E6_independent_join
    {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hOrbK : GGResCentBoundNbrInput)
    (hBs : Nat.card ↥Bs ≤ 3 ^ 7)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ}
    {CK : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hMK : MK = CoxeterMatrix.E₆.reindex e) (hCK : GGIntCartan MK CK)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  subst hp3
  have hAll : LR6E6All := lr6E6All_of_certificate
  have hAKcard : Nat.card ↥(ggAutomizer K Bs) = 51840 :=
    ggE6K_card_AK e hMK fK
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hbound : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
      3 ^ 7 * (6 * (3 - 1) * 51840) :=
    ggE6K_card_join_le hOrbK rfl hH hy hBs hAKcard
  exact ggTwoNodeIndepAtK_e6 hAll hFix hFixK rfl hH hBs hLrefl hbound
    e hMK hCK hφ hpair hAK hind

end AschbacherKOnlyIndependentContext

theorem GGResHyp.K_only_E6_exact2_join_or_dependent
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hOrbK : GGResCentBoundNbrInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelDep ggTypLE6 := by
  classical
  have hBs6 := hH.card_Bs_six_of_K_only_E6 hFix hD hno
  have hBs7 : Nat.card Bs ≤ 3 ^ 7 := by rw [hBs6]; norm_num
  have hLrefl : GGReflGenerated 3 (ggAutomizer L Bs) :=
    GGResXDatum.reflGenerated (GGResLeviDatumCard.xDatum_right hD)
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, hE6, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fK, hfK⟩, hfL, hclosK, hclosL, hconn, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  by_cases hind : LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i))
  · obtain ⟨e, he⟩ := hE6
    exact Or.inl (hH.K_only_E6_independent_join rfl hFix hFixK hOrbK hBs7 hLrefl
      e he hCL (fun i w => hlin (Sum.inl i) w) hpair fK hclosK hind)
  · exact Or.inr ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hA1, hA3, hML, hCL, hMK, hCK, hE6, hlin, hrefl, hpair, hpairK,
      hind, ⟨fK, hfK⟩, hfL, hclosK, hclosL, hconn, hclosJ⟩


end CFSG.StandardType
