module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_13
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_15_statement
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G)
    (R : G → Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  IsMinCE G →
    theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R →
      Subgroup.normalizer Achoice = M ∧
        Section2.hypothesis_2_2_statement Achoice M R ∧
        (∀ U W1 W2 : Subgroup G,
          notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2 →
            section8Hypothesis46Source M W1 W2 MF A A0 ∧
              section8Hypothesis46Source M W1 W2 Ms A A0) ∧
        (section8Hypothesis52Source M MF Ms A A0 A1 →
          (∃ U W1 W2 : Subgroup G,
            notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2) →
            section8InducedNonkernelFamily M Ms S →
              ∃ ν : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
                Section5.hypothesis_5_2_statement S ν)

/-- Peterfalvi `(8.16)`. -/


private theorem section8SemidirectProductIn_isInternalSemidirectProduct
    {G : Type u} [Group G]
    {C H K : Subgroup G}
    (h : section8SemidirectProductIn C H K) :
    Section2.IsInternalSemidirectProduct C H K := by
  classical
  rcases h with ⟨hcomp, hHnormal⟩
  rcases hcomp with ⟨hHC, hKC, hCeq, hdisj⟩
  rcases hHnormal with ⟨_hHC', hHnormal⟩
  have hsup_local : H.subgroupOf C ⊔ K.subgroupOf C = ⊤ := by
    calc
      H.subgroupOf C ⊔ K.subgroupOf C = (H ⊔ K).subgroupOf C := by
        symm
        exact Subgroup.subgroupOf_sup (A := H) (A' := K) (B := C) hHC hKC
      _ = ⊤ := by
        rw [← hCeq]
        simp
  refine
    { left_le := hHC
      right_le := hKC
      right_normalizes_left := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro k hk h0 hh0
    let kC : C := ⟨k, hKC hk⟩
    let hC : H.subgroupOf C := ⟨⟨h0, hHC hh0⟩, hh0⟩
    have hmem :
        kC * hC * kC⁻¹ ∈ H.subgroupOf C :=
      Subgroup.Normal.conj_mem hHnormal hC hC.property kC
    simpa [Section2.conjBy, kC, hC, Subgroup.mem_subgroupOf] using hmem
  · exact hdisj.eq_bot
  · intro c hc
    let cC : C := ⟨c, hc⟩
    have hcSup : cC ∈ H.subgroupOf C ⊔ K.subgroupOf C := by
      rw [hsup_local]
      simp
    rcases (Subgroup.mem_sup_of_normal_left
        (s := H.subgroupOf C) (t := K.subgroupOf C) (x := cC)).1 hcSup with
      ⟨hC, hhC, kC, hkC, hmul⟩
    refine ⟨(hC : G), ?_, (kC : G), ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hhC
    · simpa [Subgroup.mem_subgroupOf] using hkC
    · simpa [cC] using (congrArg Subtype.val hmul).symm

private theorem theorem_8_15_setNormalizer_eq_subgroupNormalizer
    {G : Type u} [Group G] (A : Set G) :
    Section2.setNormalizer A = Subgroup.normalizer A := by
  ext g
  simp [Section2.setNormalizer, Section2.normalizesSet, Section2.conjBy,
    Subgroup.normalizer, iff_comm]

private theorem theorem_8_15_section16_top_conjugate_of_section2
    {G : Type u} [Group G] {x y : G}
    (hxy : Section2.conjugateIn x y) :
    section16ConjugateInSubgroup (⊤ : Subgroup G) x y := by
  rcases hxy with ⟨g, hg⟩
  exact ⟨g, by simp, by simpa [Section2.conjBy] using hg.symm⟩

private theorem theorem_8_15_section2_conjugateInSubgroup_of_section16
    {G : Type u} [Group G] {M : Subgroup G} {x y : G}
    (hxy : section16ConjugateInSubgroup M x y) :
    Section2.conjugateInSubgroup M x y := by
  rcases hxy with ⟨g, hgM, hg⟩
  exact ⟨⟨g, hgM⟩, by simpa [Section2.conjBy] using hg.symm⟩

private theorem theorem_8_15_mem_source_X_ne_one
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G} {A A0 A1 X : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hX : X = A ∨ X = A0) :
    ∀ x : G, x ∈ X → x ≠ 1 := by
  classical
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hCases⟩
  have hA_ne_one : ∀ x : G, x ∈ A → x ≠ 1 := by
    intro x hxA
    rcases hCases with hTypeI | hTypeP
    · rcases hTypeI with ⟨_hTypeI, hA, _hA0⟩
      rw [hA, section8CentralizerUnion] at hxA
      rcases hxA with ⟨_z, _hz, hxCent⟩
      exact hxCent.2
    · rcases hTypeP with ⟨_U, _W1, _W2, _hP, _hSourceType, hA, _hA0, _hLate⟩
      rw [hA, section8CentralizerUnion] at hxA
      rcases hxA with ⟨_z, _hz, hxCent⟩
      exact hxCent.2
  have hA0_ne_one : ∀ x : G, x ∈ A0 → x ≠ 1 := by
    intro x hxA0
    rcases hCases with hTypeI | hTypeP
    · rcases hTypeI with ⟨_hTypeI, _hA, hA0⟩
      exact hA_ne_one x (by simpa [hA0] using hxA0)
    · rcases hTypeP with ⟨_U, W1, W2, _hP, _hSourceType, _hA, hA0, _hLate⟩
      rw [hA0] at hxA0
      rcases hxA0 with hxA | hxConj
      · exact hA_ne_one x hxA
      · rcases hxConj with ⟨w, hw, m, _hmM, hx_eq⟩
        intro hx_one
        have hmw_one : m * w * m⁻¹ = 1 := by
          simpa [hx_one] using hx_eq.symm
        have hw_one : w = 1 := by
          have h := congrArg (fun z : G => m⁻¹ * z * m) hmw_one
          simpa [mul_assoc] using h
        exact hw.2 (Or.inl (by simp [hw_one]))
  intro x hx
  rcases hX with rfl | rfl
  · exact hA_ne_one x hx
  · exact hA0_ne_one x hx

private theorem theorem_8_15_mem_source_X_mem_M
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G} {A A0 A1 X : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hX : X = A ∨ X = A0) :
    ∀ x : G, x ∈ X → x ∈ M := by
  classical
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hCases⟩
  have hA_mem : ∀ x : G, x ∈ A → x ∈ M := by
    intro x hxA
    rcases hCases with hTypeI | hTypeP
    · rcases hTypeI with ⟨_hTypeI, hA, _hA0⟩
      rw [hA, section8CentralizerUnion] at hxA
      rcases hxA with ⟨_z, _hz, hxCent⟩
      exact hxCent.1.1
    · rcases hTypeP with ⟨_U, _W1, _W2, _hP, _hSourceType, hA, _hA0, _hLate⟩
      rw [hA, section8CentralizerUnion] at hxA
      rcases hxA with ⟨_z, _hz, hxCent⟩
      exact (section12_ambientDerivedSubgroup_le (G := G) (E := M)) hxCent.1.1
  have hA0_mem : ∀ x : G, x ∈ A0 → x ∈ M := by
    intro x hxA0
    rcases hCases with hTypeI | hTypeP
    · rcases hTypeI with ⟨_hTypeI, _hA, hA0⟩
      exact hA_mem x (by simpa [hA0] using hxA0)
    · rcases hTypeP with ⟨_U, W1, W2, hP, _hSourceType, _hA, hA0, _hLate⟩
      rw [hA0] at hxA0
      rcases hxA0 with hxA | hxConj
      · exact hA_mem x hxA
      · rcases hxConj with ⟨w, hw, m, hmM, rfl⟩
        rcases hP with
          ⟨hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
            _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
            hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
        have hW2M : W2 ≤ M := fun y hy => hMF.1.1 (hW2le hy).1
        have hWM : W1 ⊔ W2 ≤ M := sup_le hW1hall.1 hW2M
        exact M.mul_mem (M.mul_mem hmM (hWM hw.1)) (M.inv_mem hmM)
  intro x hx
  rcases hX with rfl | rfl
  · exact hA_mem x hx
  · exact hA0_mem x hx

private theorem theorem_8_15_exists_nonidentity_of_ne_bot
    {G : Type u} [Group G] {H : Subgroup G} (hH : H ≠ ⊥) :
    ∃ x : G, x ∈ H ∧ x ≠ 1 := by
  classical
  by_contra hnone
  apply hH
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · exact False.elim (hnone ⟨x, hx, hx1⟩)

private theorem theorem_8_15_typeP_MF_ne_bot
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    MF ≠ ⊥ := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, hW2ne, _hCent, _hHatW⟩
  intro hMFbot
  apply hW2ne
  rw [Subgroup.eq_bot_iff_forall]
  intro x hxW2
  have hxMF : x ∈ MF := (hW2le hxW2).1
  rw [hMFbot] at hxMF
  simpa using hxMF

private theorem theorem_8_15_typeP_derived_ne_bot_of_U
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) (hUne : U ≠ ⊥) :
    ambientDerivedSubgroup M ≠ ⊥ := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  intro hD
  apply hUne
  rw [Subgroup.eq_bot_iff_forall]
  intro x hxU
  have hxD : x ∈ ambientDerivedSubgroup M := hUleD hxU
  rw [hD] at hxD
  simpa using hxD

private theorem theorem_8_15_msChoiceSource_ne_bot
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hMs : msChoiceSource M MF Ms) :
    Ms ≠ ⊥ := by
  classical
  rcases hMs with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨hTypeI, _hnII, _hnIII, _hnIV, _hnV, hMs_eq⟩
    rcases hTypeI with ⟨U, U1, U0, hF, _hTypeIAlt⟩
    rcases hF with
      ⟨_hsolv, _hodd, _hMF, hMFpos, _hMFltM, _hUne, _hcomp,
        _hU1le, _hU1comm, _hU1norm, _hcent, _hU0le, _hexp, _hfrob⟩
    have hMFne : MF ≠ ⊥ := ne_of_gt hMFpos
    simpa [hMs_eq] using hMFne
  · rcases hII with ⟨_hnI, hTypeII, _hnIII, _hnIV, _hnV, hMs_eq⟩
    rcases hTypeII with ⟨U, W1, W2, U1, U0, hP, _hCond, _hUcomm, _hUnorm, _hF⟩
    have hMFne : MF ≠ ⊥ :=
      theorem_8_15_typeP_MF_ne_bot (G := G) (M := M) (U := U) (W1 := W1)
        (W2 := W2) hP
    simpa [hMs_eq] using hMFne
  · rcases hIII with ⟨_hnI, _hnII, hTypeIII, _hnIV, _hnV, hMs_eq⟩
    rcases hTypeIII with ⟨U, W1, W2, hP, hCond, _hUcomm, _hUnorm⟩
    have hDne : ambientDerivedSubgroup M ≠ ⊥ :=
      theorem_8_15_typeP_derived_ne_bot_of_U (G := G) (M := M) (MF := MF)
        (U := U) (W1 := W1) (W2 := W2) hP hCond.1
    simpa [hMs_eq] using hDne
  · rcases hIV with ⟨_hnI, _hnII, _hnIII, hTypeIV, _hnV, hMs_eq⟩
    rcases hTypeIV with ⟨U, W1, W2, hP, hCond, _hUncomm, _hUnorm⟩
    have hDne : ambientDerivedSubgroup M ≠ ⊥ :=
      theorem_8_15_typeP_derived_ne_bot_of_U (G := G) (M := M) (MF := MF)
        (U := U) (W1 := W1) (W2 := W2) hP hCond.1
    simpa [hMs_eq] using hDne
  · rcases hV with ⟨_hnI, _hnII, _hnIII, _hnIV, hTypeV, hMs_eq⟩
    rcases hTypeV with ⟨U, W1, W2, hP, _hUbot, _hAlt⟩
    have hMFne : MF ≠ ⊥ :=
      theorem_8_15_typeP_MF_ne_bot (G := G) (M := M) (U := U) (W1 := W1)
        (W2 := W2) hP
    simpa [hMs_eq] using hMFne

private theorem theorem_8_15_A1_nonempty
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1) :
    ∃ x : G, x ∈ A1 ∧ x ≠ 1 := by
  rcases hNotation with ⟨_hM, _hMF, hMs, hA1, _hCases⟩
  rcases theorem_8_15_exists_nonidentity_of_ne_bot
      (G := G) (H := Ms) (theorem_8_15_msChoiceSource_ne_bot hMs) with
    ⟨x, hxMs, hxne⟩
  exact ⟨x, by simpa [hA1, a1Set] using ⟨hxMs, hxne⟩, hxne⟩

private theorem theorem_8_15_choice_nonempty
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G}
    {R : G → Subgroup G}
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R) :
    ∃ x : G, x ∈ Achoice ∧ x ≠ 1 := by
  rcases hData with ⟨hNotation, h14, hChoice⟩
  rcases h14 with ⟨hA1subA, hAsubA0, _hD, _hRbot, _hUnique, _hReq,
    _htildeA, _htildeA0, _htildeA1⟩
  rcases theorem_8_15_A1_nonempty hNotation with ⟨x, hxA1, hxne⟩
  rcases hChoice with rfl | rfl | rfl
  · exact ⟨x, hAsubA0 (hA1subA hxA1), hxne⟩
  · exact ⟨x, hA1subA hxA1, hxne⟩
  · exact ⟨x, hxA1, hxne⟩

private theorem theorem_8_15_choice_subset_M
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G}
    {R : G → Subgroup G}
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R) :
    Achoice ⊆ M := by
  rcases hData with ⟨hNotation, h14, hChoice⟩
  rcases h14 with ⟨hA1subA, _hAsubA0, _hD, _hRbot, _hUnique, _hReq,
    _htildeA, _htildeA0, _htildeA1⟩
  have hA0_mem_M : ∀ x : G, x ∈ A0 → x ∈ M :=
    theorem_8_15_mem_source_X_mem_M hNotation (Or.inr rfl)
  have hA_mem_M : ∀ x : G, x ∈ A → x ∈ M :=
    theorem_8_15_mem_source_X_mem_M hNotation (Or.inl rfl)
  rcases hChoice with rfl | rfl | rfl
  · exact hA0_mem_M
  · exact hA_mem_M
  · intro x hx
    exact hA_mem_M x (hA1subA hx)

private theorem theorem_8_15_choice_subset_A0
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G} {A A0 A1 Achoice D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R) :
    Achoice ⊆ A0 := by
  rcases hData with ⟨_hNotation, h14, hChoice⟩
  rcases h14 with ⟨hA1subA, hAsubA0, _hD, _hRbot, _hUnique, _hReq,
    _htildeA, _htildeA0, _htildeA1⟩
  rcases hChoice with rfl | rfl | rfl
  · exact subset_rfl
  · exact hAsubA0
  · exact hA1subA.trans hAsubA0


private theorem theorem_8_15_trivial_semidirect_centralizer
    {G : Type u} [Group G] {M : Subgroup G} {x : G}
    (hcent_le_M : Section2.elementCentralizer x ≤ M) :
    Section2.IsInternalSemidirectProduct
      (Section2.elementCentralizer x) (⊥ : Subgroup G) (Section2.centralizerIn M x) where
  left_le := bot_le
  right_le := by
    intro y hy
    exact hy.2
  right_normalizes_left := by
    intro k hk h hh
    have hh1 : h = 1 := by simpa using hh
    subst h
    simp [Section2.conjBy]
  inf_eq_bot := by
    simp
  mul_surjective := by
    intro c hc
    refine ⟨1, by simp, c, ?_, by simp⟩
    exact ⟨hcent_le_M hc, hc⟩

public theorem theorem_8_15_support_of_mem_D
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G} {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hG : IsMinCE G)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (h14 : notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R)
    {x : G} (hxD : x ∈ D) :
    ∃ L LF : Subgroup G,
      supportConclusionDataSource M MF M A0 x L LF ∧ R x = elementCentralizerIn LF x := by
  classical
  letI : IsMinCE G := hG
  rcases h14 with ⟨_hA1subA, _hAsubA0, hD, _hRbot, hUnique, hReq,
    _htildeA, _htildeA0, _htildeA1⟩
  have hxD0 : x ∈ section8DSet M A0 := by
    simpa [hD] using hxD
  have h13A0 :=
    (theorem_8_13 (G := G) M MF Ms A A0 A1 A0) hG hNotation (Or.inr rfl)
  rcases hUnique x hxD with ⟨L, hLmem, _hLuniq⟩
  rcases h13A0.2.2.2 x hxD0 L hLmem with ⟨LF, hSupp⟩
  refine ⟨L, LF, hSupp, ?_⟩
  rcases hSupp with ⟨_hLmax, hLF, hContain, _hSemiL, _hSemiC, _hcop, _htype⟩
  exact hReq x hxD L LF hContain hLF

private theorem theorem_8_15_centralizer_semidirect
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G} {A A0 A1 Achoice D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hG : IsMinCE G)
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R)
    {x : G} (hx : x ∈ Achoice) :
    Section2.IsInternalSemidirectProduct
      (Section2.elementCentralizer x) (R x) (Section2.centralizerIn M x) := by
  classical
  rcases hData with ⟨hNotation, h14, _hChoice⟩
  rcases h14 with ⟨_hA1subA, _hAsubA0, hD, hRbot, _hUnique, _hReq,
    _htildeA, _htildeA0, _htildeA1⟩
  have hxA0 : x ∈ A0 :=
    theorem_8_15_choice_subset_A0
      (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0) (A1 := A1)
      (Achoice := Achoice) (D := D) (tildeA := tildeA) (tildeA0 := tildeA0)
      (tildeA1 := tildeA1) (R := R) ⟨hNotation, by
        exact ⟨_hA1subA, _hAsubA0, hD, hRbot, _hUnique, _hReq,
          _htildeA, _htildeA0, _htildeA1⟩, _hChoice⟩ hx
  by_cases hxD : x ∈ D
  · rcases theorem_8_15_support_of_mem_D
      (G := G) (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0) (A1 := A1)
      (D := D) (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (R := R) hG hNotation
      ⟨_hA1subA, _hAsubA0, hD, hRbot, _hUnique, _hReq,
        _htildeA, _htildeA0, _htildeA1⟩ hxD with
      ⟨L, LF, hSupp, hReqx⟩
    rcases hSupp with ⟨_hLmax, _hLF, _hContain, _hSemiL, hSemiC, _hcop, _htype⟩
    have hSemi := section8SemidirectProductIn_isInternalSemidirectProduct hSemiC
    simpa [hReqx, Section2.elementCentralizer, Section2.centralizerIn, elementCentralizerIn]
      using hSemi
  · have hxNotD : x ∈ A0 \ D := ⟨hxA0, hxD⟩
    have hR : R x = ⊥ := hRbot x hxNotD
    have hcent_le_M : Section2.elementCentralizer x ≤ M := by
      intro y hy
      by_contra hyM
      exact hxD (by
        rw [hD]
        exact ⟨hxA0, fun hle => hyM (hle hy)⟩)
    have hSemi := theorem_8_15_trivial_semidirect_centralizer
      (G := G) (M := M) (x := x) hcent_le_M
    simpa [hR] using hSemi

private theorem theorem_8_15_coprime_orders
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G} {A A0 A1 Achoice D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hG : IsMinCE G)
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R)
    {x y : G} (hx : x ∈ Achoice) (hy : y ∈ Achoice) :
    Nat.Coprime (Nat.card (R x)) (Nat.card (Section2.centralizerIn M y)) := by
  classical
  rcases hData with ⟨hNotation, h14, hChoice⟩
  rcases h14 with ⟨_hA1subA, _hAsubA0, hD, hRbot, _hUnique, _hReq,
    _htildeA, _htildeA0, _htildeA1⟩
  have hxA0 : x ∈ A0 :=
    theorem_8_15_choice_subset_A0
      (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0) (A1 := A1)
      (Achoice := Achoice) (D := D) (tildeA := tildeA) (tildeA0 := tildeA0)
      (tildeA1 := tildeA1) (R := R) ⟨hNotation, by
        exact ⟨_hA1subA, _hAsubA0, hD, hRbot, _hUnique, _hReq,
          _htildeA, _htildeA0, _htildeA1⟩, hChoice⟩ hx
  have hyA0 : y ∈ A0 :=
    theorem_8_15_choice_subset_A0
      (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0) (A1 := A1)
      (Achoice := Achoice) (D := D) (tildeA := tildeA) (tildeA0 := tildeA0)
      (tildeA1 := tildeA1) (R := R) ⟨hNotation, by
        exact ⟨_hA1subA, _hAsubA0, hD, hRbot, _hUnique, _hReq,
          _htildeA, _htildeA0, _htildeA1⟩, hChoice⟩ hy
  by_cases hxD : x ∈ D
  · rcases theorem_8_15_support_of_mem_D
      (G := G) (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0) (A1 := A1)
      (D := D) (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (R := R) hG hNotation
      ⟨_hA1subA, _hAsubA0, hD, hRbot, _hUnique, _hReq,
        _htildeA, _htildeA0, _htildeA1⟩ hxD with
      ⟨L, LF, hSupp, hReqx⟩
    rcases hSupp with ⟨_hLmax, _hLF, _hContain, _hSemiL, _hSemiC, hcop, _htype⟩
    have hcopLF : Nat.Coprime (Nat.card LF) (Nat.card (elementCentralizerIn M y)) :=
      hcop y hyA0
    have hcard_dvd : Nat.card (elementCentralizerIn LF x) ∣ Nat.card LF := by
      have hcard_dvd' :
          Nat.card ((elementCentralizerIn LF x).subgroupOf LF) ∣ Nat.card LF :=
        Subgroup.card_subgroup_dvd_card ((elementCentralizerIn LF x).subgroupOf LF)
      have hcard_eq :
          Nat.card ((elementCentralizerIn LF x).subgroupOf LF) =
            Nat.card (elementCentralizerIn LF x) :=
        natCard_subgroupOf_eq (elementCentralizerIn LF x) LF inf_le_left
      simpa [hcard_eq] using hcard_dvd'
    simpa [hReqx, Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using
      hcopLF.of_dvd_left hcard_dvd
  · have hxNotD : x ∈ A0 \ D := ⟨hxA0, hxD⟩
    have hR : R x = ⊥ := hRbot x hxNotD
    rw [hR, Subgroup.card_bot]
    exact Nat.coprime_one_left (Nat.card (Section2.centralizerIn M y))

private theorem theorem_8_15_hypothesis2_of_normalizer_eq
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G}
    {R : G → Subgroup G}
    (hG : IsMinCE G)
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R)
    (hNorm : Subgroup.normalizer Achoice = M) :
    Section2.hypothesis_2_2_statement Achoice M R := by
  classical
  dsimp [Section2.hypothesis_2_2_statement]
  rcases hData with ⟨hNotation, h14, hChoice⟩
  have hData' :
      theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R :=
    ⟨hNotation, h14, hChoice⟩
  have hA0_ne_one : ∀ x : G, x ∈ A0 → x ≠ 1 :=
    theorem_8_15_mem_source_X_ne_one hNotation (Or.inr rfl)
  have hA_ne_one : ∀ x : G, x ∈ A → x ≠ 1 :=
    theorem_8_15_mem_source_X_ne_one hNotation (Or.inl rfl)
  have hA0_mem_M : ∀ x : G, x ∈ A0 → x ∈ M :=
    theorem_8_15_mem_source_X_mem_M hNotation (Or.inr rfl)
  have hA_mem_M : ∀ x : G, x ∈ A → x ∈ M :=
    theorem_8_15_mem_source_X_mem_M hNotation (Or.inl rfl)
  have h13A :=
    (theorem_8_13 (G := G) M MF Ms A A0 A1 A) hG hNotation (Or.inl rfl)
  have h13A0 :=
    (theorem_8_13 (G := G) M MF Ms A A0 A1 A0) hG hNotation (Or.inr rfl)
  refine
    { subset_punctured := ?_
      subset_L := ?_
      L_le_normalizer := ?_
      G_conjugate_imp_L_conjugate := ?_
      centralizer_eq_product := ?_
      coprime_orders := ?_ }
  · intro x hx
    rcases h14 with ⟨hA1subA, _hAsubA0, _hD, _hRbot, _hUnique, _hReq,
      _htildeA, _htildeA0, _htildeA1⟩
    rcases hChoice with rfl | rfl | rfl
    · exact hA0_ne_one x hx
    · exact hA_ne_one x hx
    · exact hA_ne_one x (hA1subA hx)
  · intro x hx
    rcases h14 with ⟨hA1subA, _hAsubA0, _hD, _hRbot, _hUnique, _hReq,
      _htildeA, _htildeA0, _htildeA1⟩
    rcases hChoice with rfl | rfl | rfl
    · exact hA0_mem_M x hx
    · exact hA_mem_M x hx
    · exact hA_mem_M x (hA1subA hx)
  · rw [← hNorm]
    exact le_of_eq (theorem_8_15_setNormalizer_eq_subgroupNormalizer Achoice).symm
  · intro x y hx hy hconj
    rcases h14 with ⟨hA1subA, _hAsubA0, _hD, _hRbot, _hUnique, _hReq,
      _htildeA, _htildeA0, _htildeA1⟩
    have hconjTop : section16ConjugateInSubgroup (⊤ : Subgroup G) x y :=
      theorem_8_15_section16_top_conjugate_of_section2 hconj
    rcases hChoice with rfl | rfl | rfl
    · exact theorem_8_15_section2_conjugateInSubgroup_of_section16
        (h13A0.1 x y hx hy hconjTop)
    · exact theorem_8_15_section2_conjugateInSubgroup_of_section16
        (h13A.1 x y hx hy hconjTop)
    · exact theorem_8_15_section2_conjugateInSubgroup_of_section16
        (h13A.1 x y (hA1subA hx) (hA1subA hy) hconjTop)
  · intro x hx
    exact theorem_8_15_centralizer_semidirect (G := G) (M := M) (MF := MF)
      (Ms := Ms) (A := A) (A0 := A0) (A1 := A1) (Achoice := Achoice)
      (D := D) (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (R := R) hG hData' hx
  · intro x y hx hy
    exact theorem_8_15_coprime_orders (G := G) (M := M) (MF := MF)
      (Ms := Ms) (A := A) (A0 := A0) (A1 := A1) (Achoice := Achoice)
      (D := D) (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (R := R) hG hData' hx hy

private theorem theorem_8_15_le_normalizer_nonidentity
    {G : Type u} [Group G] {M H : Subgroup G}
    (hMnormH : M ≤ Subgroup.normalizer (H : Set G)) :
    M ≤ Subgroup.normalizer (section16NonidentityElements (H : Set G)) := by
  intro m hmM
  change ∀ x : G,
    x ∈ section16NonidentityElements (H : Set G) ↔
      m * x * m⁻¹ ∈ section16NonidentityElements (H : Set G)
  intro x
  constructor
  · intro hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hMnormH hmM) x).1 hx.1, ?_⟩
    intro h
    exact hx.2 (by
      have h' := congrArg (fun y : G => m⁻¹ * y * m) h
      simpa [mul_assoc] using h')
  · intro hx
    have hmInv : m⁻¹ ∈ M := M.inv_mem hmM
    have hxH : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (hMnormH hmInv) (m * x * m⁻¹)).1 hx.1
    refine ⟨?_, ?_⟩
    · simpa [mul_assoc] using hxH
    · intro hx1
      exact hx.2 (by simp [hx1])

private theorem theorem_8_15_le_normalizer_centralizerUnion
    {G : Type u} [Group G] {M C H : Subgroup G}
    (hMnormC : M ≤ Subgroup.normalizer (C : Set G))
    (hMnormH : M ≤ Subgroup.normalizer (H : Set G)) :
    M ≤ Subgroup.normalizer (section8CentralizerUnion C H) := by
  classical
  have hforward :
      ∀ m : G, m ∈ M → ∀ y : G, y ∈ section8CentralizerUnion C H →
        m * y * m⁻¹ ∈ section8CentralizerUnion C H := by
    intro m hmM y hy
    rw [section8CentralizerUnion] at hy ⊢
    rcases hy with ⟨x, hxHSharp, hyCentSharp⟩
    refine ⟨m * x * m⁻¹, ?_, ?_⟩
    · refine ⟨(Subgroup.mem_normalizer_iff.mp (hMnormH hmM) x).1 hxHSharp.1, ?_⟩
      intro h
      exact hxHSharp.2 (by
        have h' := congrArg (fun z : G => m⁻¹ * z * m) h
        simpa [mul_assoc] using h')
    · refine ⟨?_, ?_⟩
      · refine ⟨(Subgroup.mem_normalizer_iff.mp (hMnormC hmM) y).1 hyCentSharp.1.1, ?_⟩
        change m * y * m⁻¹ ∈ Subgroup.centralizer ({m * x * m⁻¹} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : y * x = x * y :=
          Subgroup.mem_centralizer_singleton_iff.mp hyCentSharp.1.2
        calc
          (m * y * m⁻¹) * (m * x * m⁻¹) = m * (y * x) * m⁻¹ := by group
          _ = m * (x * y) * m⁻¹ := by rw [hcomm]
          _ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
      · intro h
        exact hyCentSharp.2 (by
          have h' := congrArg (fun z : G => m⁻¹ * z * m) h
          simpa [mul_assoc] using h')
  intro m hmM
  change ∀ y : G,
    y ∈ section8CentralizerUnion C H ↔ m * y * m⁻¹ ∈ section8CentralizerUnion C H
  intro y
  constructor
  · exact hforward m hmM y
  · intro hy
    have hback := hforward m⁻¹ (M.inv_mem hmM) (m * y * m⁻¹) hy
    simpa [mul_assoc] using hback

private theorem theorem_8_15_le_normalizer_conjugates_by_M
    {G : Type u} [Group G] {M : Subgroup G} {X : Set G} :
    M ≤ Subgroup.normalizer (section16ConjugatesOfSetBySet X (M : Set G)) := by
  classical
  intro m hmM
  change ∀ z : G,
    z ∈ section16ConjugatesOfSetBySet X (M : Set G) ↔
      m * z * m⁻¹ ∈ section16ConjugatesOfSetBySet X (M : Set G)
  intro z
  constructor
  · rintro ⟨x, hxX, n, hnM, hz⟩
    refine ⟨x, hxX, m * n, M.mul_mem hmM hnM, ?_⟩
    rw [hz]
    group
  · rintro ⟨x, hxX, n, hnM, hz⟩
    refine ⟨x, hxX, m⁻¹ * n, M.mul_mem (M.inv_mem hmM) hnM, ?_⟩
    have hz' : m⁻¹ * (m * z * m⁻¹) * m = m⁻¹ * (n * x * n⁻¹) * m := by
      rw [hz]
    calc
      z = m⁻¹ * (m * z * m⁻¹) * m := by group
      _ = m⁻¹ * (n * x * n⁻¹) * m := hz'
      _ = (m⁻¹ * n) * x * (m⁻¹ * n)⁻¹ := by group

private theorem theorem_8_15_le_normalizer_union
    {G : Type u} [Group G] {M : Subgroup G} {X Y : Set G}
    (hX : M ≤ Subgroup.normalizer X)
    (hY : M ≤ Subgroup.normalizer Y) :
    M ≤ Subgroup.normalizer (X ∪ Y) := by
  intro m hmM
  change ∀ z : G, z ∈ X ∪ Y ↔ m * z * m⁻¹ ∈ X ∪ Y
  intro z
  constructor
  · intro hz
    rcases hz with hzX | hzY
    · exact Or.inl ((hX hmM z).1 hzX)
    · exact Or.inr ((hY hmM z).1 hzY)
  · intro hz
    rcases hz with hzX | hzY
    · exact Or.inl ((hX hmM z).2 hzX)
    · exact Or.inr ((hY hmM z).2 hzY)

private theorem theorem_8_15_le_normalizer_choice
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G}
    {R : G → Subgroup G}
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R) :
    M ≤ Subgroup.normalizer Achoice := by
  classical
  rcases hData with ⟨hNotation, _h14, hChoice⟩
  rcases hNotation with ⟨_hM, hMF, hMs, hA1, hCases⟩
  rcases hMF with ⟨hMFIn, _hMFmax⟩
  rcases hMFIn with ⟨hMFM, hMFnorm, _hMFnil, _hMFhall⟩
  let Dsub : Subgroup G := ambientDerivedSubgroup M
  have hDleM : Dsub ≤ M := by
    simpa [Dsub] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hDnorm : (Dsub.subgroupOf M).Normal := by
    simpa [Dsub] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hMnormM : M ≤ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer
  have hMnormMF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFnorm
  have hMnormD : M ≤ Subgroup.normalizer (Dsub : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDleM).1 hDnorm
  have hMnormMs : M ≤ Subgroup.normalizer (Ms : Set G) := by
    rcases hMs with hI | hII | hIII | hIV | hV
    · rcases hI with ⟨_hTypeI, _hnII, _hnIII, _hnIV, _hnV, hMs_eq⟩
      simpa [hMs_eq] using hMnormMF
    · rcases hII with ⟨_hnI, _hTypeII, _hnIII, _hnIV, _hnV, hMs_eq⟩
      simpa [hMs_eq] using hMnormMF
    · rcases hIII with ⟨_hnI, _hnII, _hTypeIII, _hnIV, _hnV, hMs_eq⟩
      simpa [hMs_eq, Dsub] using hMnormD
    · rcases hIV with ⟨_hnI, _hnII, _hnIII, _hTypeIV, _hnV, hMs_eq⟩
      simpa [hMs_eq, Dsub] using hMnormD
    · rcases hV with ⟨_hnI, _hnII, _hnIII, _hnIV, _hTypeV, hMs_eq⟩
      simpa [hMs_eq] using hMnormMF
  have hMnormA1 : M ≤ Subgroup.normalizer A1 := by
    have hraw :=
      theorem_8_15_le_normalizer_nonidentity
        (G := G) (M := M) (H := Ms) hMnormMs
    simpa [hA1, a1Set] using hraw
  have hMnormA_A0 :
      M ≤ Subgroup.normalizer A ∧ M ≤ Subgroup.normalizer A0 := by
    rcases hCases with hTypeI | hTypeP
    · rcases hTypeI with ⟨_hTypeI, hA, hA0⟩
      have hMnormA : M ≤ Subgroup.normalizer A := by
        have hraw :=
          theorem_8_15_le_normalizer_centralizerUnion
            (G := G) (M := M) (C := M) (H := MF) hMnormM hMnormMF
        simpa [hA] using hraw
      exact ⟨hMnormA, by simpa [hA0] using hMnormA⟩
    · rcases hTypeP with ⟨U, W1, W2, _hP, _hSourceType, hA, hA0, _hLate⟩
      have hMnormA : M ≤ Subgroup.normalizer A := by
        have hraw :=
          theorem_8_15_le_normalizer_centralizerUnion
            (G := G) (M := M) (C := Dsub) (H := Ms) hMnormD hMnormMs
        simpa [hA, Dsub] using hraw
      have hMnormConj :
          M ≤ Subgroup.normalizer
            (section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)) :=
        theorem_8_15_le_normalizer_conjugates_by_M
          (G := G) (M := M) (X := section16HatW W1 W2)
      have hMnormA0 : M ≤ Subgroup.normalizer A0 := by
        have hraw :=
          theorem_8_15_le_normalizer_union
            (G := G) (M := M) (X := A)
            (Y := section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
            hMnormA hMnormConj
        simpa [hA0] using hraw
      exact ⟨hMnormA, hMnormA0⟩
  rcases hChoice with rfl | rfl | rfl
  · exact hMnormA_A0.2
  · exact hMnormA_A0.1
  · exact hMnormA1

private theorem theorem_8_15_normalizer_proper
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M : Subgroup G} {Achoice : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hAM : Achoice ⊆ M)
    (hne : ∃ x : G, x ∈ Achoice ∧ x ≠ 1) :
    Subgroup.normalizer Achoice ≠ ⊤ := by
  classical
  intro hnormTop
  letI : IsSimpleGroup G := IsMinCE.simple
  rcases hne with ⟨a, haA, hane⟩
  let N : Subgroup G := Subgroup.normalClosure ({a} : Set G)
  have hNleM : N ≤ M := by
    dsimp [N]
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    rw [Group.mem_conjugatesOfSet_iff] at hy
    rcases hy with ⟨z, hz, hzy⟩
    have hz_eq : z = a := by simpa using hz
    subst z
    rcases isConj_iff.mp hzy with ⟨g, hgy⟩
    have hgNorm : g ∈ Subgroup.normalizer Achoice := by
      rw [hnormTop]
      simp
    have hgNorm' : ∀ n : G, n ∈ Achoice ↔ g * n * g⁻¹ ∈ Achoice := by
      simpa [Subgroup.normalizer] using hgNorm
    have hga : g * a * g⁻¹ ∈ Achoice :=
      (hgNorm' a).1 haA
    have hyA : y ∈ Achoice := by
      rwa [← hgy]
    exact hAM hyA
  have hNne : N ≠ ⊥ := by
    intro hNbot
    have haN : a ∈ N := Subgroup.subset_normalClosure (by simp)
    have haBot : a ∈ (⊥ : Subgroup G) := by
      simpa [N, hNbot] using haN
    exact hane (by simpa using haBot)
  have hNnormal : N.Normal := by
    dsimp [N]
    infer_instance
  rcases (haveI := hNnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal N) with hNbot | hNtop
  · exact hNne hNbot
  · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hNtop] using hNleM
    have hM8 : M ∈ section8MaximalSubgroups G :=
      section8_maximal_of_section9_maximal hM
    exact section8MaximalSubgroups_ne_top hM8 (top_le_iff.mp htop_le_M)

private theorem theorem_8_15_normalizer_eq
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G}
    {R : G → Subgroup G}
    (hG : IsMinCE G)
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R) :
    Subgroup.normalizer Achoice = M := by
  classical
  letI : IsMinCE G := hG
  rcases hData with ⟨hNotation, h14, hChoice⟩
  have hData' :
      theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R :=
    ⟨hNotation, h14, hChoice⟩
  rcases hNotation with ⟨hM, _hMF, _hMs, _hA1, _hCases⟩
  have hMleNorm : M ≤ Subgroup.normalizer Achoice :=
    theorem_8_15_le_normalizer_choice (G := G) (M := M) (MF := MF) (Ms := Ms)
      (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
      (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
      (R := R) hData'
  have hNorm_ne_top : Subgroup.normalizer Achoice ≠ ⊤ :=
    theorem_8_15_normalizer_proper (G := G) (M := M) (Achoice := Achoice)
      hM
      (theorem_8_15_choice_subset_M (G := G) (M := M) (MF := MF) (Ms := Ms)
        (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
        (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
        (R := R) hData')
      (theorem_8_15_choice_nonempty (G := G) (M := M) (MF := MF) (Ms := Ms)
        (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
        (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
        (R := R) hData')
  have hM8 : M ∈ section8MaximalSubgroups G :=
    section8_maximal_of_section9_maximal hM
  exact section8MaximalSubgroups_eq_of_le hM8 hMleNorm hNorm_ne_top


public theorem theorem_8_15_hypothesis2
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G}
    {R : G → Subgroup G}
    (hG : IsMinCE G)
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R) :
    Section2.hypothesis_2_2_statement Achoice M R := by
  exact theorem_8_15_hypothesis2_of_normalizer_eq (G := G) (M := M) (MF := MF)
    (Ms := Ms) (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
    (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
    (R := R) hG hData
    (theorem_8_15_normalizer_eq (G := G) (M := M) (MF := MF) (Ms := Ms)
      (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
      (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
      (R := R) hG hData)

public theorem theorem_8_15_subgroupSetPreimage_typeP_A0_eq
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G} {A A0 : Set G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hA0 : A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)) :
    section8SubgroupSetPreimage M A0 = section8CyclicA0Set M W1 W2 A := by
  classical
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  have hW1M : W1 ≤ M := hW1hall.1
  have hW2M : W2 ≤ M := fun y hy => hMF.1.1 (hW2le hy).1
  have hWM : W1 ⊔ W2 ≤ M := sup_le hW1M hW2M
  ext x
  constructor
  · intro hx
    change (x : G) ∈ A0 at hx
    rw [hA0] at hx
    rcases hx with hxA | hxConj
    · exact Or.inl hxA
    · rcases hxConj with ⟨w, hw, m, hmM, hx_eq⟩
      let wM : M := ⟨w, hWM hw.1⟩
      have hwM :
          wM ∈ Section3.cyclicTISet
            (W1.subgroupOf M) (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M) := by
        simpa [wM, Section3.cyclicTISet, section16HatW, Subgroup.mem_subgroupOf]
          using hw
      let mM : M := ⟨m, hmM⟩
      refine Or.inr ?_
      refine ⟨wM, hwM, mM, ?_⟩
      ext
      simpa [Section2.conjBy, wM, mM] using hx_eq.symm
  · intro hx
    change (x : G) ∈ A0
    rw [hA0]
    rcases hx with hxA | hxConj
    · exact Or.inl hxA
    · rcases hxConj with ⟨wM, hwM, mM, hconj⟩
      refine Or.inr ?_
      refine ⟨(wM : G), ?_, (mM : G), mM.property, ?_⟩
      · simpa [Section3.cyclicTISet, section16HatW, Subgroup.mem_subgroupOf]
          using hwM
      · have hval := congrArg Subtype.val hconj
        simpa [Section2.conjBy] using hval.symm

private theorem theorem_8_15_typeP_A_preimage_subset_derived_nonidentity
    {G : Type u} [Group G] [Finite G]
    {M Ms : Subgroup G} {A : Set G}
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms) :
    section8SubgroupSetPreimage M A ⊆ ((derivedSubgroup M : Subgroup M) : Set M) \ {1} := by
  intro x hx
  change (x : G) ∈ A at hx
  rw [hA, section8CentralizerUnion] at hx
  rcases hx with ⟨_z, _hz, hxCent⟩
  constructor
  · rw [← section12_ambientDerivedSubgroup_subgroupOf_eq]
    change (x : G) ∈ ambientDerivedSubgroup M
    exact hxCent.1.1
  · intro hxOne
    have hxGOne : (x : G) = 1 := by
      simpa using congrArg Subtype.val hxOne
    exact hxCent.2 hxGOne

private theorem theorem_8_15_hypothesis46_centralizers_subset_A
    {G : Type u} [Group G] [Finite G]
    {M Ms H : Subgroup G} {A : Set G}
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hHleMs : H ≤ Ms) :
    (⋃ h : {h : H.subgroupOf M // (h : M) ≠ 1},
      (((Section2.centralizerIn (derivedSubgroup M) ((h : H.subgroupOf M) : M)) : Set M) \
        {1})) ⊆ section8SubgroupSetPreimage M A := by
  intro y hy
  rw [Set.mem_iUnion] at hy
  rcases hy with ⟨h, hy⟩
  rcases hy with ⟨hyCent, hyNe⟩
  change (y : G) ∈ A
  rw [hA, section8CentralizerUnion]
  refine ⟨(((h : H.subgroupOf M) : M) : G), ?_, ?_⟩
  · constructor
    · exact hHleMs (show (((h : H.subgroupOf M) : M) : G) ∈ H from
        (h : H.subgroupOf M).property)
    · intro hhOneG
      apply h.property
      apply Subtype.ext
      exact hhOneG
  · constructor
    · constructor
      · have hyDer : y ∈ (derivedSubgroup M : Subgroup M) := hyCent.1
        rw [← section12_ambientDerivedSubgroup_subgroupOf_eq] at hyDer
        change (y : G) ∈ ambientDerivedSubgroup M at hyDer
        exact hyDer
      · have hyCommM :=
          Subgroup.mem_centralizer_singleton_iff.mp hyCent.2
        exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hyCommM)
    · intro hyOneG
      apply hyNe
      apply Subtype.ext
      exact hyOneG

private theorem theorem_8_15_typeP_MF_normal
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    (MF.subgroupOf M).Normal := by
  exact hP.1.1.2.1

private theorem theorem_8_15_typeP_MF_le_derived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    MF.subgroupOf M ≤ derivedSubgroup M := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  intro x hx
  rw [← section12_ambientDerivedSubgroup_subgroupOf_eq]
  change (x : G) ∈ ambientDerivedSubgroup M
  exact hcompDU.1 (by simpa [Subgroup.mem_subgroupOf] using hx)

private theorem theorem_8_15_typeP_W2_le_ambientDerived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ ambientDerivedSubgroup M := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  intro z hz
  have hDerDer_le_Der :
      section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
    simpa [section16SecondDerivedSubgroup] using
      (section12_ambientDerivedSubgroup_le (G := G)
        (E := ambientDerivedSubgroup M))
  exact hDerDer_le_Der (hW2le hz).2

private theorem theorem_8_15_typeP_W2_le_MF
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ MF := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  intro z hz
  exact (hW2le hz).1

private theorem theorem_8_15_typeP_W2_le_Ms
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ Ms := by
  rcases hNotation with ⟨_hM, _hMF, hMs, _hA1, _hCases⟩
  rcases hP with
    ⟨_hMFP, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  have hW2MF : W2 ≤ MF := fun z hz => (hW2le hz).1
  have hW2D : W2 ≤ ambientDerivedSubgroup M :=
    fun z hz => by
      have hDerDer_le_Der :
          section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
        simpa [section16SecondDerivedSubgroup] using
          (section12_ambientDerivedSubgroup_le (G := G)
            (E := ambientDerivedSubgroup M))
      exact hDerDer_le_Der (hW2le hz).2
  rcases hMs with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hW2MF
  · rcases hII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hW2MF
  · rcases hIII with ⟨_hnotI, _hnotII, _hIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hW2D
  · rcases hIV with ⟨_hnotI, _hnotII, _hnotIII, _hIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hW2D
  · rcases hV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, _hV, hMs_eq⟩
    rw [hMs_eq]
    exact hW2MF

private theorem theorem_8_15_typeP_MF_le_Ms
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2) :
    MF ≤ Ms := by
  rcases hNotation with ⟨_hM, _hMF, hMs, _hA1, _hCases⟩
  rcases hP with
    ⟨_hMFP, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  have hMFleD : MF ≤ ambientDerivedSubgroup M := hcompDU.1
  rcases hMs with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
  · rcases hII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
  · rcases hIII with ⟨_hnotI, _hnotII, _hIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hMFleD
  · rcases hIV with ⟨_hnotI, _hnotII, _hnotIII, _hIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hMFleD
  · rcases hV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, _hV, hMs_eq⟩
    rw [hMs_eq]

private theorem theorem_8_15_typeP_Ms_normal
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2) :
    (Ms.subgroupOf M).Normal := by
  rcases hNotation with ⟨_hM, _hMF, hMs, _hA1, _hCases⟩
  have hMFnorm : (MF.subgroupOf M).Normal :=
    theorem_8_15_typeP_MF_normal
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP
  have hDnorm : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using
      (inferInstance : (derivedSubgroup M).Normal)
  rcases hMs with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hMFnorm
  · rcases hII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hMFnorm
  · rcases hIII with ⟨_hnotI, _hnotII, _hIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hDnorm
  · rcases hIV with ⟨_hnotI, _hnotII, _hnotIII, _hIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hDnorm
  · rcases hV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, _hV, hMs_eq⟩
    rw [hMs_eq]
    exact hMFnorm

private theorem theorem_8_15_typeP_Ms_le_derived
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2) :
    Ms.subgroupOf M ≤ derivedSubgroup M := by
  rcases hNotation with ⟨_hM, _hMF, hMs, _hA1, _hCases⟩
  have hMFleD : MF.subgroupOf M ≤ derivedSubgroup M :=
    theorem_8_15_typeP_MF_le_derived
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP
  have hDleD : (ambientDerivedSubgroup M).subgroupOf M ≤ derivedSubgroup M := by
    rw [section12_ambientDerivedSubgroup_subgroupOf_eq]
  rcases hMs with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hMFleD
  · rcases hII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hMFleD
  · rcases hIII with ⟨_hnotI, _hnotII, _hIII, _hnotIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hDleD
  · rcases hIV with ⟨_hnotI, _hnotII, _hnotIII, _hIV, _hnotV, hMs_eq⟩
    rw [hMs_eq]
    exact hDleD
  · rcases hV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, _hV, hMs_eq⟩
    rw [hMs_eq]
    exact hMFleD

private theorem theorem_8_15_typeP_W2_le_M
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ M := by
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  intro x hx
  exact hMF.1.1 ((hW2le hx).1)

private theorem theorem_8_15_typeP_W1_inf_W2_eq_bot
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W1 ⊓ W2 = ⊥ := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  apply le_antisymm
  · intro x hx
    have hxD : x ∈ ambientDerivedSubgroup M := by
      have hDerDer_le_Der :
          section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
        simpa [section16SecondDerivedSubgroup] using
          (section12_ambientDerivedSubgroup_le (G := G)
            (E := ambientDerivedSubgroup M))
      exact hDerDer_le_Der (hW2le hx.2).2
    have hxInf : x ∈ ambientDerivedSubgroup M ⊓ W1 := ⟨hxD, hx.1⟩
    simpa using hcompMW1.2.2.2.le_bot hxInf
  · exact bot_le

private theorem theorem_8_15_typeP_W2_le_centralizer_W1
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ Subgroup.centralizer (W1 : Set G) := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, hCent, _hHatW⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · have hyCent : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
      simpa [hCent x hx hx1] using hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hyCent.2).symm

private theorem theorem_8_15_typeP_semidirect_derived_W1
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    Section2.IsInternalSemidirectProduct
      (⊤ : Subgroup M) (derivedSubgroup M) (W1.subgroupOf M) := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  have hDnorm : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using
      (inferInstance : (derivedSubgroup M).Normal)
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnorm
  have hsup_local :
      (ambientDerivedSubgroup M).subgroupOf M ⊔ W1.subgroupOf M = ⊤ := by
    calc
      (ambientDerivedSubgroup M).subgroupOf M ⊔ W1.subgroupOf M =
          (ambientDerivedSubgroup M ⊔ W1).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := ambientDerivedSubgroup M) (A' := W1) (B := M)
          hcompMW1.1 hcompMW1.2.1
      _ = ⊤ := by
        rw [← hcompMW1.2.2.1]
        simp
  refine
    { left_le := by intro x _hx; simp
      right_le := by intro x _hx; simp
      right_normalizes_left := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro k _hk h hh
    simpa [Section2.conjBy] using
      (Subgroup.Normal.conj_mem
        (inferInstance : (derivedSubgroup M).Normal) h hh k)
  · apply le_antisymm
    · intro x hx
      have hxDsub : x ∈ (ambientDerivedSubgroup M).subgroupOf M := by
        simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hx.1
      have hxInf : (x : G) ∈ ambientDerivedSubgroup M ⊓ W1 := by
        constructor
        · simpa [Subgroup.mem_subgroupOf] using hxDsub
        · simpa [Subgroup.mem_subgroupOf] using hx.2
      have hxBotG : (x : G) ∈ (⊥ : Subgroup G) :=
        hcompMW1.2.2.2.le_bot hxInf
      ext
      simpa using hxBotG
    · exact bot_le
  · intro c _hc
    have hcSup : c ∈
        (ambientDerivedSubgroup M).subgroupOf M ⊔ W1.subgroupOf M := by
      rw [hsup_local]
      simp
    rcases (Subgroup.mem_sup_of_normal_left
        (s := (ambientDerivedSubgroup M).subgroupOf M)
        (t := W1.subgroupOf M) (x := c)).1 hcSup with
      ⟨d, hdD, w, hwW1, hmul⟩
    refine ⟨d, ?_, w, hwW1, ?_⟩
    · simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hdD
    · simpa using hmul.symm

private theorem theorem_8_15_typeP_centralizerIn_derived_eq_W2
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∀ x : W1.subgroupOf M, x ≠ 1 →
      Section2.centralizerIn (derivedSubgroup M) (x : M) = W2.subgroupOf M := by
  intro x hx
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, hCent, _hHatW⟩
  have hxW1 : ((x : M) : G) ∈ W1 := by
    exact Subgroup.mem_subgroupOf.mp x.property
  have hxGne : ((x : M) : G) ≠ 1 := by
    intro hxG
    have hxM : (x : M) = 1 := Subtype.ext hxG
    exact hx (Subtype.ext hxM)
  ext y
  constructor
  · intro hy
    have hyDsub : y ∈ (ambientDerivedSubgroup M).subgroupOf M := by
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hy.1
    have hyDerG : ((y : M) : G) ∈ ambientDerivedSubgroup M := by
      simpa [Subgroup.mem_subgroupOf] using hyDsub
    have hyCommM :
        y * (x : M) = (x : M) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hyCommG :
        ((y : M) : G) * ((x : M) : G) =
          ((x : M) : G) * ((y : M) : G) :=
      congrArg Subtype.val hyCommM
    have hyCentG :
        ((y : M) : G) ∈ elementCentralizerIn (ambientDerivedSubgroup M) ((x : M) : G) :=
      ⟨hyDerG, Subgroup.mem_centralizer_singleton_iff.mpr hyCommG⟩
    have hyW2G : ((y : M) : G) ∈ W2 := by
      simpa [hCent ((x : M) : G) hxW1 hxGne] using hyCentG
    simpa [Subgroup.mem_subgroupOf] using hyW2G
  · intro hy
    have hyW2G : ((y : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hy
    have hyCentG :
        ((y : M) : G) ∈ elementCentralizerIn (ambientDerivedSubgroup M) ((x : M) : G) := by
      simpa [hCent ((x : M) : G) hxW1 hxGne] using hyW2G
    constructor
    · have hyDsub : y ∈ (ambientDerivedSubgroup M).subgroupOf M := by
        simpa [Subgroup.mem_subgroupOf] using hyCentG.1
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hyDsub
    · have hyCommG :
          ((y : M) : G) * ((x : M) : G) =
            ((x : M) : G) * ((y : M) : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hyCentG.2
      have hyCommM : y * (x : M) = (x : M) * y := by
        apply Subtype.ext
        exact hyCommG
      exact Subgroup.mem_centralizer_singleton_iff.mpr hyCommM

public theorem theorem_8_15_typeP_W_internalDirectProduct
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    Section2.IsInternalDirectProduct
      ((W1 ⊔ W2).subgroupOf M) (W1.subgroupOf M) (W2.subgroupOf M) := by
  classical
  have hP0 : typePDefinitionData M MF U W1 W2 := hP
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  rcases hW1hall with ⟨hW1M, _hW1HallSub⟩
  have hW2M : W2 ≤ M :=
    theorem_8_15_typeP_W2_le_M
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
  have hW2centW1 : W2 ≤ Subgroup.centralizer (W1 : Set G) :=
    theorem_8_15_typeP_W2_le_centralizer_W1
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
  have hW1infW2 : W1 ⊓ W2 = ⊥ :=
    theorem_8_15_typeP_W1_inf_W2_eq_bot
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
  have hW1_norm_W2 : W1 ≤ Subgroup.normalizer (W2 : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : a * y = y * a :=
        Subgroup.mem_centralizer_iff.mp (hW2centW1 hy) a ha
      have hconj : a * y * a⁻¹ = y := by
        calc
          a * y * a⁻¹ = y * a * a⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hconj] using hy
    · intro hy
      let y' : G := a * y * a⁻¹
      have hy'W2 : y' ∈ W2 := by simpa [y'] using hy
      have hcomm' : a * y' = y' * a :=
        Subgroup.mem_centralizer_iff.mp (hW2centW1 hy'W2) a ha
      have hconj : a⁻¹ * y' * a = y' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hy_eq : y = y' := by
        calc
          y = a⁻¹ * y' * a := by simp [y', mul_assoc]
          _ = y' := hconj
      simpa [hy_eq] using hy'W2
  let W : Subgroup G := W1 ⊔ W2
  let W1W : Subgroup W := W1.subgroupOf W
  let W2W : Subgroup W := W2.subgroupOf W
  haveI : W2W.Normal := by
    simpa [W, W2W] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := W2) hW1_norm_W2)
  have hW1W_W2W_top : W1W ⊔ W2W = ⊤ := by
    calc
      W1W ⊔ W2W = W.subgroupOf W := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := W1) (A' := W2) (B := W)
          (by simp [W])
          (by simp [W])
      _ = ⊤ := by simp
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x hx
    have hxW1 : ((x : M) : G) ∈ W1 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using
      ((le_sup_left : W1 ≤ W1 ⊔ W2) hxW1)
  · intro x hx
    have hxW2 : ((x : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using
      ((le_sup_right : W2 ≤ W1 ⊔ W2) hxW2)
  · intro h hh k hk
    have hhW1 : ((h : M) : G) ∈ W1 := by
      simpa [Subgroup.mem_subgroupOf] using hh
    have hkW2 : ((k : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hk
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hW2centW1 hkW2) ((h : M) : G) hhW1
  · apply le_antisymm
    · intro x hx
      have hxAmb : ((x : M) : G) ∈ W1 ⊓ W2 := by
        constructor
        · simpa [Subgroup.mem_subgroupOf] using hx.1
        · simpa [Subgroup.mem_subgroupOf] using hx.2
      have hxBotG : ((x : M) : G) ∈ (⊥ : Subgroup G) := by
        simpa [hW1infW2] using hxAmb
      ext
      simpa using hxBotG
    · exact bot_le
  · intro c hc
    let cW : W := ⟨((c : M) : G), by simpa [W, Subgroup.mem_subgroupOf] using hc⟩
    have hcSup : cW ∈ W1W ⊔ W2W := by
      rw [hW1W_W2W_top]
      simp
    rcases (Subgroup.mem_sup_of_normal_right (s := W1W) (t := W2W) (x := cW)).1
        hcSup with
      ⟨aW, haW, bW, hbW, hab⟩
    have haW1 : (aW : G) ∈ W1 := by
      simpa [W1W, Subgroup.mem_subgroupOf] using haW
    have hbW2 : (bW : G) ∈ W2 := by
      simpa [W2W, Subgroup.mem_subgroupOf] using hbW
    let aM : M := ⟨(aW : G), hW1M haW1⟩
    let bM : M := ⟨(bW : G), hW2M hbW2⟩
    refine ⟨aM, ?_, bM, ?_, ?_⟩
    · simpa [aM, Subgroup.mem_subgroupOf] using haW1
    · simpa [bM, Subgroup.mem_subgroupOf] using hbW2
    · apply Subtype.ext
      have hval := congrArg (fun z : W => (z : G)) hab
      simpa [aM, bM, cW] using hval.symm

private theorem theorem_8_15_hypothesis42_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hG : IsMinCE G)
    (hP : typePDefinitionData M MF U W1 W2) :
    Section4.hypothesis_4_2_statement
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M) := by
  classical
  have hP0 : typePDefinitionData M MF U W1 W2 := hP
  rcases hP with
    ⟨_hMF, hW1cyc, hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, hW2cyc, hW2ne, _hCent, _hHatW⟩
  rcases hW1hall with ⟨hW1M, hW1HallSub⟩
  have hW2M : W2 ≤ M :=
    theorem_8_15_typeP_W2_le_M
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact theorem_8_15_typeP_semidirect_derived_W1
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
  · exact ⟨subgroupPrimeSet W1, hW1HallSub⟩
  · exact (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).isCyclic.2
      hW1cyc
  · intro hcard
    apply hW1ne
    apply (Subgroup.card_eq_one (H := W1)).1
    have hcard_eq : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
      natCard_subgroupOf_eq W1 M hW1M
    rwa [← hcard_eq]
  · exact (Subgroup.subgroupOfEquivOfLe (H := W2) (K := M) hW2M).isCyclic.2
      hW2cyc
  · intro hcard
    apply hW2ne
    apply (Subgroup.card_eq_one (H := W2)).1
    have hcard_eq : Nat.card (W2.subgroupOf M) = Nat.card W2 :=
      natCard_subgroupOf_eq W2 M hW2M
    rwa [← hcard_eq]
  · exact theorem_8_15_typeP_centralizerIn_derived_eq_W2
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
  · intro x hx
    have hxW1 : ((x : M) : G) ∈ W1 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using
      ((le_sup_left : W1 ≤ W1 ⊔ W2) hxW1)
  · intro x hx
    have hxW2 : ((x : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using
      ((le_sup_right : W2 ≤ W1 ⊔ W2) hxW2)
  · exact theorem_8_15_typeP_W_internalDirectProduct
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
  · letI : IsMinCE G := hG
    have hWleM : W1 ⊔ W2 ≤ M := sup_le hW1M hW2M
    have hWodd : Odd (Nat.card (W1 ⊔ W2 : Subgroup G)) :=
      odd_of_card_dvd IsMinCE.odd_order
        (Subgroup.card_subgroup_dvd_card (W1 ⊔ W2 : Subgroup G))
    have hcard_eq :
        Nat.card ((W1 ⊔ W2).subgroupOf M) =
          Nat.card (W1 ⊔ W2 : Subgroup G) :=
      natCard_subgroupOf_eq (W1 ⊔ W2 : Subgroup G) M hWleM
    simpa [hcard_eq] using hWodd

/-- A Type-P maximal subgroup supplies the PF `(4.2)` package for
`M'`, `W₁`, `W₂`, and `W₁ ⊔ W₂`. -/
public theorem theorem_8_15_hypothesis_4_2_of_typeP
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hG : IsMinCE G)
    (hP : typePDefinitionData M MF U W1 W2) :
    Section4.hypothesis_4_2_statement
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M) :=
  theorem_8_15_hypothesis42_core hG hP


public theorem theorem_8_15_typeP_W2_subgroupOf_le_derived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2.subgroupOf M ≤ derivedSubgroup M := by
  intro x hx
  have hxD : ((x : M) : G) ∈ ambientDerivedSubgroup M :=
    theorem_8_15_typeP_W2_le_ambientDerived
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      hP (by simpa [Subgroup.mem_subgroupOf] using hx)
  rw [← section12_ambientDerivedSubgroup_subgroupOf_eq]
  simpa [Subgroup.mem_subgroupOf] using hxD


public theorem theorem_8_15_hypothesis_3_1_of_typeP
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hG : IsMinCE G)
    (hP : typePDefinitionData M MF U W1 W2) :
    Section3.hypothesis_3_1_statement
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M) := by
  exact
    (Section4.theorem_4_3_a
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M)
      (theorem_8_15_hypothesis_4_2_of_typeP
        (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
        hG hP)).2

private theorem theorem_8_15_hypothesis46_core
    {G : Type u} [Group G] [Finite G]
    {M MF Ms H : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G}
    {R : G → Subgroup G}
    (hG : IsMinCE G)
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R) :
    ∀ U W1 W2 : Subgroup G,
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2 →
        H = MF ∨ H = Ms →
          Section4Scratch.hypothesis_4_6_statement
            (derivedSubgroup M)
            (W1.subgroupOf M)
            (W2.subgroupOf M)
            ((W1 ⊔ W2).subgroupOf M)
            (H.subgroupOf M)
            (section8SubgroupSetPreimage M A) := by
  intro U W1 W2 hWitness hH
  rcases hData with ⟨hNotation, _h14, _hChoice⟩
  rcases hWitness with ⟨hP, _hSourceType, hA, _hA0, _hLate⟩
  have h42 :
      Section4.hypothesis_4_2_statement
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M) :=
    theorem_8_15_hypothesis42_core
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hG hP
  have hAsub :
      section8SubgroupSetPreimage M A ⊆ ((derivedSubgroup M : Subgroup M) : Set M) \ {1} :=
    theorem_8_15_typeP_A_preimage_subset_derived_nonidentity
      (G := G) (M := M) (Ms := Ms) (A := A) hA
  rcases hH with rfl | rfl
  · have hW2MF : W2.subgroupOf M ≤ H.subgroupOf M := by
      intro x hx
      exact theorem_8_15_typeP_W2_le_MF
        (G := G) (M := M) (MF := H) (U := U) (W1 := W1) (W2 := W2) hP
        (by simpa [Subgroup.mem_subgroupOf] using hx)
    have hMFleMs : H ≤ Ms :=
      theorem_8_15_typeP_MF_le_Ms
        (G := G) (M := M) (MF := H) (Ms := Ms) (U := U) (W1 := W1)
        (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP
    refine ⟨h42, ?_, hW2MF, ?_, ?_, hAsub⟩
    · exact theorem_8_15_typeP_MF_normal
        (G := G) (M := M) (MF := H) (U := U) (W1 := W1) (W2 := W2) hP
    · exact theorem_8_15_typeP_MF_le_derived
        (G := G) (M := M) (MF := H) (U := U) (W1 := W1) (W2 := W2) hP
    · exact theorem_8_15_hypothesis46_centralizers_subset_A
        (G := G) (M := M) (Ms := Ms) (H := H) (A := A) hA hMFleMs
  · have hW2Ms : W2.subgroupOf M ≤ H.subgroupOf M := by
      intro x hx
      exact theorem_8_15_typeP_W2_le_Ms
        (G := G) (M := M) (MF := MF) (Ms := H) (U := U) (W1 := W1)
        (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP
        (by simpa [Subgroup.mem_subgroupOf] using hx)
    refine ⟨h42, ?_, hW2Ms, ?_, ?_, hAsub⟩
    · exact theorem_8_15_typeP_Ms_normal
        (G := G) (M := M) (MF := MF) (Ms := H) (U := U) (W1 := W1)
        (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP
    · exact theorem_8_15_typeP_Ms_le_derived
        (G := G) (M := M) (MF := MF) (Ms := H) (U := U) (W1 := W1)
        (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP
    · exact theorem_8_15_hypothesis46_centralizers_subset_A
        (G := G) (M := M) (Ms := H) (H := H) (A := A) hA le_rfl

private theorem theorem_8_15_hypothesis46
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G}
    {R : G → Subgroup G}
    (hG : IsMinCE G)
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D tildeA tildeA0 tildeA1 R) :
    ∀ U W1 W2 : Subgroup G,
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2 →
        section8Hypothesis46Source M W1 W2 MF A A0 ∧
          section8Hypothesis46Source M W1 W2 Ms A A0 := by
  intro U W1 W2 hWitness
  have hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) :=
    hWitness.2.2.2.1
  have hA0pre :
      section8SubgroupSetPreimage M A0 = section8CyclicA0Set M W1 W2 A :=
    theorem_8_15_subgroupSetPreimage_typeP_A0_eq
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (A := A) (A0 := A0) hWitness.1 hA0
  have hAsub : A ⊆ A0 := by
    intro x hx
    rw [hA0]
    exact Or.inl hx
  have h46MF :
      Section4Scratch.hypothesis_4_6_statement
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        (MF.subgroupOf M)
        (section8SubgroupSetPreimage M A) := by
    exact theorem_8_15_hypothesis46_core (G := G) (M := M) (MF := MF) (Ms := Ms)
      (H := MF) (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
      (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
      (R := R) hG hData U W1 W2 hWitness (Or.inl rfl)
  have h46Ms :
      Section4Scratch.hypothesis_4_6_statement
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        (Ms.subgroupOf M)
        (section8SubgroupSetPreimage M A) := by
    exact theorem_8_15_hypothesis46_core (G := G) (M := M) (MF := MF) (Ms := Ms)
      (H := Ms) (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
      (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
      (R := R) hG hData U W1 W2 hWitness (Or.inr rfl)
  exact ⟨⟨hA0pre, h46MF, hAsub⟩, ⟨hA0pre, h46Ms, hAsub⟩⟩

/-- PF `(8.15)` supplies the bare Section `(4.6)` statements for the Type-P
witness selected by the PF `(8.10)` notation. -/
public theorem theorem_8_15_hypothesis_4_6_source
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G}
    {R : G → Subgroup G}
    (hG : IsMinCE G)
    (hData : theorem_8_15_source_data M MF Ms A A0 A1 Achoice D
      tildeA tildeA0 tildeA1 R) :
    ∀ U W1 W2 : Subgroup G,
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2 →
        section8Hypothesis46Source M W1 W2 MF A A0 ∧
          section8Hypothesis46Source M W1 W2 Ms A A0 :=
  theorem_8_15_hypothesis46 hG hData

private theorem theorem_8_15_inducedFromNonkernelFamily
    {G : Type u} [Group G] [Finite G]
    {M Ms : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hS : section8InducedNonkernelFamily M Ms S) :
    Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup M) (Ms.subgroupOf M) S := by
  intro χ hχ
  rcases hS.2.2 χ hχ with ⟨θ, hθirr, hθnonker, hχeq⟩
  refine ⟨θ, hθirr, ?_, hχeq⟩
  intro hker
  apply hθnonker
  intro m hmMs
  let a : (Ms.subgroupOf M).subgroupOf (derivedSubgroup M) :=
    ⟨m, by
      change ((m : M) : G) ∈ Ms
      exact hmMs⟩
  have ha := hker a
  simpa [a, Section1.subgroupInKernel', Section1.degree] using ha

private theorem theorem_8_15_hypothesis52_a
    {G : Type u} [Group G] [Finite G]
    {M Ms : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hG : IsMinCE G)
    (hS : section8InducedNonkernelFamily M Ms S) :
    Section5.hypothesis_5_2_a_statement S := by
  classical
  have hModd : Odd (Nat.card M) :=
    Odd.of_dvd_nat hG.odd_order (Subgroup.card_subgroup_dvd_card M)
  intro X
  constructor
  · exact hS.2.1 (X : Section1.ClassFunction M) X.2
  · intro hreal
    rcases hS.2.2 (X : Section1.ClassFunction M) X.2 with
      ⟨θ, hθirr, hθnonker, hXeq⟩
    rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
    have hθne' :
        ρ.character ≠ Section1.principalCharacter (derivedSubgroup M) := by
      intro hprin
      apply hθnonker
      intro m hmMs
      rw [hθeq, hprin]
      simp [Section1.principalCharacter]
    have horth :=
      Section1.proposition_1_5_e_rep_dual_orbit_relIndex_canonical
        (derivedSubgroup M) ρ hModd hρirr hθne'
    have horth0 :
        Section1.scalarProduct M
          (X : Section1.ClassFunction M)
          (Section1.conjugateCharacter (X : Section1.ClassFunction M)) = 0 := by
      simpa [Section1.orthogonal, hXeq, hθeq] using horth
    have hself0 :
        Section1.scalarProduct M
          (X : Section1.ClassFunction M) (X : Section1.ClassFunction M) = 0 := by
      simpa [← hreal] using horth0
    have hself :
        Section1.scalarProduct M
          (X : Section1.ClassFunction M) (X : Section1.ClassFunction M) =
            ((derivedSubgroup M).relIndex
              (Section1.inertiaSubgroup (derivedSubgroup M) ρ.character) : ℂ) := by
      simpa [hXeq, hθeq] using
        (Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
          (derivedSubgroup M) ρ hρirr)
    have hrel_ne :
        (((derivedSubgroup M).relIndex
          (Section1.inertiaSubgroup (derivedSubgroup M) ρ.character)) : ℂ) ≠ 0 := by
      have hrel_nat_ne :
          (derivedSubgroup M).relIndex
            (Section1.inertiaSubgroup (derivedSubgroup M) ρ.character) ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      exact_mod_cast hrel_nat_ne
    exact hrel_ne (by rw [← hself, hself0])

public theorem theorem_8_15_hypothesis_5_2_of_fullData
    {G : Type u} [Group G] [Finite G]
    {M Ms W1 W2 : Subgroup G}
    {A : Set G}
    {S : Finset (Section1.ClassFunction M)} :
    IsMinCE G →
      (d : section8Hypothesis52FullData M Ms W1 W2 A) →
        section8InducedNonkernelFamily M Ms S →
          Section5.hypothesis_5_2_statement S d.tau := by
  intro hG d hS
  classical
  letI : Fintype d.I := d.instFintypeI
  letI : Fintype d.J := d.instFintypeJ
  letI : DecidableEq d.I := d.instDecidableEqI
  letI : DecidableEq d.J := d.instDecidableEqJ
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    theorem_8_15_hypothesis52_a (G := G) (M := M) (Ms := Ms) hG hS
  have hInd :
      Section5.inducedFromNonkernelFamily_statement
        (derivedSubgroup M) (Ms.subgroupOf M) S :=
    theorem_8_15_inducedFromNonkernelFamily (G := G) (M := M) (Ms := Ms) hS
  have hCtx :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53
      (L := M)
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := d.W)
      (H := Ms.subgroupOf M)
      (A := section8SubgroupSetPreimage M A)
      (i0 := d.i0)
      (j0 := d.j0)
      (ω := d.omega)
      (σL := d.sigmaM)
      (σ := d.sigma)
      (piChar := d.piChar)
      (xChar := d.xChar)
      (deltaSign := d.deltaSign)
      (τ := d.tau)
      (H_A := d.H_A)
      d.fullHypothesis
  have hpack :=
    Section5.theorem_5_3_b_core
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := d.W)
      (H := Ms.subgroupOf M)
      (A := section8SubgroupSetPreimage M A)
      (i0 := d.i0)
      (j0 := d.j0)
      (ω := d.omega)
      (σL := d.sigmaM)
      (σ := d.sigma)
      (piChar := d.piChar)
      (xChar := d.xChar)
      (deltaSign := d.deltaSign)
      (τ := d.tau)
      (S := S)
      hCtx hS.1 h52a hInd
  rcases hpack with ⟨R5, hsetup, h52a', h52b, h52c, h52d, h52e, _hextra⟩
  exact ⟨hsetup, R5, h52a', h52b, h52c, h52d, h52e⟩

/-- The PF `(5.3)(b)` extra orthogonality obtained inside the Type-P
Hypothesis `(5.2)` branch of PF `(8.15)`.  The existing Hypothesis `(5.2)`
projection keeps only the structural fields; this helper exposes the discarded
orthogonality of the chosen `R`-family to the Section `(3.3)` `ω^σ` family. -/
public theorem theorem_8_15_hypothesis_5_2_extra_of_fullData
    {G : Type u} [Group G] [Finite G]
    {M Ms W1 W2 : Subgroup G}
    {A : Set G}
    {S : Finset (Section1.ClassFunction M)} :
    IsMinCE G →
      (d : section8Hypothesis52FullData M Ms W1 W2 A) →
        section8InducedNonkernelFamily M Ms S →
          letI : Fintype d.I := d.instFintypeI
          letI : Fintype d.J := d.instFintypeJ
          letI : DecidableEq d.I := d.instDecidableEqI
          letI : DecidableEq d.J := d.instDecidableEqJ
          letI : Fintype G := Fintype.ofFinite G
          ∃ R5 : S → Finset (Section1.ClassFunction G),
            Section5.hypothesis_5_2_setup_statement S ∧
              Section5.hypothesis_5_2_a_statement S ∧
                Section5.hypothesis_5_2_b_statement S d.tau ∧
                  Section5.hypothesis_5_2_c_statement S ∧
                    Section5.hypothesis_5_2_d_statement S d.tau R5 ∧
                      Section5.hypothesis_5_2_e_statement S R5 ∧
                        Section5.theorem_5_3_b_extra_statement S R5
                          (Finset.univ.image fun p : d.I × d.J =>
                            d.sigma (d.omega p.1 p.2)) := by
  intro hG d hS
  classical
  letI : Fintype d.I := d.instFintypeI
  letI : Fintype d.J := d.instFintypeJ
  letI : DecidableEq d.I := d.instDecidableEqI
  letI : DecidableEq d.J := d.instDecidableEqJ
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    theorem_8_15_hypothesis52_a (G := G) (M := M) (Ms := Ms) hG hS
  have hInd :
      Section5.inducedFromNonkernelFamily_statement
        (derivedSubgroup M) (Ms.subgroupOf M) S :=
    theorem_8_15_inducedFromNonkernelFamily (G := G) (M := M) (Ms := Ms) hS
  have hCtx :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53
      (L := M)
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := d.W)
      (H := Ms.subgroupOf M)
      (A := section8SubgroupSetPreimage M A)
      (i0 := d.i0)
      (j0 := d.j0)
      (ω := d.omega)
      (σL := d.sigmaM)
      (σ := d.sigma)
      (piChar := d.piChar)
      (xChar := d.xChar)
      (deltaSign := d.deltaSign)
      (τ := d.tau)
      (H_A := d.H_A)
      d.fullHypothesis
  exact
    Section5.theorem_5_3_b_core
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := d.W)
      (H := Ms.subgroupOf M)
      (A := section8SubgroupSetPreimage M A)
      (i0 := d.i0)
      (j0 := d.j0)
      (ω := d.omega)
      (σL := d.sigmaM)
      (σ := d.sigma)
      (piChar := d.piChar)
      (xChar := d.xChar)
      (deltaSign := d.deltaSign)
      (τ := d.tau)
      (S := S)
      hCtx hS.1 h52a hInd

private theorem theorem_8_15_hypothesis52
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    {S : Finset (Section1.ClassFunction M)} :
    IsMinCE G →
    section8Hypothesis52Source M MF Ms A A0 A1 →
    (∃ U W1 W2 : Subgroup G,
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2) →
      section8InducedNonkernelFamily M Ms S →
        ∃ ν : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
          Section5.hypothesis_5_2_statement S ν := by
  intro hG h52Source hWitness hS
  rcases hWitness with ⟨U, W1, W2, hWitness⟩
  rcases h52Source U W1 W2 hWitness with ⟨d⟩
  letI : Fintype d.I := d.instFintypeI
  letI : Fintype d.J := d.instFintypeJ
  letI : DecidableEq d.I := d.instDecidableEqI
  letI : DecidableEq d.J := d.instDecidableEqJ
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    theorem_8_15_hypothesis52_a (G := G) (M := M) (Ms := Ms) hG hS
  have hInd :
      Section5.inducedFromNonkernelFamily_statement
        (derivedSubgroup M) (Ms.subgroupOf M) S :=
    theorem_8_15_inducedFromNonkernelFamily (G := G) (M := M) (Ms := Ms) hS
  have hCtx :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53
      (L := M)
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := d.W)
      (H := Ms.subgroupOf M)
      (A := section8SubgroupSetPreimage M A)
      (i0 := d.i0)
      (j0 := d.j0)
      (ω := d.omega)
      (σL := d.sigmaM)
      (σ := d.sigma)
      (piChar := d.piChar)
      (xChar := d.xChar)
      (deltaSign := d.deltaSign)
      (τ := d.tau)
      (H_A := d.H_A)
      d.fullHypothesis
  have hpack :=
    Section5.theorem_5_3_b_core
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := d.W)
      (H := Ms.subgroupOf M)
      (A := section8SubgroupSetPreimage M A)
      (i0 := d.i0)
      (j0 := d.j0)
      (ω := d.omega)
      (σL := d.sigmaM)
      (σ := d.sigma)
      (piChar := d.piChar)
      (xChar := d.xChar)
      (deltaSign := d.deltaSign)
      (τ := d.tau)
      (S := S)
      hCtx hS.1 h52a hInd
  rcases hpack with ⟨R5, hsetup, h52a', h52b, h52c, h52d, h52e, _hextra⟩
  exact ⟨d.tau, hsetup, R5, h52a', h52b, h52c, h52d, h52e⟩

public theorem theorem_8_15
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 Achoice : Set G)
    (R : G → Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    theorem_8_15_statement M MF Ms A A0 A1 D tildeA tildeA0 tildeA1 Achoice R S := by
  classical
  dsimp [theorem_8_15_statement]
  intro hG hData
  have hNorm : Subgroup.normalizer Achoice = M :=
    theorem_8_15_normalizer_eq (G := G) (M := M) (MF := MF) (Ms := Ms)
      (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
      (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
      (R := R) hG hData
  refine ⟨hNorm, ?_, ?_, ?_⟩
  · exact theorem_8_15_hypothesis2_of_normalizer_eq (G := G) (M := M) (MF := MF)
      (Ms := Ms) (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
      (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
      (R := R) hG hData hNorm
  · exact theorem_8_15_hypothesis46 (G := G) (M := M) (MF := MF) (Ms := Ms)
      (A := A) (A0 := A0) (A1 := A1) (D := D) (tildeA := tildeA)
      (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := Achoice)
      (R := R) hG hData
  · intro h52Source
    exact theorem_8_15_hypothesis52 (G := G) (M := M) (MF := MF) (Ms := Ms)
      (A := A) (A0 := A0) (A1 := A1) (S := S) hG h52Source

end CFSG.Section8
