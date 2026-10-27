module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_11

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_13_statement
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 X : Set G) : Prop :=
  IsMinCE G →
    notation_8_10_source_data M MF Ms A A0 A1 →
      (X = A ∨ X = A0) →
        let D := section8DSet M X
        (∀ x y : G, x ∈ X → y ∈ X →
          section16ConjugateInSubgroup ⊤ x y →
            section16ConjugateInSubgroup M x y) ∧
        D ⊆ A1 ∧
        (∀ x : G, x ∈ D →
          ∃! L : Subgroup G,
            L ∈ section9MaximalSubgroupsContaining
              (Subgroup.centralizer ({x} : Set G))) ∧
        (∀ x : G, x ∈ D →
          ∀ L : Subgroup G,
            L ∈ section9MaximalSubgroupsContaining
              (Subgroup.centralizer ({x} : Set G)) →
              ∃ LF : Subgroup G, supportConclusionDataSource M MF M X x L LF)

/-- Peterfalvi Definition and Notation `(8.14)`. -/


private theorem theorem_8_13_mem_source_X_ne_one
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


public theorem theorem_8_13_typeP_conjugates_hatW_centralizer_le
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∀ y : G,
      y ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) →
        Subgroup.centralizer ({y} : Set G) ≤ M := by
  classical
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hW1Comp, _hUleD, _hUnil,
      _hW1norm, _hCompU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCentralizer, hHatW⟩
  have hW2M : W2 ≤ M := by
    intro z hz
    exact hMF.1.1 (hW2le hz).1
  have hWM : W1 ⊔ W2 ≤ M := sup_le hW1Hall.1 hW2M
  intro y hy c hc
  rcases hy with ⟨w, hw, m, hmM, hy_eq⟩
  let d : G := m⁻¹ * c * m
  have hdCent : d ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcComm : c * y = y * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [hy_eq] at hcComm
    dsimp [d]
    calc
      (m⁻¹ * c * m) * w =
          m⁻¹ * (c * (m * w * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * w * m⁻¹) * c) * m := by rw [hcComm]
      _ = w * (m⁻¹ * c * m) := by group
  have hdNorm : d ∈ Subgroup.normalizer ({w} : Set G) := by
    have hcomm : d * w = w * d :=
      Subgroup.mem_centralizer_singleton_iff.mp hdCent
    have hfix : d * w * d⁻¹ = w := by
      calc
        d * w * d⁻¹ = w * d * d⁻¹ := by rw [hcomm]
        _ = w := by simp [mul_assoc]
    change ∀ z : G, z ∈ ({w} : Set G) ↔ d * z * d⁻¹ ∈ ({w} : Set G)
    intro z
    constructor
    · intro hz
      have hz_eq : z = w := by simpa using hz
      simp [hz_eq, hfix]
    · intro hz
      have hz_eq : d * z * d⁻¹ = w := by simpa using hz
      have hfix_inv : d⁻¹ * w * d = w := by
        have h := congrArg (fun t : G => d⁻¹ * t * d) hfix
        simpa [mul_assoc] using h.symm
      have hz_w : z = w := by
        calc
          z = d⁻¹ * (d * z * d⁻¹) * d := by group
          _ = d⁻¹ * w * d := by rw [hz_eq]
          _ = w := hfix_inv
      simp [hz_w]
  have hnormSingleton :
      Subgroup.normalizer ({w} : Set G) = W1 ⊔ W2 := by
    exact hHatW ({w} : Set G) (Set.singleton_nonempty w) (by
      intro z hz
      have hz_eq : z = w := by simpa using hz
      simpa [hz_eq] using hw)
  have hdW : d ∈ W1 ⊔ W2 := by
    simpa [hnormSingleton] using hdNorm
  have hdM : d ∈ M := hWM hdW
  have hc_eq : c = m * d * m⁻¹ := by
    dsimp [d]
    group
  rw [hc_eq]
  exact M.mul_mem (M.mul_mem hmM hdM) (M.inv_mem hmM)

private theorem theorem_8_13_typeP_D_A0_subset_D_A
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G} {A A0 : Set G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)) :
    section8DSet M A0 ⊆ section8DSet M A := by
  classical
  intro x hxD
  rcases hxD with ⟨hxA0, hxCent_not_le⟩
  rw [hA0] at hxA0
  rcases hxA0 with hxA | hxConj
  · exact ⟨hxA, hxCent_not_le⟩
  · have hxCent_le :
        Subgroup.centralizer ({x} : Set G) ≤ M :=
      theorem_8_13_typeP_conjugates_hatW_centralizer_le
        (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
        hP x hxConj
    exact False.elim (hxCent_not_le hxCent_le)

private theorem theorem_8_13_mem_normalizer_of_conjugateSet_eq
    {G : Type u} [Group G] {X : Set G} {g : G}
    (hconj : section16ConjugateSet X g = X) :
    g ∈ Subgroup.normalizer X := by
  change ∀ x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X
  intro x
  constructor
  · intro hx
    have hxconj : g * x * g⁻¹ ∈ section16ConjugateSet X g :=
      ⟨x, hx, rfl⟩
    simpa [hconj] using hxconj
  · intro hx
    have hxconj : g * x * g⁻¹ ∈ section16ConjugateSet X g := by
      simpa [hconj] using hx
    rcases hxconj with ⟨y, hy, hy_eq⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hy_eq]
        _ = y := by group
    simpa [hxy] using hy

private theorem theorem_8_13_typeP_conjugates_hatW_fusion_in_M
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∀ x y : G,
      x ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) →
      y ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) →
      section16ConjugateInSubgroup ⊤ x y →
        section16ConjugateInSubgroup M x y := by
  classical
  let V : Set G := section16HatW W1 W2
  have hTI : section16TISubsetWithNormalizer V (W1 ⊔ W2) :=
    theorem_8_5_c (G := G) M MF U W1 W2 hP
  have hWleM : W1 ⊔ W2 ≤ M := by
    rcases hP with
      ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hW1Comp, _hUleD, _hUnil,
        _hW1norm, _hCompU, _hMFnotCyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hHatW⟩
    have hW2M : W2 ≤ M := by
      intro z hz
      exact hMF.1.1 (hW2le hz).1
    exact sup_le hW1Hall.1 hW2M
  intro x y hx hy hxy
  rcases hx with ⟨a, ha, m, hmM, hx_eq⟩
  rcases hy with ⟨b, hb, n, hnM, hy_eq⟩
  rcases hxy with ⟨g, _hgTop, hgy⟩
  let t : G := n⁻¹ * g * m
  have hb_t : b = t * a * t⁻¹ := by
    have hmain : n * b * n⁻¹ = g * (m * a * m⁻¹) * g⁻¹ := by
      simpa [hx_eq, hy_eq] using hgy
    calc
      b = n⁻¹ * (n * b * n⁻¹) * n := by group
      _ = n⁻¹ * (g * (m * a * m⁻¹) * g⁻¹) * n := by rw [hmain]
      _ = t * a * t⁻¹ := by
        dsimp [t]
        group
  have hb_inter : b ∈ V ∩ section16ConjugateSet V t := by
    refine ⟨hb, ?_⟩
    exact ⟨a, ha, hb_t⟩
  have hb_ne : b ≠ 1 := by
    intro hb_one
    exact hb.2 (Or.inl (by simp [hb_one]))
  have htW : t ∈ W1 ⊔ W2 := by
    rcases hTI.1 t with hEq | hSub
    · have htNorm : t ∈ Subgroup.normalizer V :=
        theorem_8_13_mem_normalizer_of_conjugateSet_eq (G := G) hEq
      simpa [hTI.2] using htNorm
    · have hb_one : b ∈ ({1} : Set G) := hSub hb_inter
      exact False.elim (hb_ne (by simpa using hb_one))
  have hg_eq : g = n * t * m⁻¹ := by
    dsimp [t]
    group
  have hgM : g ∈ M := by
    rw [hg_eq]
    exact M.mul_mem (M.mul_mem hnM (hWleM htW)) (M.inv_mem hmM)
  exact ⟨g, hgM, hgy⟩

private theorem theorem_8_13_source_D_subset_A1_of_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G} {A A0 A1 X : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hX : X = A ∨ X = A0)
    (hDσ : section8DSet M X ⊆ section10Msigma M) :
    section8DSet M X ⊆ A1 := by
  classical
  have hNotation' := hNotation
  rcases hNotation with ⟨hM, hMF, hMs, hA1, _hCases⟩
  have hMs_eq : Ms = section10Msigma M :=
    theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  intro x hxD
  have hxσ : x ∈ section10Msigma M := hDσ hxD
  have hxne : x ≠ 1 := theorem_8_13_mem_source_X_ne_one
    (G := G) (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0)
    (A1 := A1) hNotation' hX x hxD.1
  rw [hA1, a1Set, hMs_eq]
  exact ⟨hxσ, hxne⟩


public theorem theorem_8_13_source_centralizerUnion_subset_ASet_of_complement
    {G : Type u} [Group G] [Finite G]
    {M D H U : Subgroup G} {A : Set G}
    (hDM : D ≤ M)
    (hH : section16MFSubgroup M H)
    (hH_eq : H = section10Msigma M)
    (hcomp : section12ComplementIn D H U)
    (hA : A = section8CentralizerUnion D H) :
    A ⊆ section16ASet M U := by
  classical
  rcases hH.1 with ⟨hHM, hHnorm, _hHnil, _hHHall⟩
  have hM_le_norm_H : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hHnorm
  have hU_norm_H : U ≤ Subgroup.normalizer (H : Set G) := by
    intro u hu
    exact hM_le_norm_H (hDM (hcomp.2.1 hu))
  have hprod :
      ((U ⊔ H : Subgroup G) : Set G) = ((U : Set G) * (H : Set G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U H hU_norm_H
  have hD_eq : D = U ⊔ H := by
    simpa [sup_comm] using hcomp.2.2.1
  intro y hyA
  rw [hA, section8CentralizerUnion] at hyA
  rcases hyA with ⟨x, hxHsharp, hyCentSharp⟩
  have hxH : x ∈ H := hxHsharp.1
  have hxne : x ≠ 1 := hxHsharp.2
  have hyCent : y ∈ elementCentralizerIn D x := hyCentSharp.1
  have hyD : y ∈ D := by
    simpa [elementCentralizerIn] using hyCent.1
  have hyM : y ∈ M := hDM hyD
  have hySup : y ∈ U ⊔ H := by
    simpa [hD_eq] using hyD
  have hyProdH : y ∈ ((U : Set G) * (H : Set G) : Set G) := by
    have hySupSet : y ∈ ((U ⊔ H : Subgroup G) : Set G) := hySup
    rw [hprod] at hySupSet
    exact hySupSet
  have hyProd :
      y ∈ ((U : Set G) * (section10Msigma M : Set G) : Set G) := by
    simpa [← hH_eq] using hyProdH
  have hyHat : y ∈ section16HatMsigmaSet M := by
    refine ⟨hyM, ?_⟩
    have hxSigma : x ∈ section10Msigma M := by
      simpa [← hH_eq] using hxH
    have hxCentY : x ∈ Subgroup.centralizer ({y} : Set G) := by
      have hyCentX : y ∈ Subgroup.centralizer ({x} : Set G) := by
        simpa [elementCentralizerIn] using hyCent.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hyCentX).symm
    let xC : elementCentralizerIn (section10Msigma M) y :=
      ⟨x, hxSigma, hxCentY⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨xC, ?_⟩
    intro hxC_one
    exact hxne (by simpa [xC] using congrArg Subtype.val hxC_one)
  exact ⟨hyHat, hyProd, hyCentSharp.2⟩

private theorem theorem_8_13_source_centralizerUnion_subset_ASet_of_ambient_complement
    {G : Type u} [Group G] [Finite G]
    {M C H U : Subgroup G} {A : Set G}
    (hCM : C ≤ M)
    (hH : section16MFSubgroup M H)
    (hH_eq : H = section10Msigma M)
    (hcomp : section12ComplementIn M H U)
    (hA : A = section8CentralizerUnion C H) :
    A ⊆ section16ASet M U := by
  classical
  rcases hH.1 with ⟨hHM, hHnorm, _hHnil, _hHHall⟩
  have hM_le_norm_H : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hHnorm
  have hU_norm_H : U ≤ Subgroup.normalizer (H : Set G) := by
    intro u hu
    exact hM_le_norm_H (hcomp.2.1 hu)
  have hprod :
      ((U ⊔ H : Subgroup G) : Set G) = ((U : Set G) * (H : Set G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U H hU_norm_H
  have hM_eq : M = U ⊔ H := by
    simpa [sup_comm] using hcomp.2.2.1
  intro y hyA
  rw [hA, section8CentralizerUnion] at hyA
  rcases hyA with ⟨x, hxHsharp, hyCentSharp⟩
  have hxH : x ∈ H := hxHsharp.1
  have hxne : x ≠ 1 := hxHsharp.2
  have hyCent : y ∈ elementCentralizerIn C x := hyCentSharp.1
  have hyC : y ∈ C := by
    simpa [elementCentralizerIn] using hyCent.1
  have hyM : y ∈ M := hCM hyC
  have hySup : y ∈ U ⊔ H := by
    simpa [hM_eq] using hyM
  have hyProdH : y ∈ ((U : Set G) * (H : Set G) : Set G) := by
    have hySupSet : y ∈ ((U ⊔ H : Subgroup G) : Set G) := hySup
    rw [hprod] at hySupSet
    exact hySupSet
  have hyProd :
      y ∈ ((U : Set G) * (section10Msigma M : Set G) : Set G) := by
    simpa [← hH_eq] using hyProdH
  have hyHat : y ∈ section16HatMsigmaSet M := by
    refine ⟨hyM, ?_⟩
    have hxSigma : x ∈ section10Msigma M := by
      simpa [← hH_eq] using hxH
    have hxCentY : x ∈ Subgroup.centralizer ({y} : Set G) := by
      have hyCentX : y ∈ Subgroup.centralizer ({x} : Set G) := by
        simpa [elementCentralizerIn] using hyCent.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hyCentX).symm
    let xC : elementCentralizerIn (section10Msigma M) y :=
      ⟨x, hxSigma, hxCentY⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨xC, ?_⟩
    intro hxC_one
    exact hxne (by simpa [xC] using congrArg Subtype.val hxC_one)
  exact ⟨hyHat, hyProd, hyCentSharp.2⟩

private theorem theorem_8_13_msigma_nonidentity_mem_ASet
    {G : Type u} [Group G] [Finite G]
    {M U : Subgroup G} {x : G}
    (hxσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1) :
    x ∈ section16ASet M U := by
  classical
  have hxM : x ∈ M := section11_msigma_le M hxσ
  have hxCent : x ∈ elementCentralizerIn (section10Msigma M) x := by
    refine ⟨hxσ, ?_⟩
    change x ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hCentNe :
      elementCentralizerIn (section10Msigma M) x ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hxCent
    exact hxne (by simpa using hxbot)
  refine ⟨⟨hxM, hCentNe⟩, ?_, hxne⟩
  exact ⟨1, U.one_mem, x, hxσ, by simp⟩

private theorem theorem_8_13_bg_typeI_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hSrcI : typeIDefinitionData M MF) :
    section16TypeI M MF := by
  classical
  have hNot :
      ¬ typeIIDefinitionData M MF ∧
        ¬ typeIIIDefinitionData M MF ∧
        ¬ typeIVDefinitionData M MF ∧
        ¬ typeVDefinitionData M MF := by
    rcases hMs with hI | hII | hIII | hIV | hV
    · rcases hI with ⟨_hI, hnotII, hnotIII, hnotIV, hnotV, _hMs⟩
      exact ⟨hnotII, hnotIII, hnotIV, hnotV⟩
    · exact False.elim (hII.1 hSrcI)
    · exact False.elim (hIII.1 hSrcI)
    · exact False.elim (hIV.1 hSrcI)
    · exact False.elim (hV.1 hSrcI)
  rcases section16_type_exhaustive_of_maximal (G := G) hM hMF with
    hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
  · exact hTypeI
  · exact False.elim
      (hNot.1 (theorem_8_8_typeII_to_source_public (G := G) hM hMF hTypeII))
  · exact False.elim
      (hNot.2.1 (theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
  · exact False.elim
      (hNot.2.2.1 (theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
  · exact False.elim
      (hNot.2.2.2 (theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))

private theorem theorem_8_13_bg_typeII_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hSrcII : typeIIDefinitionData M MF) :
    section16TypeII M MF := by
  classical
  have hNot :
      ¬ typeIDefinitionData M MF ∧
        ¬ typeIIIDefinitionData M MF ∧
        ¬ typeIVDefinitionData M MF ∧
        ¬ typeVDefinitionData M MF := by
    rcases hMs with hI | hII | hIII | hIV | hV
    · exact False.elim (hI.2.1 hSrcII)
    · rcases hII with ⟨hnotI, _hII, hnotIII, hnotIV, hnotV, _hMs⟩
      exact ⟨hnotI, hnotIII, hnotIV, hnotV⟩
    · exact False.elim (hIII.2.1 hSrcII)
    · exact False.elim (hIV.2.1 hSrcII)
    · exact False.elim (hV.2.1 hSrcII)
  rcases section16_type_exhaustive_of_maximal (G := G) hM hMF with
    hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
  · exact False.elim
      (hNot.1 (theorem_8_8_typeI_to_source_public (G := G) hM hMF hTypeI))
  · exact hTypeII
  · exact False.elim
      (hNot.2.1 (theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
  · exact False.elim
      (hNot.2.2.1 (theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
  · exact False.elim
      (hNot.2.2.2 (theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))

private theorem theorem_8_13_typeP_A_subset_ASet
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (_hP : typePDefinitionData M MF U W1 W2)
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hLate :
      (typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
          typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    ∃ K Uc : Subgroup G, section16KUData M K Uc ∧ A ⊆ section16ASet M Uc := by
  classical
  rcases hNotation with ⟨hM, hMF, hMs, hA1, _hCases⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hMs_eq_sigma : Ms = section10Msigma M :=
    theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  have hSigmaSub :
      ∀ {K Uc : Subgroup G}, section16KUData M K Uc →
        A = A1 → A ⊆ section16ASet M Uc := by
    intro K Uc _hKU hAeqA1 x hxA
    have hxA1 : x ∈ A1 := by
      simpa [hAeqA1] using hxA
    have hxSigmaSharp : x ∈ a1Set Ms := by
      simpa [hA1] using hxA1
    rw [a1Set, hMs_eq_sigma] at hxSigmaSharp
    exact theorem_8_13_msigma_nonidentity_mem_ASet (G := G)
      hxSigmaSharp.1 hxSigmaSharp.2
  rcases hMs with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨hSrcI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs_eq_MF⟩
    have hTypeI : section16TypeI M MF :=
      theorem_8_13_bg_typeI_of_source (G := G) hM hMF
        (Or.inl ⟨hSrcI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs_eq_MF⟩) hSrcI
    rcases hSrcI with ⟨UI, U1, U0, hF, _hAlt⟩
    rcases hF with
      ⟨_hsolv, _hodd, _hMFsrc, _hMFpos, _hMFlt, _hUne, hcompM, _hU1le,
        _hU1comm, _hU1norm, _hCent, _hU0le, _hExp, _hFrob⟩
    rcases section16_typeI_KUData_of_complement (G := G) hM hMF hTypeI hcompM with
      ⟨hKU, hMF_eq⟩
    have hA_MF : A = section8CentralizerUnion D MF := by
      simpa [D, hMs_eq_MF] using hA
    refine ⟨⊥, UI, hKU, ?_⟩
    exact theorem_8_13_source_centralizerUnion_subset_ASet_of_ambient_complement
      (G := G) (M := M) (C := D) (H := MF) (U := UI) (A := A)
      hDleM hMF hMF_eq hcompM hA_MF
  · rcases hII with ⟨hnotI, hSrcII, hnotIII, hnotIV, hnotV, hMs_eq_MF⟩
    have hTypeII : section16TypeII M MF :=
      theorem_8_13_bg_typeII_of_source (G := G) hM hMF
        (Or.inr (Or.inl ⟨hnotI, hSrcII, hnotIII, hnotIV, hnotV, hMs_eq_MF⟩))
        hSrcII
    rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, Uc, hKU15⟩
    have hKU : section16KUData M K Uc := by
      simpa [section16KUData] using hKU15
    have hCanonical :=
      section16_typeII_canonical_caseP2_data (G := G) hM hMF hKU hTypeII
    have hCompCanonical : section12ComplementIn D MF Uc := by
      simpa [D] using hCanonical.1.2.2.1
    have hMF_eq : MF = section10Msigma M := hCanonical.2.2.2.2.2
    have hA_MF : A = section8CentralizerUnion D MF := by
      simpa [D, hMs_eq_MF] using hA
    refine ⟨K, Uc, hKU, ?_⟩
    exact theorem_8_13_source_centralizerUnion_subset_ASet_of_complement
      (G := G) (M := M) (D := D) (H := MF) (U := Uc) (A := A)
      hDleM hMF hMF_eq hCompCanonical hA_MF
  · rcases hIII with ⟨_hnotI, _hnotII, hSrcIII, _hnotIV, _hnotV, _hMs_eq_D⟩
    rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, Uc, hKU15⟩
    have hKU : section16KUData M K Uc := by
      simpa [section16KUData] using hKU15
    exact ⟨K, Uc, hKU,
      hSigmaSub hKU (hLate (Or.inl hSrcIII)).2⟩
  · rcases hIV with ⟨_hnotI, _hnotII, _hnotIII, hSrcIV, _hnotV, _hMs_eq_D⟩
    rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, Uc, hKU15⟩
    have hKU : section16KUData M K Uc := by
      simpa [section16KUData] using hKU15
    exact ⟨K, Uc, hKU,
      hSigmaSub hKU (hLate (Or.inr (Or.inl hSrcIV))).2⟩
  · rcases hV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, hSrcV, _hMs_eq_MF⟩
    rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, Uc, hKU15⟩
    have hKU : section16KUData M K Uc := by
      simpa [section16KUData] using hKU15
    exact ⟨K, Uc, hKU,
      hSigmaSub hKU (hLate (Or.inr (Or.inr hSrcV))).2⟩

private theorem theorem_8_13_source_core_conclusions_of_theoremII_subset
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms K U : Subgroup G} {A A0 A1 X Y : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hX : X = A ∨ X = A0)
    (hKU : section16KUData M K U)
    (hYChoice : section16AChoice M K U Y)
    (hXY : X ⊆ Y) :
    let D := section8DSet M X
    (∀ x y : G, x ∈ X → y ∈ X →
      section16ConjugateInSubgroup ⊤ x y →
        section16ConjugateInSubgroup M x y) ∧
    D ⊆ A1 ∧
    (∀ x : G, x ∈ D →
      ∃! L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G))) := by
  classical
  have hNotation' := hNotation
  rcases hNotation with ⟨hM, hMF, _hMs, _hA1, _hCases⟩
  let DY := section16TheoremIIDSet M Y
  have hII := theorem_16_II (G := G) hM hMF hKU hYChoice
  have hDsource_to_DY : section8DSet M X ⊆ DY := by
    intro x hxD
    exact ⟨hXY hxD.1,
      theorem_8_13_mem_source_X_ne_one (G := G) hNotation' hX x hxD.1,
      hxD.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxX hyX hxy
    exact hII.2.2.1 x y (hXY hxX) (hXY hyX) hxy
  · refine theorem_8_13_source_D_subset_A1_of_msigma hNotation' hX ?_
    intro x hxD
    exact theorem_16_II_mem_msigma_of_mem_D (G := G) hM hMF hKU hYChoice x
      (hDsource_to_DY hxD)
  · intro x hxD
    rcases hII.2.1 x (hDsource_to_DY hxD) with ⟨N, hNuniq⟩
    refine ⟨N, ?_, ?_⟩
    · simp [hNuniq]
    · intro L hL
      have hLmem : L ∈ ({N} : Set (Subgroup G)) := by
        simpa [hNuniq] using hL
      simpa using hLmem

private theorem theorem_8_13_typeI_source_core_conclusions
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G} {A A0 A1 X : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hSrcI : typeIDefinitionData M MF)
    (hA : A = section8CentralizerUnion M MF)
    (hA0 : A0 = A)
    (hX : X = A ∨ X = A0) :
    let D := section8DSet M X
    (∀ x y : G, x ∈ X → y ∈ X →
      section16ConjugateInSubgroup ⊤ x y →
        section16ConjugateInSubgroup M x y) ∧
    D ⊆ A1 ∧
    (∀ x : G, x ∈ D →
      ∃! L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G))) := by
  classical
  rcases hNotation with ⟨hM, hMF, hMs, _hA1, _hCases⟩
  have hTypeI : section16TypeI M MF :=
    theorem_8_13_bg_typeI_of_source (G := G) hM hMF hMs hSrcI
  rcases hSrcI with ⟨U, U1, U0, hF, _hAlt⟩
  rcases hF with
    ⟨_hsolv, _hodd, _hMFsrc, _hMFpos, _hMFlt, _hUne, hcomp, _hU1le,
      _hU1comm, _hU1norm, _hCent, _hU0le, _hExp, _hFrob⟩
  rcases section16_typeI_KUData_of_complement (G := G) hM hMF hTypeI hcomp with
    ⟨hKU, hMF_eq⟩
  have hAsub : A ⊆ section16ASet M U :=
    theorem_8_13_source_centralizerUnion_subset_ASet_of_complement
      (G := G) (M := M) (D := M) (H := MF) (U := U) (A := A)
      le_rfl hMF hMF_eq hcomp hA
  have hXsub : X ⊆ section16ASet M U := by
    intro x hx
    rcases hX with rfl | rfl
    · exact hAsub hx
    · exact hAsub (by simpa [hA0] using hx)
  exact theorem_8_13_source_core_conclusions_of_theoremII_subset
    (G := G) (M := M) (MF := MF) (Ms := Ms) (K := (⊥ : Subgroup G))
    (U := U) (A := A) (A0 := A0) (A1 := A1) (X := X)
    (Y := section16ASet M U) ⟨hM, hMF, hMs, _hA1, _hCases⟩ hX hKU
    (Or.inl rfl) hXsub

private theorem theorem_8_13_semidirect_of_mf_complement
    {G : Type u} [Group G] [Finite G]
    {L LF C : Subgroup G}
    (hLF : section16MFSubgroup L LF)
    (hcomp : section12ComplementIn L LF C) :
    section8SemidirectProductIn L LF C := by
  rcases hLF.1 with ⟨hLFL, hLFnorm, _hLFnil, _hLFHall⟩
  exact ⟨hcomp, ⟨hLFL, hLFnorm⟩⟩

private theorem theorem_8_13_semidirect_of_normalComplementIn
    {G : Type u} [Group G] [Finite G]
    {C H R : Subgroup G}
    (hcomp : section16NormalComplementIn H C R) :
    section8SemidirectProductIn C R H := by
  classical
  rcases hcomp with ⟨hHC, hRC, hRnorm, hIsComp⟩
  refine ⟨?_, ⟨hRC, hRnorm⟩⟩
  refine ⟨hRC, hHC, ?_, ?_⟩
  · apply le_antisymm
    · intro x hxC
      let xC : C := ⟨x, hxC⟩
      have hxTop : xC ∈ (⊤ : Subgroup C) := by simp
      have hxSup : xC ∈ R.subgroupOf C ⊔ H.subgroupOf C := by
        simp [hIsComp.symm.sup_eq_top]
      have hxSub : xC ∈ (R ⊔ H).subgroupOf C := by
        have hsub_eq :
            (R ⊔ H).subgroupOf C = R.subgroupOf C ⊔ H.subgroupOf C := by
          exact Subgroup.subgroupOf_sup (A := R) (A' := H) (B := C) hRC hHC
        simpa [hsub_eq] using hxSup
      simpa [xC, Subgroup.mem_subgroupOf] using hxSub
    · exact sup_le hRC hHC
  · rw [Subgroup.disjoint_def]
    intro x hxR hxH
    let xC : C := ⟨x, hRC hxR⟩
    have hxRloc : xC ∈ R.subgroupOf C := by
      simpa [xC, Subgroup.mem_subgroupOf] using hxR
    have hxHloc : xC ∈ H.subgroupOf C := by
      simpa [xC, Subgroup.mem_subgroupOf] using hxH
    have hxbot : xC ∈ (⊥ : Subgroup C) :=
      Subgroup.disjoint_def.mp hIsComp.symm.disjoint hxRloc hxHloc
    change (xC : G) = (1 : G)
    exact congrArg Subtype.val (by simpa using hxbot)

private theorem theorem_8_13_semidirect_centralizer_of_theoremDComplement
    {G : Type u} [Group G] [Finite G]
    {M LF : Subgroup G} {x : G}
    (hD : section16TheoremDComplement M x (elementCentralizerIn LF x)) :
    section8SemidirectProductIn (Subgroup.centralizer ({x} : Set G))
      (elementCentralizerIn LF x) (elementCentralizerIn M x) := by
  exact theorem_8_13_semidirect_of_normalComplementIn (G := G) hD.2.1

public theorem theorem_8_13_source_typeI_mem_A_diff_A1_of_ASet
    {G : Type u} [Group G] [Finite G]
    {L U : Subgroup G} {x : G}
    (hxA : x ∈ section16ASet L U \ (section10Msigma L : Set G)) :
    x ∈ section8CentralizerUnion L (section10Msigma L) \
      a1Set (section10Msigma L) := by
  classical
  rcases hxA with ⟨hxASet, hxσ_not⟩
  rcases hxASet with ⟨hxHat, _hxProd, _hxneA⟩
  rcases hxHat with ⟨hxL, hxCent_ne⟩
  have hxne : x ≠ 1 := by
    intro hxone
    exact hxσ_not (by simp [hxone])
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hxCent_ne with ⟨zC, hzCne⟩
  let z : G := zC
  have hzσ : z ∈ section10Msigma L := zC.property.1
  have hzCentX : z ∈ Subgroup.centralizer ({x} : Set G) := zC.property.2
  have hzne : z ≠ 1 := by
    intro hz
    exact hzCne (by
      apply Subtype.ext
      simpa [z] using hz)
  have hxCentZ : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hzCentX ⊢
    exact hzCentX.symm
  refine ⟨?_, ?_⟩
  · refine ⟨z, ⟨hzσ, hzne⟩, ?_⟩
    exact ⟨⟨hxL, hxCentZ⟩, hxne⟩
  · intro hxA1
    exact hxσ_not hxA1.1

private theorem theorem_8_13_source_typeII_mem_A_diff_A1_of_ASet
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {L K U : Subgroup G} {x : G}
    (hL : L ∈ section9MaximalSubgroups G)
    (hLF : section16MFSubgroup L (section10Msigma L))
    (hKU : section16KUData L K U)
    (hType : section16TypeII L (section10Msigma L))
    (hxA : x ∈ section16ASet L U \ (section10Msigma L : Set G)) :
    x ∈ section8CentralizerUnion (ambientDerivedSubgroup L) (section10Msigma L) \
      a1Set (section10Msigma L) := by
  classical
  rcases hxA with ⟨hxASet, hxσ_not⟩
  rcases hxASet with ⟨hxHat, hxProd, _hxneA⟩
  rcases hxHat with ⟨_hxL, hxCent_ne⟩
  have hCommon :
      section16TypeCommon L (section10Msigma L) U K (section16Kstar L K) :=
    (section16_typeII_canonical_caseP2_data
      (G := G) hL hLF hKU hType).1
  rcases hCommon with
    ⟨_hHallD, hSigmaD, hCompSigmaU, _hUnil, _hW1norm, _hW1cyc,
      _hW1card, _hSigmanotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6, _hW2Second⟩
  have hxD : x ∈ ambientDerivedSubgroup L := by
    rcases hxProd with ⟨u, huU, s, hsSigma, hx_eq⟩
    rw [← hx_eq]
    exact (ambientDerivedSubgroup L).mul_mem
      (hCompSigmaU.2.1 huU) (hSigmaD hsSigma)
  have hxne : x ≠ 1 := by
    intro hxone
    exact hxσ_not (by simp [hxone])
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hxCent_ne with ⟨zC, hzCne⟩
  let z : G := zC
  have hzσ : z ∈ section10Msigma L := zC.property.1
  have hzCentX : z ∈ Subgroup.centralizer ({x} : Set G) := zC.property.2
  have hzne : z ≠ 1 := by
    intro hz
    exact hzCne (by
      apply Subtype.ext
      simpa [z] using hz)
  have hxCentZ : x ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hzCentX ⊢
    exact hzCentX.symm
  refine ⟨?_, ?_⟩
  · refine ⟨z, ⟨hzσ, hzne⟩, ?_⟩
    exact ⟨⟨hxD, hxCentZ⟩, hxne⟩
  · intro hxA1
    exact hxσ_not hxA1.1

private theorem theorem_8_13_source_frobenius_of_bg
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hFrob : section16FrobeniusWithCyclicComplement M MF) :
    section8FrobeniusGroupWithKernel M MF := by
  rcases hFrob with ⟨E, hcomp, hFrobJoin, _hCyc⟩
  exact ⟨E, hcomp, hFrobJoin⟩

private theorem theorem_8_13_support_conclusion_of_theoremII_subset
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms K U : Subgroup G} {A A0 A1 X Y : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hX : X = A ∨ X = A0)
    (hKU : section16KUData M K U)
    (hYChoice : section16AChoice M K U Y)
    (hXY : X ⊆ Y) :
    ∀ x : G, x ∈ section8DSet M X →
      ∀ L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) →
          ∃ LF : Subgroup G, supportConclusionDataSource M MF M X x L LF := by
  classical
  rcases hNotation with ⟨hM, hMF, hMs, hA1, hCases⟩
  intro x hxD L hL
  have hNotation' : notation_8_10_source_data M MF Ms A A0 A1 :=
    ⟨hM, hMF, hMs, hA1, hCases⟩
  have hxDY : x ∈ section16TheoremIIDSet M Y := by
    exact ⟨hXY hxD.1,
      theorem_8_13_mem_source_X_ne_one (G := G) hNotation' hX x hxD.1,
      hxD.2⟩
  have hII := theorem_16_II (G := G) hM hMF hKU hYChoice
  rcases theorem_16_II_canonical_D_data
      (G := G) hM hMF hKU hYChoice hxDY with
    ⟨NK, NU, hNcont, hNMF, hNKU, hxA, hNtype, hNcomp, hNTypeII⟩
  rcases hII.2.1 x hxDY with ⟨N0, huniq0⟩
  have hN_eq_N0 : section14N x = N0 := by
    have hmem : section14N x ∈ ({N0} : Set (Subgroup G)) := by
      simpa [huniq0] using hNcont
    simpa using hmem
  subst N0
  have huniqN :
      section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) =
        {section14N x} := by
    simpa using huniq0
  have hL_eq_N : L = section14N x := by
    have hmem : L ∈ ({section14N x} : Set (Subgroup G)) := by
      simpa [huniqN] using hL
    simpa using hmem
  subst L
  refine ⟨section10Msigma (section14N x), ?_⟩
  dsimp [supportConclusionDataSource]
  refine ⟨hNcont.1, hNMF, huniqN, ?_, ?_, ?_, ?_⟩
  · exact theorem_8_13_semidirect_of_mf_complement
      (G := G) hNMF hNcomp
  · exact theorem_8_13_semidirect_centralizer_of_theoremDComplement
      (G := G)
      (theorem_16_II_canonical_theoremDComplement
        (G := G) hM hMF hKU hYChoice hxDY)
  · intro y hyX
    exact theorem_16_II_canonical_support_coprime
      (G := G) hM hMF hKU hYChoice hxDY y
      ⟨hXY hyX, theorem_8_13_mem_source_X_ne_one
        (G := G) hNotation' hX y hyX⟩
  · rcases hNtype with hNtypeI | hNtypeII
    · left
      refine ⟨theorem_8_8_typeI_to_source_public
        (G := G) hNcont.1 hNMF hNtypeI, ?_⟩
      exact theorem_8_13_source_typeI_mem_A_diff_A1_of_ASet
        (G := G) hxA
    · right
      refine ⟨theorem_8_8_typeII_to_source_public
        (G := G) hNcont.1 hNMF hNtypeII, ?_, ?_⟩
      · exact theorem_8_13_source_typeII_mem_A_diff_A1_of_ASet
          (G := G) hNcont.1 hNMF hNKU hNtypeII hxA
      · exact theorem_8_13_source_frobenius_of_bg (G := G)
          (hNTypeII hNtypeII).1

private theorem theorem_8_13_typeI_source_conclusions
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G} {A A0 A1 X : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hSrcI : typeIDefinitionData M MF)
    (hA : A = section8CentralizerUnion M MF)
    (hA0 : A0 = A)
    (hX : X = A ∨ X = A0) :
    let D := section8DSet M X
    (∀ x y : G, x ∈ X → y ∈ X →
      section16ConjugateInSubgroup ⊤ x y →
        section16ConjugateInSubgroup M x y) ∧
    D ⊆ A1 ∧
    (∀ x : G, x ∈ D →
      ∃! L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G))) ∧
    (∀ x : G, x ∈ D →
      ∀ L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) →
          ∃ LF : Subgroup G, supportConclusionDataSource M MF M X x L LF) := by
  classical
  have hNotation' := hNotation
  rcases hNotation with ⟨hM, hMF, hMs, _hA1, _hCases⟩
  have hCore :=
    theorem_8_13_typeI_source_core_conclusions
      (G := G) (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0)
      (A1 := A1) (X := X) hNotation' hSrcI hA hA0 hX
  have hTypeI : section16TypeI M MF :=
    theorem_8_13_bg_typeI_of_source (G := G) hM hMF hMs hSrcI
  rcases hSrcI with ⟨U, U1, U0, hF, _hAlt⟩
  rcases hF with
    ⟨_hsolv, _hodd, _hMFsrc, _hMFpos, _hMFlt, _hUne, hcomp, _hU1le,
      _hU1comm, _hU1norm, _hCent, _hU0le, _hExp, _hFrob⟩
  rcases section16_typeI_KUData_of_complement (G := G) hM hMF hTypeI hcomp with
    ⟨hKU, hMF_eq⟩
  have hAsub : A ⊆ section16ASet M U :=
    theorem_8_13_source_centralizerUnion_subset_ASet_of_complement
      (G := G) (M := M) (D := M) (H := MF) (U := U) (A := A)
      le_rfl hMF hMF_eq hcomp hA
  have hXsub : X ⊆ section16ASet M U := by
    intro x hx
    rcases hX with rfl | rfl
    · exact hAsub hx
    · exact hAsub (by simpa [hA0] using hx)
  have hSupport :=
    theorem_8_13_support_conclusion_of_theoremII_subset
      (G := G) (M := M) (MF := MF) (Ms := Ms) (K := (⊥ : Subgroup G))
      (U := U) (A := A) (A0 := A0) (A1 := A1) (X := X)
      (Y := section16ASet M U) hNotation' hX hKU (Or.inl rfl) hXsub
  exact ⟨hCore.1, hCore.2.1, hCore.2.2, hSupport⟩

private theorem theorem_8_13_typeP_A_source_conclusions
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2)
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hLate :
      (typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
          typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    let D := section8DSet M A
    (∀ x y : G, x ∈ A → y ∈ A →
      section16ConjugateInSubgroup ⊤ x y →
        section16ConjugateInSubgroup M x y) ∧
    D ⊆ A1 ∧
    (∀ x : G, x ∈ D →
      ∃! L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G))) ∧
    (∀ x : G, x ∈ D →
      ∀ L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) →
          ∃ LF : Subgroup G, supportConclusionDataSource M MF M A x L LF) := by
  classical
  rcases theorem_8_13_typeP_A_subset_ASet
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (A := A) (A0 := A0) (A1 := A1)
      hNotation hP hA hLate with
    ⟨K, Uc, hKU, hAsub⟩
  have hCore :=
    theorem_8_13_source_core_conclusions_of_theoremII_subset
      (G := G) (M := M) (MF := MF) (Ms := Ms) (K := K) (U := Uc)
      (A := A) (A0 := A0) (A1 := A1) (X := A)
      (Y := section16ASet M Uc) hNotation (Or.inl rfl) hKU (Or.inl rfl) hAsub
  have hSupport :=
    theorem_8_13_support_conclusion_of_theoremII_subset
      (G := G) (M := M) (MF := MF) (Ms := Ms) (K := K) (U := Uc)
      (A := A) (A0 := A0) (A1 := A1) (X := A)
      (Y := section16ASet M Uc) hNotation (Or.inl rfl) hKU (Or.inl rfl) hAsub
  exact ⟨hCore.1, hCore.2.1, hCore.2.2, hSupport⟩

private theorem theorem_8_13_typeP_A0_D_subset_A1_unique
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2)
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
    (hLate :
      (typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
          typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    let D := section8DSet M A0
    D ⊆ A1 ∧
      (∀ x : G, x ∈ D →
        ∃! L : Subgroup G,
          L ∈ section9MaximalSubgroupsContaining
            (Subgroup.centralizer ({x} : Set G))) := by
  classical
  have hAconcl :=
    theorem_8_13_typeP_A_source_conclusions
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP hA hLate
  have hDsub :
      section8DSet M A0 ⊆ section8DSet M A :=
    theorem_8_13_typeP_D_A0_subset_D_A
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (A := A) (A0 := A0) hP hA0
  exact ⟨
    fun _x hxD => hAconcl.2.1 (hDsub hxD),
    fun x hxD => hAconcl.2.2.1 x (hDsub hxD)⟩

private theorem theorem_8_13_typeP_W2_le_centralizer_W1
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ Subgroup.centralizer (W1 : Set G) := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      hcentW1, _hnormX⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · have hyCent : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
      simpa [hcentW1 x hx hx1] using hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hyCent.2).symm

private theorem theorem_8_13_typeP_W2_le_ambientDerived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ ambientDerivedSubgroup M := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  have hDerDer_le_Der :
      section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
    simpa [section16SecondDerivedSubgroup] using
      (section12_ambientDerivedSubgroup_le (G := G)
        (E := ambientDerivedSubgroup M))
  intro z hz
  exact hDerDer_le_Der (hW2le hz).2

private theorem theorem_8_13_typeP_W2_le_Ms
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ Ms := by
  rcases hNotation with ⟨_hM, _hMF, hMs, _hA1, _hCases⟩
  rcases hP with
    ⟨_hMFP, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le,
      _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hP0 : typePDefinitionData M MF U W1 W2 := by
    exact ⟨_hMFP, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le,
      _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hW2MF : W2 ≤ MF := fun z hz => (hW2le hz).1
  have hW2D : W2 ≤ ambientDerivedSubgroup M :=
    theorem_8_13_typeP_W2_le_ambientDerived
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
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

private theorem theorem_8_13_typeP_W2_nontrivial
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∃ z : G, z ∈ W2 ∧ z ≠ 1 := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, hW2ne,
      _hcentW1, _hnormX⟩
  by_contra hnone
  apply hW2ne
  apply le_antisymm
  · intro z hz
    have hz_one : z = 1 := by
      by_contra hz_ne
      exact hnone ⟨z, hz, hz_ne⟩
    simp [hz_one]
  · exact bot_le

private theorem theorem_8_13_typeP_W_isMulCommutative
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    IsMulCommutative (W1 ⊔ W2 : Subgroup G) := by
  classical
  rcases hP with
    ⟨_hMF, hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le, hW2cyc, _hW2ne,
      hcentW1, _hnormX⟩
  have hW2centW1 : W2 ≤ Subgroup.centralizer (W1 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    by_cases hx1 : x = 1
    · simp [hx1]
    · have hyCent : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
        simpa [hcentW1 x hx hx1] using hy
      exact (Subgroup.mem_centralizer_singleton_iff.mp hyCent.2).symm
  letI : IsCyclic W1 := hW1cyc
  letI : IsCyclic W2 := hW2cyc
  let W : Subgroup G := W1 ⊔ W2
  let W1W : Subgroup W := W1.subgroupOf W
  let W2W : Subgroup W := W2.subgroupOf W
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
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxTop : x ∈ W1W ⊔ W2W := by simp [hW1W_W2W_top]
  have hyTop : y ∈ W1W ⊔ W2W := by simp [hW1W_W2W_top]
  rcases (Subgroup.mem_sup_of_normal_right (s := W1W) (t := W2W) (x := x)).1
      hxTop with
    ⟨aW, haW, bW, hbW, hxab⟩
  rcases (Subgroup.mem_sup_of_normal_right (s := W1W) (t := W2W) (x := y)).1
      hyTop with
    ⟨cW, hcW, dW, hdW, hycd⟩
  let a : G := aW
  let b : G := bW
  let c : G := cW
  let d : G := dW
  have haW1 : a ∈ W1 := by simpa [a, W1W, Subgroup.mem_subgroupOf] using haW
  have hbW2 : b ∈ W2 := by simpa [b, W2W, Subgroup.mem_subgroupOf] using hbW
  have hcW1 : c ∈ W1 := by simpa [c, W1W, Subgroup.mem_subgroupOf] using hcW
  have hdW2 : d ∈ W2 := by simpa [d, W2W, Subgroup.mem_subgroupOf] using hdW
  have hx_eq : (x : G) = a * b := by
    have hval := congrArg (fun z : W => (z : G)) hxab
    simpa [a, b] using hval.symm
  have hy_eq : (y : G) = c * d := by
    have hval := congrArg (fun z : W => (z : G)) hycd
    simpa [c, d] using hval.symm
  have hac : a * c = c * a :=
    setLike_mul_comm (s := W1) haW1 hcW1
  have hbd : b * d = d * b :=
    setLike_mul_comm (s := W2) hbW2 hdW2
  have hbc : b * c = c * b :=
    (Subgroup.mem_centralizer_iff.mp (hW2centW1 hbW2) c hcW1).symm
  have had : a * d = d * a :=
    Subgroup.mem_centralizer_iff.mp (hW2centW1 hdW2) a haW1
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  rw [hx_eq, hy_eq]
  calc
    (a * b) * (c * d) = a * (b * c) * d := by simp [mul_assoc]
    _ = a * (c * b) * d := by rw [hbc]
    _ = (a * c) * (b * d) := by simp [mul_assoc]
    _ = (c * a) * (d * b) := by rw [hac, hbd]
    _ = c * (a * d) * b := by simp [mul_assoc]
    _ = c * (d * a) * b := by rw [had]
    _ = (c * d) * (a * b) := by simp [mul_assoc]

private theorem theorem_8_13_typeP_W_le_elementCentralizerIn_of_W2
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G} {z : G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hzW2 : z ∈ W2) :
    W1 ⊔ W2 ≤ elementCentralizerIn M z := by
  classical
  rcases hP with
    ⟨hMF, hW1cyc, hW1ne, _hW1hall, hcompMW1, hUleD, hUnil, hW1normU,
      hcompDU, hMFnotcyc, hM2le, hFitEq, hFitLeD, hW2le, hW2cyc, hW2ne,
      hcentW1, hnormX⟩
  have hP0 : typePDefinitionData M MF U W1 W2 := by
    exact ⟨hMF, hW1cyc, hW1ne, _hW1hall, hcompMW1, hUleD, hUnil, hW1normU,
      hcompDU, hMFnotcyc, hM2le, hFitEq, hFitLeD, hW2le, hW2cyc, hW2ne,
      hcentW1, hnormX⟩
  rcases hMF.1 with ⟨hMFM, _hMFnormalM, _hMFnil, _hMFhallM⟩
  have hW1M : W1 ≤ M := hcompMW1.2.1
  have hW2M : W2 ≤ M := fun y hy => hMFM (hW2le hy).1
  have hWM : W1 ⊔ W2 ≤ M := sup_le hW1M hW2M
  letI : IsMulCommutative (W1 ⊔ W2 : Subgroup G) :=
    theorem_8_13_typeP_W_isMulCommutative
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
  intro a ha
  refine ⟨hWM ha, ?_⟩
  change a ∈ Subgroup.centralizer ({z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact setLike_mul_comm
    (s := W1 ⊔ W2) ha ((le_sup_right : W2 ≤ W1 ⊔ W2) hzW2)

private theorem theorem_8_13_typeP_hatW_not_mem_ambientDerived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∀ w : G, w ∈ section16HatW W1 W2 → w ∉ ambientDerivedSubgroup M := by
  classical
  have hP0 := hP
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  let W : Subgroup G := W1 ⊔ W2
  let D : Subgroup G := ambientDerivedSubgroup M
  have hW2D : W2 ≤ D := by
    intro z hz
    have hDerDer_le_Der :
        section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
      simpa [section16SecondDerivedSubgroup] using
        (section12_ambientDerivedSubgroup_le (G := G)
          (E := ambientDerivedSubgroup M))
    exact hDerDer_le_Der (hW2le hz).2
  have hW2_norm_W1 : W1 ≤ Subgroup.normalizer (W2 : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hcomm : a * z = z * a :=
        Subgroup.mem_centralizer_iff.mp
          (theorem_8_13_typeP_W2_le_centralizer_W1
            (M := M) (MF := MF) (U := U) hP0 hz) a ha
      have hconj : a * z * a⁻¹ = z := by
        calc
          a * z * a⁻¹ = z * a * a⁻¹ := by rw [hcomm]
          _ = z := by simp [mul_assoc]
      simpa [hconj] using hz
    · intro hz
      let z' : G := a * z * a⁻¹
      have hz'W2 : z' ∈ W2 := by simpa [z'] using hz
      have hcomm' : a * z' = z' * a :=
        Subgroup.mem_centralizer_iff.mp
          (theorem_8_13_typeP_W2_le_centralizer_W1
            (M := M) (MF := MF) (U := U) hP0 hz'W2) a ha
      have hconj : a⁻¹ * z' * a = z' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hz_eq : z = z' := by
        calc
          z = a⁻¹ * z' * a := by simp [z', mul_assoc]
          _ = z' := hconj
      simpa [hz_eq] using hz'W2
  let W1W : Subgroup W := W1.subgroupOf W
  let W2W : Subgroup W := W2.subgroupOf W
  haveI : W2W.Normal := by
    simpa [W, W2W] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := W2) hW2_norm_W1)
  have hWtop : W1W ⊔ W2W = ⊤ := by
    calc
      W1W ⊔ W2W = W.subgroupOf W := by
        symm
        exact Subgroup.subgroupOf_sup (A := W1) (A' := W2) (B := W)
          (by simp [W]) (by simp [W])
      _ = ⊤ := by simp
  intro w hw hwD
  let wW : W := ⟨w, hw.1⟩
  have hwTop : wW ∈ W1W ⊔ W2W := by simp [hWtop]
  rcases (Subgroup.mem_sup_of_normal_right (s := W1W) (t := W2W) (x := wW)).1
      hwTop with
    ⟨aW, haW, bW, hbW, hw_eq_sub⟩
  let a : G := aW
  let b : G := bW
  have haW1 : a ∈ W1 := by simpa [a, W1W, Subgroup.mem_subgroupOf] using haW
  have hbW2 : b ∈ W2 := by simpa [b, W2W, Subgroup.mem_subgroupOf] using hbW
  have hw_eq : w = a * b := by
    have hval := congrArg (fun z : W => (z : G)) hw_eq_sub
    simpa [wW, a, b] using hval.symm
  have hbD : b ∈ D := hW2D hbW2
  have haD : a ∈ D := by
    have h : w * b⁻¹ ∈ D := D.mul_mem hwD (D.inv_mem hbD)
    simpa [hw_eq, mul_assoc] using h
  have haInf : a ∈ D ⊓ W1 := ⟨haD, haW1⟩
  have haBot : a ∈ (⊥ : Subgroup G) := by
    simpa [D, hcompMW1.2.2.2.eq_bot] using haInf
  have ha_one : a = 1 := by simpa using haBot
  have hwW2 : w ∈ W2 := by
    rw [hw_eq, ha_one, one_mul]
    exact hbW2
  exact hw.2 (Or.inr hwW2)

private theorem theorem_8_13_typeP_conjugates_hatW_not_mem_ambientDerived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∀ y : G,
      y ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) →
        y ∉ ambientDerivedSubgroup M := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDnorm : (D.subgroupOf M).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hMleNormD : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDleM).1 hDnorm
  intro y hy hyD
  rcases hy with ⟨w, hw, m, hmM, hy_eq⟩
  have hmInvNorm : m⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
    hMleNormD (M.inv_mem hmM)
  have hwD : w ∈ D := by
    have hyD' : m⁻¹ * y * (m⁻¹)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp hmInvNorm y).1 hyD
    simpa [hy_eq, mul_assoc] using hyD'
  exact theorem_8_13_typeP_hatW_not_mem_ambientDerived
    (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP w hw hwD

private theorem theorem_8_13_complementIn_isComplement'_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    (L.subgroupOf M).IsComplement' (K.subgroupOf M) := by
  rcases hcomp with ⟨hKM, hLM, hsup, hdisj⟩
  have hsup_local : L.subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    calc
      L.subgroupOf M ⊔ K.subgroupOf M = (L ⊔ K).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := L) (A' := K) (B := M) hLM hKM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxL hxK
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxK,
      by simpa [Subgroup.mem_subgroupOf] using hxL⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (L.subgroupOf M) (K.subgroupOf M)).symm

private theorem theorem_8_13_typeP_conjugates_hatW_mem_M
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∀ y : G,
      y ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) →
        y ∈ M := by
  classical
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  rcases hMF.1 with ⟨hMFM, _hMFnormalM, _hMFnil, _hMFhallM⟩
  have hW1M : W1 ≤ M := hcompMW1.2.1
  have hW2M : W2 ≤ M := fun z hz => hMFM (hW2le hz).1
  have hWM : W1 ⊔ W2 ≤ M := sup_le hW1M hW2M
  intro y hy
  rcases hy with ⟨w, hw, m, hmM, hy_eq⟩
  have hwM : w ∈ M := hWM hw.1
  rw [hy_eq]
  exact M.mul_mem (M.mul_mem hmM hwM) (M.inv_mem hmM)

public theorem theorem_8_13_typeP_W1_coprime_ambientDerived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    Nat.Coprime (Nat.card W1) (Nat.card (ambientDerivedSubgroup M)) := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1hall, hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDnorm : (D.subgroupOf M).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : (D.subgroupOf M).Normal := hDnorm
  have hcompLocal : (W1.subgroupOf M).IsComplement' (D.subgroupOf M) :=
    theorem_8_13_complementIn_isComplement'_subgroupOf
      (M := M) (K := D) (L := W1) (by simpa [D] using hcompMW1)
  rcases hW1hall with ⟨hW1M, hHallW1⟩
  have hW1card : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hDcard : Nat.card (D.subgroupOf M) = Nat.card D :=
    natCard_subgroupOf_eq D M hcompMW1.1
  have hindex : (W1.subgroupOf M).index = Nat.card (D.subgroupOf M) :=
    hcompLocal.symm.index_eq_card
  have hcop : Nat.Coprime (Nat.card (W1.subgroupOf M)) (W1.subgroupOf M).index :=
    hHallW1.card_coprime_index
  simpa [D, hW1card, hDcard, hindex] using hcop

private theorem theorem_8_13_conjugateInSubgroup_top_symm
    {G : Type u} [Group G] {x y : G}
    (hxy : section16ConjugateInSubgroup (⊤ : Subgroup G) x y) :
    section16ConjugateInSubgroup (⊤ : Subgroup G) y x := by
  rcases hxy with ⟨g, _hg, hgy⟩
  refine ⟨g⁻¹, by simp, ?_⟩
  rw [hgy]
  group

private theorem theorem_8_13_supportConclusionDataSource_union_right
    {G : Type u} [Group G] [Finite G]
    {M MF X : Subgroup G} {Xset Yset : Set G} {x : G} {L LF : Subgroup G}
    (hSupp : supportConclusionDataSource M MF X Xset x L LF)
    (hYcop :
      ∀ y : G, y ∈ Yset →
        Nat.Coprime (Nat.card LF) (Nat.card (elementCentralizerIn M y))) :
    supportConclusionDataSource M MF X (Xset ∪ Yset) x L LF := by
  classical
  dsimp [supportConclusionDataSource] at hSupp ⊢
  rcases hSupp with ⟨hL, hLF, huniq, hsplitL, hsplitC, hcop, hType⟩
  refine ⟨hL, hLF, huniq, hsplitL, hsplitC, ?_, hType⟩
  intro y hy
  rcases hy with hyX | hyY
  · exact hcop y hyX
  · exact hYcop y hyY

private theorem theorem_8_13_typeP_A_conjugates_hatW_not_conjugate
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G} {A : Set G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms) :
    ∀ x y : G, x ∈ A →
      y ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) →
        ¬ section16ConjugateInSubgroup (⊤ : Subgroup G) x y := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDnorm : (D.subgroupOf M).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : (D.subgroupOf M).Normal := hDnorm
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  have hP0 : typePDefinitionData M MF U W1 W2 := by
    exact ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  have hcompLocal : (W1.subgroupOf M).IsComplement' (D.subgroupOf M) :=
    theorem_8_13_complementIn_isComplement'_subgroupOf
      (M := M) (K := D) (L := W1) (by simpa [D] using hcompMW1)
  have hquot_card : Nat.card (M ⧸ D.subgroupOf M) = Nat.card W1 := by
    calc
      Nat.card (M ⧸ D.subgroupOf M) = (D.subgroupOf M).index := by
        simpa using (Subgroup.index_eq_card (D.subgroupOf M)).symm
      _ = Nat.card (W1.subgroupOf M) := hcompLocal.index_eq_card
      _ = Nat.card W1 := natCard_subgroupOf_eq W1 M hcompMW1.2.1
  have hcop : Nat.Coprime (Nat.card W1) (Nat.card D) := by
    simpa [D] using
      theorem_8_13_typeP_W1_coprime_ambientDerived
        (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0
  intro x y hxA hyV hxy
  have hxD : x ∈ D := by
    rw [hA, section8CentralizerUnion] at hxA
    rcases hxA with ⟨_z, _hz, hxCent⟩
    exact hxCent.1.1
  have hyM : y ∈ M :=
    theorem_8_13_typeP_conjugates_hatW_mem_M
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0 y hyV
  have hyNotD : y ∉ D :=
    theorem_8_13_typeP_conjugates_hatW_not_mem_ambientDerived
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP0 y hyV
  let q : M →* M ⧸ D.subgroupOf M := QuotientGroup.mk' (D.subgroupOf M)
  let yM : M := ⟨y, hyM⟩
  have hyq_ne : q yM ≠ 1 := by
    intro hyq
    have hyker : yM ∈ q.ker := by
      simpa [MonoidHom.mem_ker] using hyq
    have hyDsub : yM ∈ D.subgroupOf M := by
      simpa [q, QuotientGroup.ker_mk'] using hyker
    exact hyNotD (by simpa [D, yM, Subgroup.mem_subgroupOf] using hyDsub)
  have hq_dvd_W1 : orderOf (q yM) ∣ Nat.card W1 := by
    have hqcard : orderOf (q yM) ∣ Nat.card (M ⧸ D.subgroupOf M) :=
      orderOf_dvd_natCard (q yM)
    simpa [hquot_card] using hqcard
  have hq_dvd_yM : orderOf (q yM) ∣ orderOf yM :=
    orderOf_map_dvd q yM
  have hq_dvd_y : orderOf (q yM) ∣ orderOf y := by
    simpa [yM, Subgroup.orderOf_coe] using hq_dvd_yM
  have horder_yx : orderOf y = orderOf x := by
    rcases hxy with ⟨g, _hg, hgy⟩
    rw [hgy]
    simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq x
  have hq_dvd_x : orderOf (q yM) ∣ orderOf x := by
    simpa [horder_yx] using hq_dvd_y
  have hq_dvd_D : orderOf (q yM) ∣ Nat.card D :=
    hq_dvd_x.trans (Subgroup.orderOf_dvd_natCard D hxD)
  have hq_order_one : orderOf (q yM) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hq_dvd_W1 hq_dvd_D
  exact hyq_ne (orderOf_eq_one_iff.mp hq_order_one)

private theorem theorem_8_13_typeP_elementCentralizerIn_conjugates_hatW_le_conjBy
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∀ y : G,
      y ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) →
        ∃ m : G, m ∈ M ∧
          elementCentralizerIn M y ≤ (W1 ⊔ W2 : Subgroup G).conjBy m := by
  classical
  rcases hP with
    ⟨hMF, hW1cyc, hW1ne, hW1hall, hcompMW1, hUleD, hUnil, hW1normU,
      hcompDU, hMFnotcyc, hM2le, hFitEq, hFitLeD, hW2le, hW2cyc, hW2ne,
      hcentW1, hHatW⟩
  intro y hy
  rcases hy with ⟨w, hw, m, hmM, hy_eq⟩
  refine ⟨m, hmM, ?_⟩
  intro c hc
  rcases hc with ⟨_hcM, hcCent⟩
  let d : G := m⁻¹ * c * m
  have hdCent : d ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcComm : c * y = y * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcCent
    rw [hy_eq] at hcComm
    dsimp [d]
    calc
      (m⁻¹ * c * m) * w =
          m⁻¹ * (c * (m * w * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * w * m⁻¹) * c) * m := by rw [hcComm]
      _ = w * (m⁻¹ * c * m) := by group
  have hdNorm : d ∈ Subgroup.normalizer ({w} : Set G) := by
    have hcomm : d * w = w * d :=
      Subgroup.mem_centralizer_singleton_iff.mp hdCent
    have hfix : d * w * d⁻¹ = w := by
      calc
        d * w * d⁻¹ = w * d * d⁻¹ := by rw [hcomm]
        _ = w := by simp [mul_assoc]
    change ∀ z : G, z ∈ ({w} : Set G) ↔ d * z * d⁻¹ ∈ ({w} : Set G)
    intro z
    constructor
    · intro hz
      have hz_eq : z = w := by simpa using hz
      simp [hz_eq, hfix]
    · intro hz
      have hz_eq : d * z * d⁻¹ = w := by simpa using hz
      have hfix_inv : d⁻¹ * w * d = w := by
        have h := congrArg (fun t : G => d⁻¹ * t * d) hfix
        simpa [mul_assoc] using h.symm
      have hz_w : z = w := by
        calc
          z = d⁻¹ * (d * z * d⁻¹) * d := by group
          _ = d⁻¹ * w * d := by rw [hz_eq]
          _ = w := hfix_inv
      simp [hz_w]
  have hnormSingleton :
      Subgroup.normalizer ({w} : Set G) = W1 ⊔ W2 := by
    exact hHatW ({w} : Set G) (Set.singleton_nonempty w) (by
      intro z hz
      have hz_eq : z = w := by simpa using hz
      simpa [hz_eq] using hw)
  have hdW : d ∈ W1 ⊔ W2 := by
    simpa [hnormSingleton] using hdNorm
  have hc_eq : c = m * d * m⁻¹ := by
    dsimp [d]
    group
  rw [Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨d, hdW, ?_⟩
  simp [MulAut.conj_apply, hc_eq]

private theorem theorem_8_13_typeP_elementCentralizerIn_conjugates_hatW_card_dvd_W
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∀ y : G,
      y ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) →
        Nat.card (elementCentralizerIn M y) ∣ Nat.card (W1 ⊔ W2 : Subgroup G) := by
  intro y hy
  rcases theorem_8_13_typeP_elementCentralizerIn_conjugates_hatW_le_conjBy
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP y hy with
    ⟨m, _hmM, hCent_le⟩
  have hdiv :
      Nat.card (elementCentralizerIn M y) ∣
        Nat.card ((W1 ⊔ W2 : Subgroup G).conjBy m) :=
    Subgroup.card_dvd_of_le hCent_le
  simpa [section11_card_conjBy (G := G) (W1 ⊔ W2 : Subgroup G) m] using hdiv

private theorem theorem_8_13_typeP_A_support_coprime_conjugates_hatW
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 L LF : Subgroup G} {A A0 A1 : Set G} {x : G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2)
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hSuppA : supportConclusionDataSource M MF M A x L LF) :
    ∀ y : G,
      y ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) →
        Nat.Coprime (Nat.card LF) (Nat.card (elementCentralizerIn M y)) := by
  classical
  rcases hSuppA with ⟨_hLmax, _hLF, _huniq, _hsplitL, _hsplitC, hcopA, _hType⟩
  obtain ⟨z, hzW2, hz_ne⟩ :=
    theorem_8_13_typeP_W2_nontrivial
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP
  have hzMs : z ∈ Ms :=
    theorem_8_13_typeP_W2_le_Ms
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP hzW2
  have hzD : z ∈ ambientDerivedSubgroup M :=
    theorem_8_13_typeP_W2_le_ambientDerived
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP hzW2
  have hzA : z ∈ A := by
    rw [hA, section8CentralizerUnion]
    refine ⟨z, ⟨hzMs, hz_ne⟩, ?_⟩
    constructor
    · refine ⟨hzD, ?_⟩
      change z ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact hz_ne
  have hcop_z :
      Nat.Coprime (Nat.card LF) (Nat.card (elementCentralizerIn M z)) :=
    hcopA z hzA
  have hW_le_Cz :
      W1 ⊔ W2 ≤ elementCentralizerIn M z :=
    theorem_8_13_typeP_W_le_elementCentralizerIn_of_W2
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP hzW2
  have hW_dvd_Cz :
      Nat.card (W1 ⊔ W2 : Subgroup G) ∣ Nat.card (elementCentralizerIn M z) :=
    Subgroup.card_dvd_of_le hW_le_Cz
  have hcop_W :
      Nat.Coprime (Nat.card LF) (Nat.card (W1 ⊔ W2 : Subgroup G)) :=
    Nat.Coprime.of_dvd_right hW_dvd_Cz hcop_z
  intro y hy
  exact Nat.Coprime.of_dvd_right
    (theorem_8_13_typeP_elementCentralizerIn_conjugates_hatW_card_dvd_W
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP y hy)
    hcop_W

private theorem theorem_8_13_typeP_A0_fusion
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2)
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
    (hLate :
      (typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
          typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    ∀ x y : G, x ∈ A0 → y ∈ A0 →
      section16ConjugateInSubgroup ⊤ x y →
        section16ConjugateInSubgroup M x y := by
  classical
  have hAconcl :=
    theorem_8_13_typeP_A_source_conclusions
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP hA hLate
  have hVfusion :=
    theorem_8_13_typeP_conjugates_hatW_fusion_in_M
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP
  have hnot :=
    theorem_8_13_typeP_A_conjugates_hatW_not_conjugate
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (A := A) hP hA
  intro x y hxA0 hyA0 hxy
  rw [hA0] at hxA0 hyA0
  rcases hxA0 with hxA | hxV
  · rcases hyA0 with hyA | hyV
    · exact hAconcl.1 x y hxA hyA hxy
    · exact False.elim (hnot x y hxA hyV hxy)
  · rcases hyA0 with hyA | hyV
    · exact False.elim
        (hnot y x hyA hxV (theorem_8_13_conjugateInSubgroup_top_symm hxy))
    · exact hVfusion x y hxV hyV hxy

private theorem theorem_8_13_typeP_A0_support_conclusion
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2)
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
    (hLate :
      (typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
          typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    ∀ x : G, x ∈ section8DSet M A0 →
      ∀ L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) →
          ∃ LF : Subgroup G, supportConclusionDataSource M MF M A0 x L LF := by
  classical
  have hAconcl :=
    theorem_8_13_typeP_A_source_conclusions
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP hA hLate
  have hDsub :
      section8DSet M A0 ⊆ section8DSet M A :=
    theorem_8_13_typeP_D_A0_subset_D_A
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (A := A) (A0 := A0) hP hA0
  intro x hxD L hL
  rcases hAconcl.2.2.2 x (hDsub hxD) L hL with ⟨LF, hSuppA⟩
  refine ⟨LF, ?_⟩
  rw [hA0]
  exact theorem_8_13_supportConclusionDataSource_union_right hSuppA
    (theorem_8_13_typeP_A_support_coprime_conjugates_hatW
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (L := L) (LF := LF) (A := A) (A0 := A0) (A1 := A1)
      (x := x) hNotation hP hA hSuppA)

private theorem theorem_8_13_typeP_A0_source_conclusions
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G} {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hP : typePDefinitionData M MF U W1 W2)
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
    (hLate :
      (typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
          typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    let D := section8DSet M A0
    (∀ x y : G, x ∈ A0 → y ∈ A0 →
      section16ConjugateInSubgroup ⊤ x y →
        section16ConjugateInSubgroup M x y) ∧
    D ⊆ A1 ∧
    (∀ x : G, x ∈ D →
      ∃! L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G))) ∧
    (∀ x : G, x ∈ D →
      ∀ L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) →
          ∃ LF : Subgroup G, supportConclusionDataSource M MF M A0 x L LF) := by
  classical
  have hDUnique :=
    theorem_8_13_typeP_A0_D_subset_A1_unique
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP hA hA0 hLate
  exact ⟨
    theorem_8_13_typeP_A0_fusion
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP hA hA0 hLate,
    hDUnique.1,
    hDUnique.2,
    theorem_8_13_typeP_A0_support_conclusion
      (G := G) (M := M) (MF := MF) (Ms := Ms) (U := U) (W1 := W1)
      (W2 := W2) (A := A) (A0 := A0) (A1 := A1) hNotation hP hA hA0 hLate⟩

public theorem theorem_8_13
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 X : Set G) :
    theorem_8_13_statement M MF Ms A A0 A1 X := by
  classical
  dsimp [theorem_8_13_statement]
  intro hG hNotation hX
  letI : IsMinCE G := hG
  have hNotation' := hNotation
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hCases⟩
  rcases hCases with hTypeI | hTypeP
  · rcases hTypeI with ⟨hSrcI, hA, hA0⟩
    exact theorem_8_13_typeI_source_conclusions
      (G := G) (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0)
      (A1 := A1) (X := X) hNotation' hSrcI hA hA0 hX
  · rcases hTypeP with ⟨U, W1, W2, hP, _hSourceType, hA, hA0, hLate⟩
    rcases hX with rfl | hXA0
    · exact theorem_8_13_typeP_A_source_conclusions hNotation' hP hA hLate
    · subst X
      exact theorem_8_13_typeP_A0_source_conclusions hNotation' hP hA hA0 hLate

/-- The PF `(8.13)` support conclusion constructs the PF `(8.14)` Dade
subgroup function for any chosen `A` or `A₀` source set. -/
public theorem exists_notation_8_14_source_data_of_theorem_8_13
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 X : Set G)
    (hG : IsMinCE G)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hX : X = A ∨ X = A0)
    (hA1X : A1 ⊆ X) :
    ∃ R : G → Subgroup G, ∃ tildeX tildeX0 tildeX1 : Set G,
      notation_8_14_source_data M X X A1
        (section8DSet M X) tildeX tildeX0 tildeX1 R := by
  classical
  have h13 := theorem_8_13 M MF Ms A A0 A1 X hG hNotation hX
  rcases h13 with ⟨_hFusion, hDsubA1, hUnique, hSupport⟩
  let D : Set G := section8DSet M X
  let LOf : (x : G) → x ∈ D → Subgroup G :=
    fun x hx => Classical.choose (hUnique x hx)
  have hLOf_mem :
      ∀ x : G, ∀ hx : x ∈ D,
        LOf x hx ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) := by
    intro x hx
    exact (Classical.choose_spec (hUnique x hx)).1
  let LFOf : (x : G) → (hx : x ∈ D) → Subgroup G :=
    fun x hx => Classical.choose (hSupport x hx (LOf x hx) (hLOf_mem x hx))
  have hLFOf_supp :
      ∀ x : G, ∀ hx : x ∈ D,
        supportConclusionDataSource M MF M X x (LOf x hx) (LFOf x hx) := by
    intro x hx
    exact Classical.choose_spec (hSupport x hx (LOf x hx) (hLOf_mem x hx))
  let R : G → Subgroup G := fun x =>
    if hx : x ∈ D then elementCentralizerIn (LFOf x hx) x else ⊥
  let tildeX : Set G :=
    {y | ∃ a : G, a ∈ X ∧ y ∈ section16ConjugatesOfSetBySet
      (section16LeftCosetSet a (R a)) Set.univ}
  let tildeX0 : Set G :=
    {y | ∃ a : G, a ∈ X ∧ y ∈ section16ConjugatesOfSetBySet
      (section16LeftCosetSet a (R a)) Set.univ}
  let tildeX1 : Set G :=
    {y | ∃ a : G, a ∈ A1 ∧ y ∈ section16ConjugatesOfSetBySet
      (section16LeftCosetSet a (R a)) Set.univ}
  refine ⟨R, tildeX, tildeX0, tildeX1, ?_⟩
  refine ⟨hA1X, le_rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · intro x hx
    have hxnotD : ¬ x ∈ D := hx.2
    simp [R, hxnotD]
  · intro x hx
    exact hUnique x hx
  · intro x hx L LF hSet hLF
    have hxD : x ∈ D := hx
    have hLmem :
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) := by
      rw [hSet]
      simp
    have hL_eq : LOf x hxD = L := by
      have hspec := Classical.choose_spec (hUnique x hxD)
      exact (hspec.2 L hLmem).symm
    have hSuppL :
        supportConclusionDataSource M MF M X x L (LFOf x hxD) := by
      simpa [hL_eq] using hLFOf_supp x hxD
    have hR :
        R x = elementCentralizerIn (LFOf x hxD) x := by
      simp [R, hxD]
    rw [hR]
    rcases hSuppL with
      ⟨_hLmax, hLFOf, _hContain, _hSemiL, _hSemiC, _hCoprime, _hType⟩
    have hLF_eq : LFOf x hxD = LF :=
      le_antisymm (hLF.2 (LFOf x hxD) hLFOf.1) (hLFOf.2 LF hLF.1)
    simp [hLF_eq]

/-- The PF `(8.13)` support conclusion constructs the mixed PF `(8.14)`
package with the original `A ⊆ A₀` notation, not only the diagonal
`X = A` or `X = A₀` package. -/
public theorem exists_mixed_notation_8_14_source_data_of_theorem_8_13
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 : Set G)
    (hG : IsMinCE G)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hA1A : A1 ⊆ A)
    (hAA0 : A ⊆ A0) :
    ∃ R : G → Subgroup G, ∃ tildeA tildeA0 tildeA1 : Set G,
      notation_8_14_source_data M A A0 A1
        (section8DSet M A0) tildeA tildeA0 tildeA1 R := by
  classical
  have h13 := theorem_8_13 M MF Ms A A0 A1 A0 hG hNotation (Or.inr rfl)
  rcases h13 with ⟨_hFusion, _hDsubA1, hUnique, hSupport⟩
  let D : Set G := section8DSet M A0
  let LOf : (x : G) → x ∈ D → Subgroup G :=
    fun x hx => Classical.choose (hUnique x hx)
  have hLOf_mem :
      ∀ x : G, ∀ hx : x ∈ D,
        LOf x hx ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) := by
    intro x hx
    exact (Classical.choose_spec (hUnique x hx)).1
  let LFOf : (x : G) → (hx : x ∈ D) → Subgroup G :=
    fun x hx => Classical.choose (hSupport x hx (LOf x hx) (hLOf_mem x hx))
  have hLFOf_supp :
      ∀ x : G, ∀ hx : x ∈ D,
        supportConclusionDataSource M MF M A0 x (LOf x hx) (LFOf x hx) := by
    intro x hx
    exact Classical.choose_spec (hSupport x hx (LOf x hx) (hLOf_mem x hx))
  let R : G → Subgroup G := fun x =>
    if hx : x ∈ D then elementCentralizerIn (LFOf x hx) x else ⊥
  let tildeA : Set G :=
    {y | ∃ a : G, a ∈ A ∧ y ∈ section16ConjugatesOfSetBySet
      (section16LeftCosetSet a (R a)) Set.univ}
  let tildeA0 : Set G :=
    {y | ∃ a : G, a ∈ A0 ∧ y ∈ section16ConjugatesOfSetBySet
      (section16LeftCosetSet a (R a)) Set.univ}
  let tildeA1 : Set G :=
    {y | ∃ a : G, a ∈ A1 ∧ y ∈ section16ConjugatesOfSetBySet
      (section16LeftCosetSet a (R a)) Set.univ}
  refine ⟨R, tildeA, tildeA0, tildeA1, ?_⟩
  refine ⟨hA1A, hAA0, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · intro x hx
    have hxnotD : ¬ x ∈ D := hx.2
    simp [R, hxnotD]
  · intro x hx
    exact hUnique x hx
  · intro x hx L LF hSet hLF
    have hxD : x ∈ D := hx
    have hLmem :
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) := by
      rw [hSet]
      simp
    have hL_eq : LOf x hxD = L := by
      have hspec := Classical.choose_spec (hUnique x hxD)
      exact (hspec.2 L hLmem).symm
    have hSuppL :
        supportConclusionDataSource M MF M A0 x L (LFOf x hxD) := by
      simpa [hL_eq] using hLFOf_supp x hxD
    have hR :
        R x = elementCentralizerIn (LFOf x hxD) x := by
      simp [R, hxD]
    rw [hR]
    rcases hSuppL with
      ⟨_hLmax, hLFOf, _hContain, _hSemiL, _hSemiC, _hCoprime, _hType⟩
    have hLF_eq : LFOf x hxD = LF :=
      le_antisymm (hLF.2 (LFOf x hxD) hLFOf.1) (hLFOf.2 LF hLF.1)
    simp [hLF_eq]

end CFSG.Section8
