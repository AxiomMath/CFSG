module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4Iso
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootNormalizer
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ItemThree
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.GroupTheory.TitsSystem.Parabolic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAutD
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.LieKnownR2.F4

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley

private theorem l10sf4a_pCore_le_centralizer_highRoot
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    pCoreOf 2 (Subgroup.normalizer
        (((f4Datum K).rootGroup (CFSG.SeitzReduction.highRoot .F4) :
            Subgroup ↥(adjointGroup .F4 K)) :
          Set ↥(adjointGroup .F4 K))) ≤
      Subgroup.centralizer
        (((f4Datum K).rootGroup (CFSG.SeitzReduction.highRoot .F4) :
            Subgroup ↥(adjointGroup .F4 K)) :
          Set ↥(adjointGroup .F4 K)) := by
  rw [Short.pCoreOf_normalizer_rootGroup_highRoot_F4 K]
  exact highestRootRadical_le_centralizer_rootGroup (Short.f4_steinbergExtras_exact K)
    (Short.f4_rootGroupCommutators_exact K) rfl (Short.isHighestRoot_F4 K)

private theorem l10sf4a_conj_eq_of_mem {G : Type*} [Group G] {R : Subgroup G} {y : MulAut G}
    (hcent : pCoreOf 2 (Subgroup.normalizer (R : Set G)) ≤ Subgroup.centralizer (R : Set G))
    (hy : ∀ m ∈ Subgroup.normalizer (R : Set G),
      y m * m⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (R : Set G)))
    {m : G} (hm : m ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R) :
    y m * x * (y m)⁻¹ = m * x * m⁻¹ := by
  have hq : y m * m⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (R : Set G)) := hy m hm
  have hqc : y m * m⁻¹ ∈ Subgroup.centralizer (R : Set G) := hcent hq
  have hmx : m * x * m⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hm x).mp hx
  have hcomm : (m * x * m⁻¹) * (y m * m⁻¹) = (y m * m⁻¹) * (m * x * m⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hqc (m * x * m⁻¹) hmx
  calc y m * x * (y m)⁻¹ = (y m * m⁻¹) * (m * x * m⁻¹) * (y m * m⁻¹)⁻¹ := by group
    _ = m * x * m⁻¹ := by rw [← hcomm]; group

private theorem l10sf4a_xPar_mem_rootGroup
    {K : Type} [Field K] {γ : Fin (f4Datum K).rank → ℤ} (hγ : IsRoot .F4 γ) (c : K) :
    xPar (rootOperatorFamily .F4) γ c ∈ (f4Datum K).rootGroup γ := by
  change xPar (rootOperatorFamily .F4) γ c ∈ rootGroup (rootOperatorFamily .F4) K γ
  rw [CFSG.LieType.Steinberg.Adjoint.rootGroup_of_isRoot (F := rootOperatorFamily .F4) hγ,
    CFSG.LieType.Steinberg.Adjoint.xPar_of_isRoot (F := rootOperatorFamily .F4) hγ]
  exact (rootOperatorFamily .F4).eltElement_mem_rootSubgroup ⟨γ, hγ⟩ c

private theorem l10sf4a_torus_conj_f4x
    {K : Type} [Field K] {h : ModGL .F4 K} (hh : h ∈ torusGroup .F4 K) (c : K) :
    h * f4x K 47 c * h⁻¹ =
      f4x K 47 (torusRootChar h (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) * c) := by
  have hγ : IsRoot .F4 (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
    rw [CFSG.SeitzReduction.F4Pilot.orbitCertRoot_47_44.1]
    exact CFSG.SeitzReduction.F4Pilot.isRoot_rootR
  change h * pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) c * h⁻¹ =
    pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)
      (torusRootChar h (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) * c)
  rw [conj_pinnedX_of_mem_torusGroup hh hγ]

private theorem l10sf4a_torusElt_char
    {K : Type} [Field K] (t : Kˣ) :
    torusRootChar (torusElt .F4 K (⟨0, by decide⟩ : Fin Tag.F4.rank) t)
        (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) = (t : K) := by
  have hγ : IsRoot .F4 (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
    rw [CFSG.SeitzReduction.F4Pilot.orbitCertRoot_47_44.1]
    exact CFSG.SeitzReduction.F4Pilot.isRoot_rootR
  rw [torusRootChar_torusElt (i := (⟨0, by decide⟩ : Fin Tag.F4.rank)) t hγ]
  have hexp : (∑ j : Fin Tag.F4.rank,
      Tag.cartan .F4 (⟨0, by decide⟩ : Fin Tag.F4.rank) j *
        (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) j) = 1 := by
    decide +kernel
  rw [hexp]
  simp

private theorem l10sf4a_fr_pow_f4x
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (j : ℕ) (c : K) :
    (CFSG.SeitzReduction.f4Fr (K := K) ^ j)
        (⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) =
      ⟨f4x K 47 (c ^ ReeTag.F4.prime ^ j), pinnedX_mem_adjointGroup _ _⟩ :=
  Subtype.ext (CFSG.SeitzReduction.F4Pilot.coe_f4Fr_pow_f4x (K := K) j 47 c)

private theorem l10sf4a_frobenius_surj {K : Type} [Field K] [Finite K] [CharP K 2] (j : ℕ) :
    Function.Surjective (fun c : K => c ^ 2 ^ j) := by
  haveI : PerfectRing K 2 := inferInstance
  intro d
  exact ⟨(iterateFrobeniusEquiv K 2 j).symm d, by
    change (iterateFrobeniusEquiv K 2 j) ((iterateFrobeniusEquiv K 2 j).symm d) = d
    exact (iterateFrobeniusEquiv K 2 j).apply_symm_apply d⟩

private theorem l10sf4a_exists_xPar_of_mem_rootGroup
    {K : Type} [Field K] {γ : Fin (f4Datum K).rank → ℤ} (hγ : IsRoot .F4 γ)
    {x : ↥(adjointGroup .F4 K)} (hx : x ∈ (f4Datum K).rootGroup γ) :
    ∃ c : K, x = xPar (rootOperatorFamily .F4) γ c := by
  change x ∈ rootGroup (rootOperatorFamily .F4) K γ at hx
  rw [CFSG.LieType.Steinberg.Adjoint.rootGroup_of_isRoot (F := rootOperatorFamily .F4) hγ] at hx
  obtain ⟨c, hc⟩ := (rootOperatorFamily .F4).mem_rootSubgroup.mp hx
  exact ⟨c, hc.symm.trans (CFSG.LieType.Steinberg.Adjoint.xPar_of_isRoot
    (F := rootOperatorFamily .F4) hγ c).symm⟩

private theorem l10sf4a_exists_pinnedX_of_mem_rootGroup
    {K : Type} [Field K] {γ : Fin (f4Datum K).rank → ℤ} (hγ : IsRoot .F4 γ)
    {x : ↥(adjointGroup .F4 K)} (hx : x ∈ (f4Datum K).rootGroup γ) :
    ∃ d : K, x = (⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := by
  obtain ⟨c, rfl⟩ := l10sf4a_exists_xPar_of_mem_rootGroup hγ hx
  exact ⟨(((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : K) * c,
    Subtype.ext (CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hγ c)⟩

private theorem l10sf4a_pinnedX_mem_rootGroup
    {K : Type} [Field K] {γ : Fin (f4Datum K).rank → ℤ} (hγ : IsRoot .F4 γ) (d : K) :
    (⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) ∈
      (f4Datum K).rootGroup γ := by
  have hsign : (((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : K) ≠ 0 := by
    rcases (rootOperatorFamily .F4).pinnedFamilySign_eq γ with h | h <;> rw [h] <;> norm_num
  have hx : (⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) =
      xPar (rootOperatorFamily .F4) γ
        ((((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : K)⁻¹ * d) := by
    apply Subtype.ext
    rw [CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hγ]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ hsign, one_mul]
  rw [hx]
  exact l10sf4a_xPar_mem_rootGroup hγ _

private theorem l10sf4a_fr_pow_pinnedX
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (j : ℕ)
    {γ : Fin (f4Datum K).rank → ℤ} (c : K) :
    (CFSG.SeitzReduction.f4Fr (K := K) ^ j)
        (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) =
      ⟨pinnedX .F4 K γ (c ^ ReeTag.F4.prime ^ j), pinnedX_mem_adjointGroup _ _⟩ :=
  Subtype.ext (CFSG.SeitzReduction.F4Pilot.coe_f4Fr_pow_pinnedX (K := K) j γ c)

private theorem l10sf4a_fr_pow_map_rootGroup
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (j : ℕ) :
    ((f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)).map
        (CFSG.SeitzReduction.f4Fr (K := K) ^ j).toMonoidHom =
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
  have hγ : IsRoot .F4 (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
    rw [CFSG.SeitzReduction.F4Pilot.orbitCertRoot_47_44.1]
    exact CFSG.SeitzReduction.F4Pilot.isRoot_rootR
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := l10sf4a_exists_xPar_of_mem_rootGroup hγ hx
    have hx2 : xPar (rootOperatorFamily .F4)
          (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) c =
        (⟨pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)
            ((((rootOperatorFamily .F4).pinnedFamilySign
              (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) : ℤ) : K) * c),
          pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) :=
      Subtype.ext (CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hγ c)
    rw [hx2]
    change (CFSG.SeitzReduction.f4Fr (K := K) ^ j)
        (⟨pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)
            ((((rootOperatorFamily .F4).pinnedFamilySign
              (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) : ℤ) : K) * c),
          pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) ∈
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)
    rw [l10sf4a_fr_pow_pinnedX (K := K)
      (γ := CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) j]
    exact l10sf4a_pinnedX_mem_rootGroup hγ _
  · exact le_of_eq (Subgroup.card_map_of_injective
      (f := (CFSG.SeitzReduction.f4Fr (K := K) ^ j).toMonoidHom)
      (CFSG.SeitzReduction.f4Fr (K := K) ^ j).injective).symm

private theorem l10sf4a_torus_conj_f4x_adj
    {K : Type} [Field K] {h : ↥(adjointGroup .F4 K)}
    (hh : (h : ModGL .F4 K) ∈ torusGroup .F4 K) (c : K) :
    h * (⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * h⁻¹ =
      (⟨f4x K 47 (torusRootChar (h : ModGL .F4 K)
        (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) * c),
        pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := by
  apply Subtype.ext
  exact l10sf4a_torus_conj_f4x (K := K) hh c

private theorem l10sf4a_fr_pow_torus_conj_f4x_adj
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : ↥(adjointGroup .F4 K)} (hh : (h : ModGL .F4 K) ∈ torusGroup .F4 K)
    (j : ℕ) (c : K) :
    ((CFSG.SeitzReduction.f4Fr (K := K) ^ j) h) *
        (⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) *
        (((CFSG.SeitzReduction.f4Fr (K := K) ^ j) h))⁻¹ =
      (⟨f4x K 47 ((torusRootChar (h : ModGL .F4 K)
        (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)) ^ 2 ^ j * c),
        pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := by
  obtain ⟨d, hd⟩ := l10sf4a_frobenius_surj (K := K) j c
  rw [← hd]
  rw [show (⟨f4x K 47 (d ^ 2 ^ j), pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) =
      (CFSG.SeitzReduction.f4Fr (K := K) ^ j)
        (⟨f4x K 47 d, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) from
    (l10sf4a_fr_pow_f4x (K := K) j d).symm]
  simp only [← map_inv, ← map_mul]
  rw [l10sf4a_torus_conj_f4x_adj (K := K) hh d]
  rw [l10sf4a_fr_pow_f4x (K := K) j (torusRootChar (h : ModGL .F4 K)
    (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) * d)]
  apply Subtype.ext
  exact congrArg (f4x K 47) (mul_pow (torusRootChar (h : ModGL .F4 K)
    (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)) d (2 ^ j))

private theorem l10sf4a_torus_mem_normalizer
    {K : Type} [Field K] {h : ↥(adjointGroup .F4 K)}
    (hh : (h : ModGL .F4 K) ∈ torusGroup .F4 K) :
    h ∈ Subgroup.normalizer
      (((f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) :
        Subgroup ↥(adjointGroup .F4 K)) : Set ↥(adjointGroup .F4 K)) := by
  have hθ : IsRoot .F4 (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
    rw [CFSG.SeitzReduction.F4Pilot.orbitCertRoot_47_44.1]
    exact CFSG.SeitzReduction.F4Pilot.isRoot_rootR
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨d, rfl⟩ := l10sf4a_exists_pinnedX_of_mem_rootGroup hθ hx
    change h * (⟨f4x K 47 d, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * h⁻¹ ∈
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)
    rw [l10sf4a_torus_conj_f4x_adj (K := K) hh d]
    exact l10sf4a_pinnedX_mem_rootGroup hθ _
  · intro hx
    obtain ⟨d, hd⟩ := l10sf4a_exists_pinnedX_of_mem_rootGroup hθ hx
    have hhinv : ((h⁻¹ : ↥(adjointGroup .F4 K)) : ModGL .F4 K) ∈ torusGroup .F4 K :=
      (torusGroup .F4 K).inv_mem hh
    have hxR : h⁻¹ * (⟨pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) d,
        pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * h ∈
        (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
      rw [show h⁻¹ * (⟨pinnedX .F4 K
            (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) d,
            pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * h =
          h⁻¹ * (⟨pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) d,
            pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * (h⁻¹)⁻¹ from by
        rw [inv_inv]]
      change h⁻¹ * (⟨f4x K 47 d, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) *
          (h⁻¹)⁻¹ ∈
        (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)
      rw [l10sf4a_torus_conj_f4x_adj (K := K) hhinv d]
      exact l10sf4a_pinnedX_mem_rootGroup hθ _
    rw [show x = h⁻¹ * (⟨pinnedX .F4 K
        (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) d,
        pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * h from by rw [← hd]; group]
    exact hxR

private theorem l10sf4_odd_not_normalizes
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    {γ₀ : Fin (f4Datum K).rank → ℤ} (hγ₀ : γ₀ ∈ (f4Datum K).roots)
    (hmax : ∀ δ ∈ (f4Datum K).roots, ∑ i, δ i ≤ ∑ i, γ₀ i)
    (y : MulAut ↥(adjointGroup .F4 K)) (g : ↥(adjointGroup ReeTag.F4.tag K)) {k : ℕ}
    (hk : Odd k) (hyeq : y = MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ k) :
    ((f4Datum K).rootGroup γ₀).map y.toMonoidHom ≠ (f4Datum K).rootGroup γ₀ := by
  let g' : ↥(adjointGroup .F4 K) := g
  have hyeq' : y = MulAut.conj g' * CFSG.SeitzReduction.f4Phi (K := K) ^ k := by
    rw [hyeq]; rfl
  have hγ0 : γ₀ = CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47 := by
    rw [CFSG.SeitzReduction.F4Pilot.orbitCertRoot_47_44.1]
    refine Short.eq_highRoot_of_maxHeight_F4 K hγ₀ ?_
    intro δ hδ
    exact hmax δ hδ
  subst hγ0
  intro hyR
  have hθ : IsRoot .F4 (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
    rw [CFSG.SeitzReduction.F4Pilot.orbitCertRoot_47_44.1]
    exact CFSG.SeitzReduction.F4Pilot.isRoot_rootR
  obtain ⟨j, rfl⟩ := hk
  let x : ↥(adjointGroup .F4 K) := ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩
  have hxR : x ∈ (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
    change (⟨pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) 1,
      pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) ∈
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)
    exact l10sf4a_pinnedX_mem_rootGroup hθ 1
  have hφk : (CFSG.SeitzReduction.f4Phi (K := K) ^ (2 * j + 1)) x =
      (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) :=
    CFSG.SeitzReduction.f4Phi_pow_odd_f4x_47 (K := K) j
  have hyx : y x = g' * (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ :
      ↥(adjointGroup .F4 K)) * g'⁻¹ := by
    rw [hyeq', MulAut.mul_apply, MulAut.conj_apply, hφk]
  have hyxR : g' * (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ :
      ↥(adjointGroup .F4 K)) * g'⁻¹ ∈
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
    rw [← hyx]
    have h : y x ∈ ((f4Datum K).rootGroup
        (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)).map y.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hxR, rfl⟩
    rwa [hyR] at h
  obtain ⟨c, hc⟩ := l10sf4a_exists_pinnedX_of_mem_rootGroup hθ hyxR
  by_cases hc0 : c = 0
  · exfalso
    subst hc0
    have h1 : (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) = 1 := by
      have h := hc
      rw [show (⟨pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) 0,
          pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) = 1 from
        Subtype.ext (pinnedX_zero .F4 K
          (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47))] at h
      calc (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K))
          = g'⁻¹ * (g' * (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ :
              ↥(adjointGroup .F4 K)) * g'⁻¹) * g' := by group
        _ = g'⁻¹ * 1 * g' := by rw [h]
        _ = 1 := by group
    have h1zero : (1 : ↥(adjointGroup .F4 K)) =
        (⟨f4x K 44 0, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) :=
      Subtype.ext (f4x_zero (K := K) 44).symm
    have h1' : (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) =
        (⟨f4x K 44 0, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) :=
      h1.trans h1zero
    have hval : (f4x K 44 1 : ModGL .F4 K) = f4x K 44 0 := by
      have h := congrArg Subtype.val h1'
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, f4x, pinnedX]
        using h
    have h3 : (1 : K) = 0 :=
      pinnedX_injective (τ := .F4) (R := K)
        (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 44) hval
    exact one_ne_zero h3
  · exfalso
    let u : Kˣ := Units.mk0 c hc0
    let h : ↥(adjointGroup .F4 K) :=
      ⟨torusElt .F4 K (⟨0, by decide⟩ : Fin Tag.F4.rank) u, torusElt_mem_adjointGroup _ u⟩
    have hh : (h : ModGL .F4 K) ∈ torusGroup .F4 K :=
      torusElt_mem_torusGroup (τ := .F4) (R := K) _ u
    have hχ : torusRootChar (h : ModGL .F4 K)
        (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) = c := by
      change torusRootChar (torusElt .F4 K (⟨0, by decide⟩ : Fin Tag.F4.rank) u)
        (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) = c
      rw [l10sf4a_torusElt_char (K := K) u]
      rfl
    have hconj : h * (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * h⁻¹ =
        (⟨pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) c,
          pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := by
      rw [show h * (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * h⁻¹ =
          h * (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * h⁻¹ from rfl,
        l10sf4a_torus_conj_f4x_adj (K := K) hh 1, hχ, mul_one]
      rfl
    have h1 : g' * (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * g'⁻¹ =
        h * (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * h⁻¹ := by
      rw [hc, hconj]
    have h2 : ((g'⁻¹ * h : ↥(adjointGroup .F4 K)) : ModGL .F4 K) * f4x K 47 1 *
        (((g'⁻¹ * h : ↥(adjointGroup .F4 K)) : ModGL .F4 K))⁻¹ = f4x K 44 1 := by
      have h3 : (g'⁻¹ * h : ↥(adjointGroup .F4 K)) * x * (g'⁻¹ * h : ↥(adjointGroup .F4 K))⁻¹ =
          (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := by
        calc (g'⁻¹ * h) * x * (g'⁻¹ * h)⁻¹
            = g'⁻¹ * (h * x * h⁻¹) * g' := by group
          _ = g'⁻¹ * (g' * (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ :
                ↥(adjointGroup .F4 K)) * g'⁻¹) * g' := by rw [← h1]
          _ = (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := by group
      exact congrArg Subtype.val h3
    exact CFSG.SeitzReduction.conj_f4x_47_ne_f4x_44 (K := K)
      (g := ((g'⁻¹ * h : ↥(adjointGroup .F4 K)) : ModGL .F4 K)) (g'⁻¹ * h).2 h2

private theorem l10sf4_frob_trivial
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    {γ₀ : Fin (f4Datum K).rank → ℤ} (hγ₀ : γ₀ ∈ (f4Datum K).roots)
    (hmax : ∀ δ ∈ (f4Datum K).roots, ∑ i, δ i ≤ ∑ i, γ₀ i)
    (y : MulAut ↥(adjointGroup .F4 K)) (g : ↥(adjointGroup ReeTag.F4.tag K)) (j : ℕ)
    (hyeq : y = MulAut.conj g * ReeTag.F4.finiteFrobeniusAut K ^ j)
    (hyR : ((f4Datum K).rootGroup γ₀).map y.toMonoidHom = (f4Datum K).rootGroup γ₀)
    (hy : ∀ m ∈ Subgroup.normalizer
        (((f4Datum K).rootGroup γ₀ : Subgroup ↥(adjointGroup .F4 K)) : Set ↥(adjointGroup .F4 K)),
      y m * m⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer
        (((f4Datum K).rootGroup γ₀ : Subgroup ↥(adjointGroup .F4 K)) :
          Set ↥(adjointGroup .F4 K)))) :
    ReeTag.F4.finiteFrobeniusAut K ^ j = 1 := by
  let g' : ↥(adjointGroup .F4 K) := g
  have hyeq' : y = MulAut.conj g' * CFSG.SeitzReduction.f4Fr (K := K) ^ j := by
    rw [hyeq]
    rfl
  have hγ0 : γ₀ = CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47 := by
    rw [CFSG.SeitzReduction.F4Pilot.orbitCertRoot_47_44.1]
    refine Short.eq_highRoot_of_maxHeight_F4 K hγ₀ ?_
    intro δ hδ
    exact hmax δ hδ
  subst hγ0
  have hθ : IsRoot .F4 (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
    rw [CFSG.SeitzReduction.F4Pilot.orbitCertRoot_47_44.1]
    exact CFSG.SeitzReduction.F4Pilot.isRoot_rootR
  have hcent : pCoreOf 2 (Subgroup.normalizer
        (((f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) :
          Subgroup ↥(adjointGroup .F4 K)) : Set ↥(adjointGroup .F4 K))) ≤
      Subgroup.centralizer
        (((f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) :
          Subgroup ↥(adjointGroup .F4 K)) : Set ↥(adjointGroup .F4 K)) := by
    rw [CFSG.SeitzReduction.F4Pilot.orbitCertRoot_47_44.1]
    exact l10sf4a_pCore_le_centralizer_highRoot (K := K)
  have hgN : g' ∈ Subgroup.normalizer
      (((f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) :
        Subgroup ↥(adjointGroup .F4 K)) : Set ↥(adjointGroup .F4 K)) := by
    have hgR : ((f4Datum K).rootGroup
          (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)).map
          (MulAut.conj g').toMonoidHom =
        (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
      have h := hyR
      rw [hyeq'] at h
      rw [show (MulAut.conj g' * CFSG.SeitzReduction.f4Fr (K := K) ^ j).toMonoidHom =
            (MulAut.conj g').toMonoidHom.comp
              (CFSG.SeitzReduction.f4Fr (K := K) ^ j).toMonoidHom from by
          ext z; rfl,
        ← Subgroup.map_map, l10sf4a_fr_pow_map_rootGroup (K := K) j] at h
      exact h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : g' * x * g'⁻¹ ∈ ((f4Datum K).rootGroup
            (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)).map
            (MulAut.conj g').toMonoidHom := ⟨x, hx, rfl⟩
      rwa [hgR] at hx'
    · intro hx
      have hx'' : g' * x * g'⁻¹ ∈ ((f4Datum K).rootGroup
            (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)).map
            (MulAut.conj g').toMonoidHom := by rwa [hgR]
      obtain ⟨z, hz, hzx⟩ := hx''
      have hzx' : z = x := mul_left_cancel (mul_right_cancel hzx)
      rwa [← hzx']
  let x : ↥(adjointGroup .F4 K) := ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩
  have hxR : x ∈ (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) := by
    change (⟨pinnedX .F4 K (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) 1,
      pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) ∈
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47)
    exact l10sf4a_pinnedX_mem_rootGroup hθ 1
  have hgxR : g' * x * g'⁻¹ ∈ (f4Datum K).rootGroup
      (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) :=
    (Subgroup.mem_normalizer_iff.mp hgN x).mp hxR
  obtain ⟨μ, hμeq⟩ := l10sf4a_exists_pinnedX_of_mem_rootGroup hθ hgxR
  have hμ : (g' : ModGL .F4 K) * f4x K 47 1 * (g' : ModGL .F4 K)⁻¹ = f4x K 47 μ := by
    have h := congrArg Subtype.val hμeq
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, x, f4x] using h
  obtain ⟨l, hl⟩ := CFSG.SeitzReduction.F4Pilot.exists_conj_f4x_47_eq_mul (K := K)
    (g := (g' : ModGL .F4 K)) g'.2 (μ := μ) hμ
  have hginvN : g'⁻¹ ∈ Subgroup.normalizer
      (((f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) :
        Subgroup ↥(adjointGroup .F4 K)) : Set ↥(adjointGroup .F4 K)) :=
    (Subgroup.normalizer _).inv_mem hgN
  have hginvxR : g'⁻¹ * x * g' ∈ (f4Datum K).rootGroup
      (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) :=
    (Subgroup.mem_normalizer_iff.mp hginvN x).mp hxR
  obtain ⟨ν, hνeq⟩ := l10sf4a_exists_pinnedX_of_mem_rootGroup hθ hginvxR
  have hν : ((g' : ModGL .F4 K))⁻¹ * f4x K 47 1 * (g' : ModGL .F4 K) = f4x K 47 ν :=
    congrArg Subtype.val hνeq
  obtain ⟨a, ha⟩ := CFSG.SeitzReduction.F4Pilot.exists_conj_f4x_47_eq_mul (K := K)
    (g := ((g' : ModGL .F4 K))⁻¹) (inv_mem g'.2) (μ := ν) hν
  have hla : a * l = 1 := by
    have h1 : ((g' : ModGL .F4 K))⁻¹ * f4x K 47 l * (g' : ModGL .F4 K) = f4x K 47 (a * l) :=
      ha l
    have h2 : ((g' : ModGL .F4 K))⁻¹ * f4x K 47 l * (g' : ModGL .F4 K) = f4x K 47 1 := by
      rw [show f4x K 47 l = (g' : ModGL .F4 K) * f4x K 47 1 * (g' : ModGL .F4 K)⁻¹ from
        ((hl 1).trans (by rw [mul_one])).symm]
      group
    rw [h2] at h1
    exact pinnedX_injective (τ := .F4) (R := K)
      (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) h1.symm
  have hkey : ∀ t : K, t ^ (2 : ℕ) ^ j = t := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp
    · let u : Kˣ := Units.mk0 t ht
      let h : ↥(adjointGroup .F4 K) :=
        ⟨torusElt .F4 K (⟨0, by decide⟩ : Fin Tag.F4.rank) u,
          torusElt_mem_adjointGroup _ u⟩
      have hh : (h : ModGL .F4 K) ∈ torusGroup .F4 K :=
        torusElt_mem_torusGroup (τ := .F4) (R := K) _ u
      have hN : h ∈ Subgroup.normalizer
          (((f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) :
            Subgroup ↥(adjointGroup .F4 K)) : Set ↥(adjointGroup .F4 K)) :=
        l10sf4a_torus_mem_normalizer (K := K) hh
      have hχ : torusRootChar (h : ModGL .F4 K)
          (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) = t := by
        change torusRootChar (torusElt .F4 K (⟨0, by decide⟩ : Fin Tag.F4.rank) u)
          (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) = t
        rw [l10sf4a_torusElt_char (K := K) u]
        rfl
      have hconj : y h * x * (y h)⁻¹ = h * x * h⁻¹ :=
        l10sf4a_conj_eq_of_mem
          (R := (f4Datum K).rootGroup (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47))
          (y := y) hcent hy hN hxR
      have hFH : y h = g' * ((CFSG.SeitzReduction.f4Fr (K := K) ^ j) h) * g'⁻¹ := by
        rw [hyeq']; rfl
      have hstep2 : g'⁻¹ * x * g' = (⟨f4x K 47 a, pinnedX_mem_adjointGroup _ _⟩ :
          ↥(adjointGroup .F4 K)) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, x]
        have h := ha 1
        simp only [inv_inv, mul_one] at h
        exact h
      have hstep3 : ((CFSG.SeitzReduction.f4Fr (K := K) ^ j) h) *
          (⟨f4x K 47 a, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) *
          (((CFSG.SeitzReduction.f4Fr (K := K) ^ j) h))⁻¹ =
            (⟨f4x K 47 (torusRootChar (h : ModGL .F4 K)
              (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) ^ 2 ^ j * a),
              pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) :=
        l10sf4a_fr_pow_torus_conj_f4x_adj (K := K) hh j a
      have hstep4 : g' * (⟨f4x K 47 (torusRootChar (h : ModGL .F4 K)
            (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) ^ 2 ^ j * a),
            pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * g'⁻¹ =
          (⟨f4x K 47 (l * (torusRootChar (h : ModGL .F4 K)
            (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) ^ 2 ^ j * a)),
            pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [hl (torusRootChar (h : ModGL .F4 K)
          (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) ^ 2 ^ j * a)]
      have hLHS : y h * x * (y h)⁻¹ = (⟨f4x K 47 (l * (t ^ 2 ^ j * a)),
          pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := by
        calc y h * x * (y h)⁻¹
            = g' * (((CFSG.SeitzReduction.f4Fr (K := K) ^ j) h) * (g'⁻¹ * x * g') *
                (((CFSG.SeitzReduction.f4Fr (K := K) ^ j) h))⁻¹) * g'⁻¹ := by
              rw [hFH]; group
          _ = g' * (((CFSG.SeitzReduction.f4Fr (K := K) ^ j) h) *
                (⟨f4x K 47 a, pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) *
                (((CFSG.SeitzReduction.f4Fr (K := K) ^ j) h))⁻¹) * g'⁻¹ := by rw [hstep2]
          _ = g' * (⟨f4x K 47 (torusRootChar (h : ModGL .F4 K)
                (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) ^ 2 ^ j * a),
                pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) * g'⁻¹ := by rw [hstep3]
          _ = (⟨f4x K 47 (l * (torusRootChar (h : ModGL .F4 K)
                (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) ^ 2 ^ j * a)),
                pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := hstep4
          _ = (⟨f4x K 47 (l * (t ^ 2 ^ j * a)),
                pinnedX_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) := by rw [hχ]
      have hRHS : h * x * h⁻¹ = (⟨f4x K 47 t, pinnedX_mem_adjointGroup _ _⟩ :
          ↥(adjointGroup .F4 K)) := by
        rw [show h * x * h⁻¹ = h * (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ :
            ↥(adjointGroup .F4 K)) * h⁻¹ from rfl,
          l10sf4a_torus_conj_f4x_adj (K := K) hh 1, ← hχ, mul_one]
      have heq : l * (t ^ 2 ^ j * a) = t := by
        have h := hconj
        rw [hRHS, hLHS] at h
        have h' : f4x K 47 (l * (t ^ 2 ^ j * a)) = f4x K 47 t := by
          injection h with hh
        exact pinnedX_injective (τ := .F4) (R := K)
          (CFSG.LieType.Chevalley.RootOps.orbitCertRoot .F4 47) h'
      calc t ^ (2 : ℕ) ^ j = (a * l) * t ^ (2 : ℕ) ^ j * (a * l) := by
              rw [hla, one_mul, mul_one]
        _ = a * (l * (t ^ 2 ^ j * a)) * l := by group
        _ = a * t * l := by rw [heq]
        _ = (a * l) * t := by group
        _ = t := by rw [hla, one_mul]
  exact CFSG.SeitzReduction.F4Pilot.f4Fr_pow_eq_one_of_forall (K := K) (j := j) hkey

private theorem l10sf4_inner_maxHeight
    {f : ℕ} (hf : 1 ≤ f)
    {γ₀ : Fin (f4Datum (GaloisField 2 f)).rank → ℤ}
    (hγ₀ : γ₀ ∈ (f4Datum (GaloisField 2 f)).roots)
    (hmax : ∀ δ ∈ (f4Datum (GaloisField 2 f)).roots, ∑ i, δ i ≤ ∑ i, γ₀ i) :
    GGRootNormInner ((f4Datum (GaloisField 2 f)).rootGroup γ₀) := by
  intro y hy2 hyR hytriv
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  haveI : CharP (GaloisField 2 f) ReeTag.F4.prime :=
    ‹CharP (GaloisField 2 f) 2›
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form hf (GaloisField 2 f) hcard
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf y
  rcases Nat.even_or_odd (k : ℕ) with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hyeq : y = MulAut.conj g * ReeTag.F4.finiteFrobeniusAut (GaloisField 2 f) ^ j := by
      rw [hgk, hj, ← two_mul, finiteExceptionalAut_pow_two_mul (t := ReeTag.F4) j]
    have hFr : ReeTag.F4.finiteFrobeniusAut (GaloisField 2 f) ^ j = 1 :=
      l10sf4_frob_trivial hγ₀ hmax y g j hyeq hyR hytriv
    refine ⟨g, ?_⟩
    rw [hyeq, hFr, mul_one]
    rfl
  · exact absurd hyR
      (l10sf4_odd_not_normalizes hγ₀ hmax y g (k := (k : ℕ)) ⟨j, hj⟩ hgk)

private theorem l10sf4b_inner_root_long
    {f : ℕ} (hf : 1 ≤ f)
    {β : Fin (f4Datum (GaloisField 2 f)).rank → ℤ}
    (hl : GGLongRoot (f4Datum (GaloisField 2 f)) β) :
    GGRootNormInner ((f4Datum (GaloisField 2 f)).rootGroup β) := by
  obtain ⟨w, γ₀, hγ₀mem, hγ₀max, hβeq⟩ := hl
  have hI0 := l10sf4_inner_maxHeight hf hγ₀mem hγ₀max
  have hct := Short.f4_isCTGroupDatum_exact (GaloisField 2 f)
  set m : adjointGroup .F4 (GaloisField 2 f) :=
    CFSG.LieType.Steinberg.nrep hct w with hm
  have ham : CFSG.LieType.Steinberg.ActsAs (f4Datum (GaloisField 2 f)) m w := by
    rw [hm]
    exact CFSG.LieType.Steinberg.actsAs_nrep hct w
  have hβmap : (f4Datum (GaloisField 2 f)).rootGroup β =
      ((f4Datum (GaloisField 2 f)).rootGroup γ₀).map (MulAut.conj m).toMonoidHom := by
    rw [hβeq, ← ham γ₀ hγ₀mem]
  have hI := ggRootNormInner_map_mulEquiv (MulAut.conj m) hI0
  rwa [← hβmap] at hI

private theorem l10sf4_inner_root
    {f : ℕ} (hf : 1 ≤ f)
    {β : Fin (f4Datum (GaloisField 2 f)).rank → ℤ} (hβ : β ∈ (f4Datum (GaloisField 2 f)).roots) :
    GGRootNormInner ((f4Datum (GaloisField 2 f)).rootGroup β) := by
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  haveI : CharP (GaloisField 2 f) ReeTag.F4.prime := ‹CharP (GaloisField 2 f) 2›
  by_cases hl : GGLongRoot (f4Datum (GaloisField 2 f)) β
  · exact l10sf4b_inner_root_long hf hl
  · obtain ⟨β', -, hmap, -, hlong⟩ :=
      Short.finiteExceptionalAut_F4_map_rootGroup (GaloisField 2 f) hβ
    let φ : MulAut (adjointGroup .F4 (GaloisField 2 f)) :=
      ReeTag.F4.finiteExceptionalAut (GaloisField 2 f)
    have hmapφ : ((f4Datum (GaloisField 2 f)).rootGroup β).map φ.toMonoidHom =
        (f4Datum (GaloisField 2 f)).rootGroup β' := hmap
    have hlβ' : GGLongRoot (f4Datum (GaloisField 2 f)) β' := hlong.mpr hl
    have hI' := l10sf4b_inner_root_long hf hlβ'
    have hββ' : (f4Datum (GaloisField 2 f)).rootGroup β =
        ((f4Datum (GaloisField 2 f)).rootGroup β').map φ.symm.toMonoidHom := by
      have hinj : Function.Injective (Subgroup.map φ.toMonoidHom) :=
        Subgroup.map_injective φ.injective
      apply hinj
      rw [GGRootNorm.map_map_symm, hmapφ]
    rw [hββ']
    exact ggRootNormInner_map_mulEquiv φ.symm hI'

theorem ggRootNormInner_f4
    {n f : ℕ} (hf : 1 ≤ f)
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (u : (ggU .F4 n f).K) :
    GGRootNormInner (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u) := by
  have hI : GGRootNormInner ((ggU .F4 n f).D.rootGroup β) :=
    l10sf4_inner_root hf hβ
  have h := ggRootNormInner_map_mulEquiv (MulAut.conj u) hI
  rw [ggRootSub, Subgroup.map_id]
  exact h

private theorem l10sf4b_inner_range
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : (ggU .F4 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .F4 n f).K)
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (u : (ggU .F4 n f).K) :
    GGRootNormInner ((ggRootSub (ggU .F4 n f).D φ β u).subgroupOf φ.range) := by
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  have hZ : Subgroup.center (ggU .F4 n f).K = ⊥ := by
    change Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥
    exact center_adjointGroup_eq_bot
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hZ))
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have hI : GGRootNormInner
      (((ggU .F4 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
    have h := ggRootNormInner_f4 hf hβ u
    rwa [ggRootSub, Subgroup.map_id] at h
  have hmap := ggRootNormInner_map_mulEquiv (MonoidHom.ofInjective hinj) hI
  have hRbar : (((ggU .F4 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
        (MonoidHom.ofInjective hinj).toMonoidHom =
      ((((ggU .F4 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
        φ).subgroupOf φ.range := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro hr
      exact ⟨(MonoidHom.ofInjective hinj).symm x, hr,
        MonoidHom.apply_ofInjective_symm hinj x⟩
    · rintro ⟨r, hr, hx⟩
      have hx' : MonoidHom.ofInjective hinj r = x := by
        apply Subtype.ext
        simpa only [MonoidHom.ofInjective_apply hinj] using hx
      rw [← hx']
      simpa using hr
  rw [hRbar] at hmap
  exact hmap

theorem ggRootInnerAt_ggU_f4
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : (ggU .F4 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .F4 n f).K)
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (u : (ggU .F4 n f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .F4 n f).D φ β u) := by
  have hI := l10sf4b_inner_range hf φ hker hβ u
  intro Y hY2 hYK hYR hNY
  exact ggRootNormInner_le_sup_centralizer (Subgroup.map_le_range _ _) hYK hYR hY2 hNY hI

theorem itemThree_ggU_f4
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (ψ : (ggU .F4 n f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .F4 n f).K)
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (u : (ggU .F4 n f).K) {R : Subgroup X} (hR : R = ggRootSub (ggU .F4 n f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  have hI := l10sf4b_inner_range hf ψ hker hβ u
  intro Y hY2 hYK hYR hcomm
  refine ggRootNormInner_le_sup_centralizer_of_commutator ?_ hYK hYR hY2 hcomm ?_
  · rw [hR]
    exact Subgroup.map_le_range _ _
  · rw [hR]
    exact hI

end CFSG.StandardType.LieKnownR2.F4
