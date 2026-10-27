module

public import CFSG.Quasithin.EmptyFaithful.S146xThreeA
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section CompGlue

variable {G : Type} [Group G] [Finite G]

theorem cComp_eq_of_le_iSup {H L : Subgroup G} {ι : Type} {F : ι → Subgroup G}
    (hL : L ∈ cComp H) (hF : ∀ i, F i ∈ cComp H) (hle : L ≤ ⨆ i, F i) : ∃ i, L = F i := by
  classical
  by_contra hcon
  push Not at hcon
  have hHL : L ≤ H := le_of_mem_cComp hL
  have hHF : ∀ i, F i ≤ H := fun i => le_of_mem_cComp (hF i)
  set N : Subgroup ↥H := CFSG.solvableRadical ↥H with hN
  set π : ↥H →* ↥H ⧸ N := QuotientGroup.mk' N with hπ
  have hFc : ∀ i, ((F i).subgroupOf H).map π ≤
      Subgroup.centralizer (((L.subgroupOf H).map π : Subgroup _) : Set _) := by
    intro i
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact cComp_ne_map_commutator_eq_bot hL (hF i) (hcon i)
  have hsub : L.subgroupOf H ≤ ⨆ i, (F i).subgroupOf H := by
    intro x hx
    have hx1 : (x : G) ∈ ⨆ i, F i := hle hx
    have h2 : (⨆ i, (F i).subgroupOf H).map H.subtype = ⨆ i, F i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => Subgroup.map_subgroupOf_eq_of_le (hHF i)
    rw [← h2] at hx1
    obtain ⟨y, hy, hyx⟩ := hx1
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hL'le : (L.subgroupOf H).map π ≤ ⨆ i, ((F i).subgroupOf H).map π := by
    rw [← Subgroup.map_iSup]
    exact Subgroup.map_mono hsub
  have hLc : (L.subgroupOf H).map π ≤
      Subgroup.centralizer (((L.subgroupOf H).map π : Subgroup _) : Set _) :=
    hL'le.trans (iSup_le hFc)
  have hLL : ⁅(L.subgroupOf H).map π, (L.subgroupOf H).map π⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLc
  have hperf : ⁅L.subgroupOf H, L.subgroupOf H⁆ = L.subgroupOf H := by
    apply Subgroup.map_injective (f := H.subtype) H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hHL]
    exact perfect_of_mem_cComp hL
  have hker : L.subgroupOf H ≤ N := by
    have h3 : (L.subgroupOf H).map π = ⊥ := by
      conv_lhs => rw [← hperf]
      rw [Subgroup.map_commutator]
      exact hLL
    have h4 := (Subgroup.map_eq_bot_iff _).mp h3
    rwa [hπ, QuotientGroup.ker_mk'] at h4
  have hLrad : L ≤ solvRad H := by
    rw [solvRad_eq_map_solvableRadical]
    intro l hl
    exact ⟨⟨l, hHL hl⟩, hker hl, rfl⟩
  have := solvRad_isSolvable H
  have hsolv : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLrad)
      (Subgroup.inclusion_injective hLrad)
  exact not_isSolvable_of_mem_cComp hL hsolv

omit [Finite G] in
theorem cjSub_one_eq (K : Subgroup G) : cjSub 1 K = K := by
  ext x
  simp [mem_cjSub]

omit [Finite G] in
theorem conjSub_eq_cjSub (t : G) (K : Subgroup G) : B6.conjSub t K = cjSub t K := by
  ext x
  rw [B6.mem_conjSub, mem_cjSub]

omit [Finite G] in
theorem cjSub_mem_cComp {H K : Subgroup G} (hK : K ∈ cComp H) {t : G} (ht : t ∈ H) :
    cjSub t K ∈ cComp H := by
  rw [← conjSub_eq_cjSub]
  exact conjSub_mem_cComp_of_mem hK ht

omit [Finite G] in
theorem cjSub_cjSub_eq (s t : G) (K : Subgroup G) : cjSub s (cjSub t K) = cjSub (s * t) K := by
  ext x
  simp [mem_cjSub, mul_assoc]

theorem exists_cjSub_eq_of_cComp {I S K L : Subgroup G} (hK : K ∈ cComp I) (hIK : I = K ⊔ S)
    (hS : Group.IsSolvable S) (hL : L ∈ cComp I) : ∃ s ∈ S, L = cjSub s K := by
  have hKI : K ≤ I := le_of_mem_cComp hK
  have hSI : S ≤ I := hIK ▸ le_sup_right
  set K₀ : Subgroup G := ⨆ s : S, cjSub (s : G) K with hK₀
  have hF : ∀ s : S, cjSub (s : G) K ∈ cComp I := fun s => cjSub_mem_cComp hK (hSI s.2)
  have hK₀I : K₀ ≤ I := iSup_le fun s => le_of_mem_cComp (hF s)
  have hKK₀ : K ≤ K₀ := by
    refine le_trans ?_ (le_iSup (fun s : S => cjSub (s : G) K) ⟨1, S.one_mem⟩)
    rw [show ((⟨1, S.one_mem⟩ : S) : G) = 1 from rfl, cjSub_one_eq]
  have hcj : ∀ s ∈ S, cjSub s K₀ ≤ K₀ := by
    intro s hs
    rw [hK₀, cjSub, Subgroup.map_iSup]
    refine iSup_le fun t => ?_
    have : Subgroup.map (MulAut.conj s).toMonoidHom (cjSub (t : G) K) = cjSub (s * t) K :=
      cjSub_cjSub_eq s t K
    rw [this]
    exact le_iSup (fun u : S => cjSub (u : G) K) ⟨s * t, S.mul_mem hs t.2⟩
  have hSnorm : S ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hcj s hs ((mem_cjSub (g := s) (A := K₀)).mpr (by simpa [mul_assoc] using hx))
    · intro hx
      have h1 := hcj s⁻¹ (S.inv_mem hs)
        ((mem_cjSub (g := s⁻¹) (A := K₀)).mpr (by simpa [mul_assoc] using hx))
      simpa using h1
  have hnorm : I ≤ Subgroup.normalizer (K₀ : Set G) := by
    rw [hIK]
    exact sup_le (hKK₀.trans Subgroup.le_normalizer) hSnorm
  have hnormal : (K₀.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀I).mpr hnorm
  have hIeq : I = K₀ ⊔ S := by
    refine le_antisymm ?_ (sup_le hK₀I hSI)
    rw [hIK]
    exact sup_le_sup_right hKK₀ S
  have hperf : perfectCore I ≤ K₀ := perfectCore_le_of_sup_solvable hK₀I hnormal hIeq hS
  have hLK₀ : L ≤ K₀ :=
    (le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)).trans hperf
  obtain ⟨s, hs⟩ := cComp_eq_of_le_iSup hL hF hLK₀
  exact ⟨s, s.2, hs⟩

theorem isComponentIn_of_cComp_of_exists {I S K : Subgroup G} (hK : K ∈ cComp I)
    (hIK : I = K ⊔ S) (hS : Group.IsSolvable S) (hex : ∃ L : Subgroup G, IsComponentIn L I) :
    IsComponentIn K I := by
  obtain ⟨L, hL⟩ := hex
  have hLc : L ∈ cComp I := Id2519.mem_cComp_of_isComponentIn hL
  obtain ⟨s, -, hLs⟩ := exists_cjSub_eq_of_cComp hK hIK hS hLc
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have e : ↥K ≃* ↥(cjSub s K) :=
    Subgroup.equivMapOfInjective K (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
  have hKq : CFSG.IsQuasisimple ↥K := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm ?_
    rw [← hLs]
    exact hLq
  exact Id2519.isComponentIn_of_mem_cComp hK hKq

end CompGlue

end CFSG.Quasithin
