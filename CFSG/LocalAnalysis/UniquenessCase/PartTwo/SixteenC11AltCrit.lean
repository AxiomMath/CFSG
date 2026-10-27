module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltVec
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Foote.E27.TableMat
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyOddOMinus
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma5_2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Data.E27Q2O
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin
open scoped Pointwise

@[expose] def S16C11AltTriple {n : ℕ} (x₀ xa xb : Fin n → ZMod 2) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ v ∈ [x₀, xa, xb], ∃ w ∈ [x₀, xa, xb], S16C11AltEqv w (S16C11AltPact g v)

open scoped CFSG.Decide.Bounded in
instance {n : ℕ} (x₀ xa xb : Fin n → ZMod 2) (g : Equiv.Perm (Fin n)) :
    Decidable (S16C11AltTriple x₀ xa xb g) := by
  unfold S16C11AltTriple
  infer_instance

theorem s16c11_alt_sw2_mem {n : ℕ} (a b c d : Fin n) (h₁ : a ≠ b) (h₂ : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h₁,
    Equiv.Perm.sign_swap h₂]
  decide

@[expose] def S16C11AltSw2 {n : ℕ} (a b c d : Fin n) (h₁ : a ≠ b) (h₂ : c ≠ d) :
    ↥(alternatingGroup (Fin n)) :=
  ⟨Equiv.swap a b * Equiv.swap c d, s16c11_alt_sw2_mem a b c d h₁ h₂⟩

instance s16c11AltModFinite (n : ℕ) : Finite (FFModel.altDn n).Mod := by
  haveI : Finite (FFModel.altDn n).Amb := by
    unfold FFModel.altDn
    exact inferInstance
  exact inferInstanceAs (Finite (↥(FFModel.altDn n).sec ⧸
    (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec))

private theorem s16c11_altcrit_mem_triple_set_iff {n : ℕ}
    {x₀ xa xb u : Fin n → ZMod 2} (h₀ : ∑ i, x₀ i = 0) (ha : ∑ i, xa i = 0)
    (hb : ∑ i, xb i = 0) (hu : ∑ i, u i = 0) :
    S16C11AltCls n u ∈
        ({S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb} :
          Set (FFModel.altDn n).Mod) ↔
      ∃ w ∈ [x₀, xa, xb], S16C11AltEqv w u := by
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h)
    · exact ⟨x₀, by simp, (s16c11_alt_eqv_comm u x₀).mp
        ((s16c11_alt_cls_eq_iff hu h₀).mp h)⟩
    · exact ⟨xa, by simp, (s16c11_alt_eqv_comm u xa).mp
        ((s16c11_alt_cls_eq_iff hu ha).mp h)⟩
    · exact ⟨xb, by simp, (s16c11_alt_eqv_comm u xb).mp
        ((s16c11_alt_cls_eq_iff hu hb).mp h)⟩
  · rintro ⟨w, hw, hwu⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with h0 | h0 | h0
    · rw [h0] at hwu
      exact Or.inl ((s16c11_alt_cls_eq_iff hu h₀).mpr
        ((s16c11_alt_eqv_comm x₀ u).mp hwu))
    · rw [h0] at hwu
      exact Or.inr (Or.inl ((s16c11_alt_cls_eq_iff hu ha).mpr
        ((s16c11_alt_eqv_comm xa u).mp hwu)))
    · rw [h0] at hwu
      exact Or.inr (Or.inr ((s16c11_alt_cls_eq_iff hu hb).mpr
        ((s16c11_alt_eqv_comm xb u).mp hwu)))

private theorem s16c11_altcrit_orbit_finset_subset {n : ℕ} [DecidableEq (FFModel.altDn n).Mod]
    {v : Fin n → ZMod 2}
    (hv : ∑ i, v i = 0) (cs : List (Fin n → ZMod 2))
    (h : ∀ g : Equiv.Perm (Fin n), ∃ w ∈ cs, S16C11AltPact g v = w) :
    {z : (FFModel.altDn n).Mod |
        ∃ g : ↥(alternatingGroup (Fin n)), S16C11AltAct n g (S16C11AltCls n v) = z} ⊆
      ↑((cs.map (S16C11AltCls n)).toFinset : Finset (FFModel.altDn n).Mod) := by
  intro z hz
  obtain ⟨g, rfl⟩ := hz
  obtain ⟨w, hw, hwv⟩ := h (g : Equiv.Perm (Fin n))
  rw [s16c11_alt_act_cls g hv, hwv]
  rw [Finset.mem_coe, List.mem_toFinset]
  exact List.mem_map.mpr ⟨w, hw, rfl⟩

theorem s16c11_alt_fixed_iff {n : ℕ} (g : ↥(alternatingGroup (Fin n))) {x : Fin n → ZMod 2}
    (hx : ∑ i, x i = 0) :
    S16C11AltAct n g (S16C11AltCls n x) = S16C11AltCls n x ↔
      S16C11AltEqv x (S16C11AltPact (g : Equiv.Perm (Fin n)) x) := by
  rw [s16c11_alt_act_cls g hx,
    s16c11_alt_cls_eq_iff (by rw [s16c11_alt_sum_pact]; exact hx) hx]
  exact s16c11_alt_eqv_comm _ x

theorem s16c11_alt_mem_setStab_iff {n : ℕ} {x₀ xa xb : Fin n → ZMod 2} (h₀ : ∑ i, x₀ i = 0)
    (ha : ∑ i, xa i = 0) (hb : ∑ i, xb i = 0) (g : ↥(alternatingGroup (Fin n))) :
    g ∈ S16C11SetStab (S16C11AltAct n)
        {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb} ↔
      S16C11AltTriple x₀ xa xb (g : Equiv.Perm (Fin n)) := by
  let Y : Set (FFModel.altDn n).Mod :=
    {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb}
  change g ∈ S16C11SetStab (S16C11AltAct n) Y ↔
    S16C11AltTriple x₀ xa xb (g : Equiv.Perm (Fin n))
  have hmem_iff : ∀ u : Fin n → ZMod 2, (∑ i, u i = 0) →
      (S16C11AltCls n u ∈ Y ↔ ∃ w ∈ [x₀, xa, xb], S16C11AltEqv w u) := by
    intro u hu
    simpa only [Y] using s16c11_altcrit_mem_triple_set_iff (n := n) h₀ ha hb hu
  have hP0 : ∀ t : ↥(alternatingGroup (Fin n)),
      ∑ i, S16C11AltPact (t : Equiv.Perm (Fin n)) x₀ i = 0 := by
    intro t
    rw [s16c11_alt_sum_pact]
    exact h₀
  have hPa : ∀ t : ↥(alternatingGroup (Fin n)),
      ∑ i, S16C11AltPact (t : Equiv.Perm (Fin n)) xa i = 0 := by
    intro t
    rw [s16c11_alt_sum_pact]
    exact ha
  have hPb : ∀ t : ↥(alternatingGroup (Fin n)),
      ∑ i, S16C11AltPact (t : Equiv.Perm (Fin n)) xb i = 0 := by
    intro t
    rw [s16c11_alt_sum_pact]
    exact hb
  constructor
  · intro hstab v hv
    have hv0 : ∑ i, v i = 0 := by
      have hv' : v = x₀ ∨ v = xa ∨ v = xb := by
        simpa only [List.mem_cons, List.mem_nil_iff, or_false] using hv
      rcases hv' with h0 | h0 | h0
      · rw [h0]; exact h₀
      · rw [h0]; exact ha
      · rw [h0]; exact hb
    have hvY : S16C11AltCls n v ∈ Y :=
      (hmem_iff v hv0).mpr ⟨v, hv, Or.inl rfl⟩
    have hmem : S16C11AltAct n g ∈
        MulAction.stabilizer (MulAut (FFModel.altDn n).Mod) Y := by
      have h : g ∈ (MulAction.stabilizer (MulAut (FFModel.altDn n).Mod) Y).comap
          (S16C11AltAct n) := by
        rwa [S16C11SetStab] at hstab
      exact Subgroup.mem_comap.1 h
    have hsm : (S16C11AltAct n g) • (S16C11AltCls n v) ∈ Y :=
      ((MulAction.mem_stabilizer_set.mp hmem) (S16C11AltCls n v)).mpr hvY
    have hgY : S16C11AltCls n (S16C11AltPact (g : Equiv.Perm (Fin n)) v) ∈ Y :=
      (s16c11_alt_act_cls g hv0).symm ▸ hsm
    have hv0' : ∑ i, S16C11AltPact (g : Equiv.Perm (Fin n)) v i = 0 := by
      rw [s16c11_alt_sum_pact]; exact hv0
    exact (hmem_iff _ hv0').mp hgY
  · intro htriple
    have hsub : (S16C11AltAct n g) '' Y ⊆ Y := by
      intro y hy
      obtain ⟨b, hbY, rfl⟩ := hy
      have hb' : b = S16C11AltCls n x₀ ∨ b = S16C11AltCls n xa ∨
          b = S16C11AltCls n xb := by
        simpa only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] using hbY
      rcases hb' with h0 | h0 | h0
      · rw [h0]
        exact (s16c11_alt_act_cls g h₀).symm ▸
          (hmem_iff _ (hP0 g)).mpr (htriple x₀ (by simp))
      · rw [h0]
        exact (s16c11_alt_act_cls g ha).symm ▸
          (hmem_iff _ (hPa g)).mpr (htriple xa (by simp))
      · rw [h0]
        exact (s16c11_alt_act_cls g hb).symm ▸
          (hmem_iff _ (hPb g)).mpr (htriple xb (by simp))
    have heq : (S16C11AltAct n g) '' Y = Y := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_
      rw [Set.ncard_image_of_injective Y (S16C11AltAct n g).injective]
    have hmem : (S16C11AltAct n) g ∈
        MulAction.stabilizer (MulAut (FFModel.altDn n).Mod) Y := by
      rw [MulAction.mem_stabilizer_iff]
      refine (Set.image_smul (a := (S16C11AltAct n) g) (t := Y)).symm.trans ?_
      simpa using heq
    rw [S16C11SetStab]
    exact Subgroup.mem_comap.2 hmem

theorem s16c11_alt_two_lt_ncard_orbit {n : ℕ} {T : Subgroup ↥(alternatingGroup (Fin n))}
    {v : Fin n → ZMod 2} (hv : ∑ i, v i = 0) {t₁ t₂ : ↥(alternatingGroup (Fin n))} (h₁ : t₁ ∈ T)
    (h₂ : t₂ ∈ T) (c₁ : ¬ S16C11AltEqv v (S16C11AltPact (t₁ : Equiv.Perm (Fin n)) v))
    (c₂ : ¬ S16C11AltEqv v (S16C11AltPact (t₂ : Equiv.Perm (Fin n)) v))
    (c₃ : ¬ S16C11AltEqv (S16C11AltPact (t₁ : Equiv.Perm (Fin n)) v)
      (S16C11AltPact (t₂ : Equiv.Perm (Fin n)) v)) :
    2 < {w : (FFModel.altDn n).Mod | ∃ t ∈ T, S16C11AltAct n t (S16C11AltCls n v) = w}.ncard := by
  let O : Set (FFModel.altDn n).Mod :=
    {w | ∃ t ∈ T, S16C11AltAct n t (S16C11AltCls n v) = w}
  change 2 < O.ncard
  let p := S16C11AltCls n v
  let q := S16C11AltCls n (S16C11AltPact (t₁ : Equiv.Perm (Fin n)) v)
  let r := S16C11AltCls n (S16C11AltPact (t₂ : Equiv.Perm (Fin n)) v)
  have hq0 : ∑ i, S16C11AltPact (t₁ : Equiv.Perm (Fin n)) v i = 0 := by
    rw [s16c11_alt_sum_pact]; exact hv
  have hr0 : ∑ i, S16C11AltPact (t₂ : Equiv.Perm (Fin n)) v i = 0 := by
    rw [s16c11_alt_sum_pact]; exact hv
  have hpq : p ≠ q := fun h => c₁ ((s16c11_alt_cls_eq_iff hv hq0).mp h)
  have hpr : p ≠ r := fun h => c₂ ((s16c11_alt_cls_eq_iff hv hr0).mp h)
  have hqr : q ≠ r := fun h => c₃ ((s16c11_alt_cls_eq_iff hq0 hr0).mp h)
  have hthree : ({p, q, r} : Set (FFModel.altDn n).Mod).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have hsub : ({p, q, r} : Set (FFModel.altDn n).Mod) ⊆ O := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨1, T.one_mem, ?_⟩
      show (S16C11AltAct n (1 : (FFModel.altDn n).Gam)) (S16C11AltCls n v) = p
      rw [map_one]
      rfl
    · exact ⟨t₁, h₁, by simpa only [p, q] using s16c11_alt_act_cls t₁ hv⟩
    · exact ⟨t₂, h₂, by simpa only [p, r] using s16c11_alt_act_cls t₂ hv⟩
  have hle : 3 ≤ O.ncard := by
    rw [← hthree]
    exact Set.ncard_le_ncard hsub
  exact lt_of_lt_of_le (by norm_num) hle

theorem s16c11_alt_le_ncard_orbit {n : ℕ} {v : Fin n → ZMod 2} (hv : ∑ i, v i = 0)
    (L : List ↥(alternatingGroup (Fin n)))
    (hL : (L.map fun g => S16C11AltPact (g : Equiv.Perm (Fin n)) v).Pairwise
      fun a b => ¬ S16C11AltEqv a b) :
    L.length ≤ {z : (FFModel.altDn n).Mod |
      ∃ g : ↥(alternatingGroup (Fin n)), S16C11AltAct n g (S16C11AltCls n v) = z}.ncard := by
  classical
  let O : Set (FFModel.altDn n).Mod :=
    {z | ∃ g : ↥(alternatingGroup (Fin n)), S16C11AltAct n g (S16C11AltCls n v) = z}
  change L.length ≤ O.ncard
  have hvec : (L.map fun g => S16C11AltPact (g : Equiv.Perm (Fin n)) v).Pairwise
      (fun a b => S16C11AltCls n a ≠ S16C11AltCls n b) := by
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hL
    obtain ⟨a', -, ha'⟩ := List.mem_map.mp ha
    obtain ⟨b', -, hb'⟩ := List.mem_map.mp hb
    intro h
    have ha0 : ∑ i, a i = 0 := by rw [← ha', s16c11_alt_sum_pact]; exact hv
    have hb0 : ∑ i, b i = 0 := by rw [← hb', s16c11_alt_sum_pact]; exact hv
    exact hab ((s16c11_alt_cls_eq_iff ha0 hb0).mp h)
  have hpw : ((L.map fun g => S16C11AltPact (g : Equiv.Perm (Fin n)) v).map
      (S16C11AltCls n)).Pairwise (· ≠ ·) :=
    hvec.map (S16C11AltCls n) (fun _ _ h => h)
  have hcard : ((L.map fun g => S16C11AltPact (g : Equiv.Perm (Fin n)) v).map
      (S16C11AltCls n)).toFinset.card = L.length := by
    rw [List.toFinset_card_of_nodup hpw]
    simp [List.length_map, List.length_flatMap]
  have hsub : (↑((L.map fun g => S16C11AltPact (g : Equiv.Perm (Fin n)) v).map
      (S16C11AltCls n)).toFinset : Set (FFModel.altDn n).Mod) ⊆ O := by
    intro z hz
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    obtain ⟨a, ha, haw⟩ := List.mem_map.mp hw
    obtain ⟨g, hgL, hga⟩ := List.mem_flatMap.mp ha
    have hgaeq : a = (g : Equiv.Perm (Fin n)) := List.mem_singleton.mp hga
    refine ⟨g, ?_⟩
    exact (s16c11_alt_act_cls g hv).trans
      ((congrArg (S16C11AltCls n) (by rw [← hgaeq]; exact haw)).trans hwz)
  calc L.length = ((L.map fun g => S16C11AltPact (g : Equiv.Perm (Fin n)) v).map
        (S16C11AltCls n)).toFinset.card := hcard.symm
    _ = (↑((L.map fun g => S16C11AltPact (g : Equiv.Perm (Fin n)) v).map
          (S16C11AltCls n)).toFinset : Set (FFModel.altDn n).Mod).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ O.ncard := Set.ncard_le_ncard hsub

theorem s16c11_alt_ncard_orbit_le {n : ℕ} {v : Fin n → ZMod 2} (hv : ∑ i, v i = 0)
    (cs : List (Fin n → ZMod 2))
    (h : ∀ g : Equiv.Perm (Fin n), ∃ w ∈ cs, S16C11AltPact g v = w) :
    {z : (FFModel.altDn n).Mod |
      ∃ g : ↥(alternatingGroup (Fin n)), S16C11AltAct n g (S16C11AltCls n v) = z}.ncard ≤
        cs.length := by
  classical
  let O : Set (FFModel.altDn n).Mod :=
    {z | ∃ g : ↥(alternatingGroup (Fin n)), S16C11AltAct n g (S16C11AltCls n v) = z}
  change O.ncard ≤ cs.length
  calc O.ncard ≤ (↑((cs.map (S16C11AltCls n)).toFinset :
          Finset (FFModel.altDn n).Mod) : Set (FFModel.altDn n).Mod).ncard :=
        Set.ncard_le_ncard (s16c11_altcrit_orbit_finset_subset hv cs h)
    _ = ((cs.map (S16C11AltCls n)).toFinset).card := Set.ncard_coe_finset _
    _ ≤ (cs.map (S16C11AltCls n)).length := List.toFinset_card_le _
    _ = cs.length := List.length_map _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
