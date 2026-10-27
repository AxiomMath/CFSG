module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc

public section

namespace CFSG.StandardType.RCKSmall

section Classes

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynE (TagLieType IsADETag)

open CFSG.LocalAnalysis.GLTheoremA.S265C.DynE (isADETag_of_typeA isADETag_of_innerDE
  isADETag_POmegaMinus isADETag_twistedE6 tagLie_rationalComponent_typeA tagLie_inner_nonA_E7
  tagLie_inner_nonA_E8 tagLie_rationalComponent_outerD_high tagLie_rank_four_E6
  tagLie_rationalComponent_of_d4_outer d4_outer_htri_of_layer d4SwapLayerTag_of_leafSwap
  d4TrialityLayerTag_of_leafCycle tagLie_rationalComponent_E6)

open scoped Matrix MatrixGroups

theorem rck_tagLie_rank_four
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TagLieType (fun t => t = .POmegaMinus ∨ t = .trialityD4) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hE6 := e6FixDNAll_proved
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 => exact tagLie_rank_four_E6 S hp hpL hT hTp i hr hc hnin
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact tagLie_rationalComponent_of_d4_outer
      (tagP := fun t => t = .POmegaMinus ∨ t = .trialityD4)
      d4Base_E7 (d4SwapLayer_E7 hE6) (d4SwapLayerTag_of_leafSwap leafSwap_E7) (Or.inl rfl)
      S hFr hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin
      (d4_outer_htri_of_layer d4TrialityLayer_E7
        (d4TrialityLayerTag_of_leafCycle leafCycle_E7) (Or.inr rfl) S hFr hΦ hn v)
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact tagLie_rationalComponent_of_d4_outer
      (tagP := fun t => t = .POmegaMinus ∨ t = .trialityD4)
      d4Base_E8 (d4SwapLayer_E8 hE6) (d4SwapLayerTag_of_leafSwap leafSwap_E8) (Or.inl rfl)
      S hFr hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin
      (d4_outer_htri_of_layer d4TrialityLayer_E8
        (d4TrialityLayerTag_of_leafCycle leafCycle_E8) (Or.inr rfl) S hFr hΦ hn v)

theorem rck_tagLie_rationalComponent_outerD
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hshape : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TagLieType (fun t => t = .POmegaMinus ∨ t = .trialityD4) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · exact (tagLie_rationalComponent_outerD_high S hp hT hap h1 i h5 hshape.2 hout).mono
      fun _ ht => Or.inl ht
  · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
      rw [hshape.2, hr4]
    have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    exact rck_tagLie_rank_four S hp hpL hT hTp h1 i hr4 hc hout

theorem rck_tagLie_rationalComponent_E7
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E7 L p₀) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E7.rank → Lˣ}
    (hT : rootDiagUnit Tag.E7 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.E7 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    TagLieType (fun t => IsADETag t ∨ t = .trialityD4) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact (tagLie_rationalComponent_typeA S hp hT hap h1 i hA hq).mono
      fun _ ht => Or.inl (isADETag_of_typeA ht)
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact (tagLie_inner_nonA_E7 S hp hpL hT hTp i hA hinner).mono
      fun _ ht => Or.inl (isADETag_of_innerDE ht)
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact (rck_tagLie_rationalComponent_outerD S hp hT hap h1 i hD' hinner).mono
        fun _ ht => ht.elim (fun h => Or.inl (h ▸ isADETag_POmegaMinus)) fun h => Or.inr h
    · obtain ⟨f, -, -, hlie⟩ :=
        lieModel_rationalComponent_of_outer_E7 S hp hpL hT hTp i hE'.1 hE'.2 hinner
      exact ⟨.twistedE6, 0, f, Or.inl isADETag_twistedE6, hlie⟩

theorem rck_tagLie_rationalComponent_E8
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit Tag.E8 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.E8 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    TagLieType (fun t => IsADETag t ∨ t = .trialityD4) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact (tagLie_rationalComponent_typeA S hp hT hap h1 i hA hq).mono
      fun _ ht => Or.inl (isADETag_of_typeA ht)
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact (tagLie_inner_nonA_E8 S hp hpL hT hTp i hA hinner).mono
      fun _ ht => Or.inl (isADETag_of_innerDE ht)
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact (rck_tagLie_rationalComponent_outerD S hp hT hap h1 i hD' hinner).mono
        fun _ ht => ht.elim (fun h => Or.inl (h ▸ isADETag_POmegaMinus)) fun h => Or.inr h
    · obtain ⟨f, -, -, hlie⟩ :=
        lieModel_rationalComponent_of_outer_E8 S hp hpL hT hTp i hE'.1 hE'.2 hinner
      exact ⟨.twistedE6, 0, f, Or.inl isADETag_twistedE6, hlie⟩

theorem rck_tagLie_rationalComponent_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    TagLieType (fun t => IsADETag t ∨ t = .trialityD4) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  rcases hτ with rfl | rfl | rfl
  · exact tagLie_rationalComponent_E6 S hp hT hap h1 i hq
  · exact rck_tagLie_rationalComponent_E7 S hp hT hap h1 i hq
  · exact rck_tagLie_rationalComponent_E8 S hp hT hap h1 i hq

end Classes

end CFSG.StandardType.RCKSmall
