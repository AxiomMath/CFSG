module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE78Lang
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Reduce
import CFSG.Blueprint.LieModelAPI
import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Base
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
import CFSG.Models.Transport
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def CompE78At (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S →
    β ^ 3 = 1 → β ≠ 1 →
    ∀ K : Subgroup S,
      CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) →
      (∃ K' : Subgroup S,
          CFSG.Open.IsComponentOf K' (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) ∧
            K' ≠ K) ∨
        ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
          TablePThreeKG.E78CompLabel lab

section CompE78

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms

private theorem compE78At_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : CompE78At S) : CompE78At S' := by
  intro b hbmem hbp hb1 K' hK'
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hαp : α ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hbp
  have hα1 : α ≠ 1 := by
    intro h1
    apply hb1
    rw [← hconj, h1, map_one]
  set K : Subgroup S := K'.map (e.symm : S' →* S) with hK
  have hfix : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup b).map (e.symm : S' →* S) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hfix' : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).map (e : S →* S') =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup b := by
    rw [← hfix, Subgroup.map_map]
    simp
  have hKcomp : CFSG.Open.IsComponentOf K
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  rcases h α hαmem hαp hα1 K hKcomp with ⟨K'', hK''c, hK''ne⟩ | ⟨lab, hlab1, hlab2, hlabE⟩
  · refine Or.inl ⟨K''.map (e : S →* S'), ?_, ?_⟩
    · have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK''c
      rwa [hfix'] at this
    · intro hEq
      apply hK''ne
      have h1 : (K''.map (e : S →* S')).map (e.symm : S' →* S) = K'' := by
        rw [Subgroup.map_map]; simp
      have h2 : (K''.map (e : S →* S')).map (e.symm : S' →* S) = K := by
        rw [hEq, hK]
      exact h1.symm.trans h2
  · have hKmap : K.map (e : S →* S') = K' := by
      rw [hK, Subgroup.map_map]; simp
    let ε : ↥K ≃* ↥K' :=
      (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
    let θ : ↥K ⧸ Subgroup.center ↥K ≃* ↥K' ⧸ Subgroup.center ↥K' :=
      QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)
    have hhas' : GGHasLabel lab (↥K' ⧸ Subgroup.center ↥K') := by
      unfold GGHasLabel at hlab2 ⊢
      refine largeEvenRawDatum_mono ?_ hlab2
      rintro R' _ I F ⟨ψ⟩
      exact ⟨θ.symm.trans ψ⟩
    exact Or.inr ⟨lab, hlab1, hhas', hlabE⟩

private theorem compE78At_adjointGroup
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8) : CompE78At ↥(adjointGroup τ K) := by
  classical
  intro β hβmem hβp hβ1 J hJ
  have hτE : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h <;> simp [h]
  obtain ⟨h, hh, hβh, hp1, hh1⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
      hτE Nat.prime_three β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : 3 ≠ ringChar K := by rw [hK2]; norm_num
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK, hK2]
    intro hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos Nat.prime_three (by norm_num) hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hτ5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h <;> simp [h]
  have hτ6 : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h <;> simp [h]
  have hτs : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h <;> simp [h]
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ6 Nat.prime_three
      (by norm_num)
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    CFSG.LieType.Chevalley.single_edge_perfect τ K hτs
  obtain ⟨S, a, ι, hSq, _, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ5 Nat.prime_three hpK hp₀ hp₀K hq₀' hmon hperf
      β h (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hℓ2 : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  haveI : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three (by rw [hℓL]; exact hpℓ.symm)
  have hτne : τ ≠ .G2 := by
    rintro rfl
    rcases hτ with h | h <;> exact absurd h (by decide)
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hpL
    (fun hG2 => absurd hG2 hτne) hT hap h1
  obtain ⟨i, hqs, hJR⟩ :=
    components_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap h1 hTame hJ
  rcases TablePThreeKG.langE78_comp_cases hτ S hT hap h1 i hqs with
    ⟨j, hqsj, hRjne⟩ | ⟨lab, hlab, hlabE⟩
  ·
    have hcompRj : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) j)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) :=
      CFSG.HardMathSupport.Dickson.Sec6.isComponentOf_rationalComponent S hT j hqsj
    have hRjrange : rationalComponent S.ρ S.Γ (rootCharHom a) j ≤ ι.range := by
      rw [hrange]
      exact (langSubnormal_of_mem_torus S hT j).1.trans inf_le_left
    have hCd : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ≤ ι.range := by
      rw [hrange]; exact inf_le_left
    have hfixmap : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β).map ι =
        S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hinj β
        (rootDiagUnit τ a) hconj, hrange]
    have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}).comap ι =
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β := by
      rw [← hfixmap]
      exact Subgroup.comap_map_eq_self_of_injective hinj _
    refine Or.inl ⟨(rationalComponent S.ρ S.Γ (rootCharHom a) j).comap ι, ?_, ?_⟩
    · have h := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isComponentOf_comap_of_injective
        ι hinj hRjrange hCd hcompRj
      rwa [hcomapfix] at h
    · intro hEq
      exact hRjne (by
        have h := congrArg (Subgroup.map ι) hEq
        rw [Subgroup.map_comap_eq_self hRjrange, hJR] at h
        exact h)
  ·
    obtain ⟨hlab1, hlab2⟩ := hlab
    let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
    let θ : ↥J ⧸ Subgroup.center ↥J ≃*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
    have hhasJ : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
      unfold GGHasLabel at hlab2 ⊢
      refine largeEvenRawDatum_mono ?_ hlab2
      rintro R' _ I F ⟨ψ⟩
      exact ⟨θ.trans ψ⟩
    exact Or.inr ⟨lab, hlab1, hhasJ, hlabE⟩

end CompE78

theorem compE78_cat_of_lang
    (d : TauCeti.ValidLieTypeIndex) (hch : d.1.characteristic = 2)
    (hd : (∃ q, d.1 = .E7 q) ∨ ∃ q, d.1 = .E8 q) : CompE78At (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨e, hv⟩ := d
  rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩
  · subst hq
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    haveI := hKc
    have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_E7 q).symm.trans hch
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hK2 : ringChar K = 2 := hchar.trans hqp
    exact compE78At_of_mulEquiv eK.symm (compE78At_adjointGroup (K := K) hK2 (Or.inl rfl))
  · subst hq
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    haveI := hKc
    have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_E8 q).symm.trans hch
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hK2 : ringChar K = 2 := hchar.trans hqp
    exact compE78At_of_mulEquiv eK.symm (compE78At_adjointGroup (K := K) hK2 (Or.inr rfl))

end CFSG.StandardType

end
