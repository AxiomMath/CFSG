module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
import CFSG.LocalAnalysis.StandardType.GGTablePThreeF4Lang
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

open CFSG CFSG.Assembly CFSG.StandardType.LangRat

@[expose] def CompF4BCAt (d : TauCeti.LieTypeIndex) (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S →
    β ^ 3 = 1 → β ≠ 1 →
    ∀ K : Subgroup S,
      CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) →
      (∃ K' : Subgroup S,
          CFSG.Open.IsComponentOf K' (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) ∧
            K' ≠ K) ∨
        ∃ (F : Type) (_ : Field F) (_ : Finite F),
          Nat.card F = CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d ∧
            Nonempty (↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (LargeEvenSpGroup F 3))

section CompF4BC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms

private theorem compF4BCAt_of_mulEquiv {d : TauCeti.LieTypeIndex} {S S' : Type} [Group S]
    [Group S'] (e : S ≃* S') (h : CompF4BCAt d S) : CompF4BCAt d S' := by
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
  rcases h α hαmem hαp hα1 K hKcomp with ⟨K'', hK''c, hK''ne⟩ | ⟨F, hF, hFin, hcard, hdata⟩
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
  · refine Or.inr ⟨F, hF, hFin, hcard, ?_⟩
    have hKmap : K.map (e : S →* S') = K' := by
      rw [hK, Subgroup.map_map]; simp
    let ε : ↥K ≃* ↥K' :=
      (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
    obtain ⟨eR⟩ := hdata
    exact ⟨(QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K') ε
      (Subgroup.map_center_eq ε)).symm.trans eR⟩

private theorem compF4BCAt_adjointGroup
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {d : TauCeti.LieTypeIndex}
    (hdf : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d = Nat.card K) :
    CompF4BCAt d ↥(adjointGroup .F4 K) := by
  classical
  intro β hβmem hβp hβ1 J hJ
  obtain ⟨h, hh, hβh, hp1, hh1⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_F4
      β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : 3 ≠ ringChar K := by rw [hK2]; norm_num
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK, hK2]
    intro hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    exists_setup_prime hℓ f.pos Nat.prime_three (by norm_num) hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : MonomialToralAt Tag.F4 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (Or.inr (Or.inl rfl)) Nat.prime_three (by norm_num)
  have hperf : commutator ↥(adjointGroup .F4 K) = ⊤ :=
    single_edge_perfect Tag.F4 K (Or.inl rfl)
  obtain ⟨S, a, ι, hSq, _, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (Or.inr (Or.inl rfl)) Nat.prime_three hpK
      hp₀ hp₀K hq₀' hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hℓ2 : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  haveI : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three (by rw [hℓL]; exact hpℓ.symm)
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hpL
    (fun hG2 => absurd hG2 (by decide)) hT hap h1
  obtain ⟨i, hqs, hJR⟩ :=
    components_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap h1 hTame hJ
  rcases langF4_comp_cases S hT hap h1 i hqs with
    ⟨j, hqsj, hRjne⟩ | ⟨F, hF, hFin, hcardF, hdata⟩
  ·
    have hcompRj : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) j)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a}) :=
      CFSG.HardMathSupport.Dickson.Sec6.isComponentOf_rationalComponent S hT j hqsj
    have hRjrange : rationalComponent S.ρ S.Γ (rootCharHom a) j ≤ ι.range := by
      rw [hrange]
      exact (langSubnormal_of_mem_torus S hT j).1.trans inf_le_left
    have hCd : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a} ≤ ι.range := by
      rw [hrange]; exact inf_le_left
    have hfixmap : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β).map ι =
        S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a} := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hinj β
        (rootDiagUnit Tag.F4 a) hconj, hrange]
    have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a}).comap ι =
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
    refine Or.inr ⟨F, hF, hFin, ?_, ?_⟩
    · rw [hdf, ← hSq]; exact hcardF
    · let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
        (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
      obtain ⟨eR⟩ := hdata
      exact ⟨(QuotientGroup.congr (Subgroup.center ↥J)
        (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) eJ
        (Subgroup.map_center_eq eJ)).trans eR⟩

end CompF4BC

theorem compF4BC_cat_of_lang
    (d : TauCeti.ValidLieTypeIndex) (hch : d.1.characteristic = 2) (hd : ∃ q, d.1 = .F4 q) :
    CompF4BCAt d.1 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨e, hv⟩ := d
  obtain ⟨q, hq⟩ := hd
  subst hq
  obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  haveI := hKc
  have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_F4 q).symm.trans hch
  have hchar : ringChar K = q.p := ringChar.eq K q.p
  have hK2 : ringChar K = 2 := hchar.trans hqp
  exact compF4BCAt_of_mulEquiv eK.symm
    (compF4BCAt_adjointGroup (K := K) (d := .F4 q) hK2 (by rw [hK]; rfl))

end CFSG.StandardType

end
