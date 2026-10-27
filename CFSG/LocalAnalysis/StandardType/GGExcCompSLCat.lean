module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw2
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
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
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KEXC.Basic
import CFSG.RankThree.PartOne.TCX.Ree.Perm
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.LangRat

@[expose] def CompLabSLAt (p : ℕ) (d : TauCeti.LieTypeIndex) (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S →
    β ^ p = 1 → β ≠ 1 →
    ∀ K : Subgroup S,
      CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) →
      ∃ m : ℕ, 1 ≤ m ∧
        GGCompFieldAtSL (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d ^ m) K

theorem compLabSLAt_of_mulEquiv {p : ℕ} {d : TauCeti.LieTypeIndex} {S S' : Type} [Group S]
    [Group S'] (e : S ≃* S') (h : CompLabSLAt p d S) : CompLabSLAt p d S' := by
  intro b hbmem hbp hb1 K' hK'
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hαp : α ^ p = 1 := by
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
  have hKcomp : CFSG.Open.IsComponentOf K
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  obtain ⟨m, hm, hdata⟩ := h α hαmem hαp hα1 K hKcomp
  have hKmap : K.map (e : S →* S') = K' := by
    rw [hK, Subgroup.map_map]
    simp
  let ε : ↥K ≃* ↥K' :=
    (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
  exact ⟨m, hm, hdata.congr ε⟩

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.StandardType.RecipeExcLang CFSG.ComponentClassification.OuterAutomorphisms

private theorem slg_compLabSLAt_adjointGroup
    (hF : LangRatCompFieldLenSL) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK2 : ringChar K = 2) (hpK : ¬ p ∣ Nat.card K)
    (hinn : ∀ β : MulAut ↥(adjointGroup τ K),
      β ∈ innAutDerived ↥(adjointGroup τ K) →
      β ^ p = 1 → β ≠ 1 → ∃ h ∈ inndiagGroup τ K,
        (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ p = 1 ∧ h ≠ 1)
    {d : TauCeti.LieTypeIndex} (hdc : d.characteristic = ringChar K)
    (hdf : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d = Nat.card K) :
    CompLabSLAt p d ↥(adjointGroup τ K) := by
  classical
  intro β hβmem hβp hβ1 J hJ
  obtain ⟨h, hh, hβh, hp1, hh1⟩ := hinn β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := fun h' => hpK (by rw [hK, ← h']; exact dvd_pow_self p f.ne_zero)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hτ5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hτ6 : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hτs : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ6 hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    CFSG.LieType.Chevalley.single_edge_perfect τ K hτs
  obtain ⟨S, a, ι, hSq, _, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ5 hp hpK hp₀ hp₀K hq₀' hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hℓ2 : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  haveI : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := by
    intro hG2
    rcases hτ with h | h | h <;> rw [h] at hG2 <;> exact absurd hG2 (by decide)
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  have hdata := hF τ (AlgebraicClosure K) p₀ S hτ p hp hp2 a hT hap h1 i hqs
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  refine ⟨componentOrbitLength S.ρ (componentRoots (rootCharHom a) i), ?_, ?_⟩
  · have := (outer_componentOrbitLength_spec S hT i).1; omega
  · have hdataJ : GGCompFieldAtSL
        (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) J :=
      hdata.congr eJ.symm
    rw [hdf, ← hSq]
    exact hdataJ

theorem compLabSL_cat_of_lang
    (hF : LangRatCompFieldLenSL) (d : TauCeti.ValidLieTypeIndex) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hch : d.1.characteristic = 2)
    (hd : (∃ q, d.1 = .E6 q) ∨ (∃ q, d.1 = .E7 q) ∨ (∃ q, d.1 = .E8 q) ∨
      ∃ q, d.1 = .twistedE6 q) :
    CompLabSLAt p d.1 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨e, hv⟩ := d
  rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
  ·
    subst hq
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    haveI := hKc
    have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_E6 q).symm.trans hch
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hK2 : ringChar K = 2 := hchar.trans hqp
    have hpq : p ≠ q.p := fun h => hp2 (h.trans hqp)
    exact compLabSLAt_of_mulEquiv eK.symm
      (slg_compLabSLAt_adjointGroup hF (τ := .E6) (Or.inl rfl) hp hp2 hK2
        (by rw [hK]; exact not_dvd_card_of_ne hp hpq)
        (fun β hβ hβp hβ1 =>
          CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E (Or.inl rfl) hp β hβ hβp hβ1)
        (by simp [hchar]) (by rw [hK]; rfl))
  ·
    subst hq
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    haveI := hKc
    have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_E7 q).symm.trans hch
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hK2 : ringChar K = 2 := hchar.trans hqp
    have hpq : p ≠ q.p := fun h => hp2 (h.trans hqp)
    exact compLabSLAt_of_mulEquiv eK.symm
      (slg_compLabSLAt_adjointGroup hF (τ := .E7) (Or.inr (Or.inl rfl)) hp hp2 hK2
        (by rw [hK]; exact not_dvd_card_of_ne hp hpq)
        (fun β hβ hβp hβ1 =>
          CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E (Or.inr (Or.inl rfl)) hp β hβ hβp hβ1)
        (by simp [hchar]) (by rw [hK]; rfl))
  ·
    subst hq
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    haveI := hKc
    have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_E8 q).symm.trans hch
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hK2 : ringChar K = 2 := hchar.trans hqp
    have hpq : p ≠ q.p := fun h => hp2 (h.trans hqp)
    exact compLabSLAt_of_mulEquiv eK.symm
      (slg_compLabSLAt_adjointGroup hF (τ := .E8) (Or.inr (Or.inr rfl)) hp hp2 hK2
        (by rw [hK]; exact not_dvd_card_of_ne hp hpq)
        (fun β hβ hβp hβ1 =>
          CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E (Or.inr (Or.inr rfl)) hp β hβ hβp hβ1)
        (by simp [hchar]) (by rw [hK]; rfl))
  ·
    subst hq
    obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := exists_catEquiv_twistedE6 q hv
    haveI : Finite K := Nat.finite_of_card_ne_zero (by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
    haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
    have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_twistedE6 q).symm.trans hch
    have hpq : p ≠ q.p := fun h => hp2 (h.trans hqp)
    refine compLabSLAt_of_mulEquiv eK.symm ?_
    intro β hβ hβp hβ1 J hJ
    obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ
        hσ
    have hKf : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
    have hcyc : IsCyclic (RingAut K) :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic q.prime_p K hKf).2
    have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
      refine sup_le ?_ ?_
      · rw [hker]
        exact le_sup_left
      · rw [commutator_def, Subgroup.commutator_le]
        intro x _ y _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcyc.isMulCommutative.is_comm.comm _ _
    have hmem : β ∈ (twistedE6InndiagConj K σ).range := by
      rw [range_twistedE6InndiagConj, ← hker]
      exact hΘ hβ
    obtain ⟨h, rfl⟩ := hmem
    have hp1 : h ^ p = 1 := twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
      (by rw [map_pow, hβp, map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
    obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_setup_prime q.prime_p
        q.exponent_pos hp hp2 hpq
    have hmon : MonomialToralAt Tag.E6 p :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
        (by simp) hp hp2
    obtain ⟨S, a, ι, hSq, _, hT, hap, h1, hinj, hrange, hconj⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inndiag_twE6_of_prime
        q.prime_p q.exponent_pos hK σ hσ hp hpq hp₀ hp₀ℓ hq₀ hmon (twistedE6InndiagConj K σ h)
        (h : ModGL TwistTag.E6.tag K) h.2 (twistedE6InndiagConj_apply h)
        (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
    have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S
      hp
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.natCast_ne_zero_algebraicClosure_of_ne
        q.prime_p hp hK hpq) (fun h => absurd h (by decide)) hT hap h1
    obtain ⟨i, hqi, hJR⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
      S hp ι hinj hrange _ hconj hT hap h1 hTame hJ
    have hℓL : ringChar (AlgebraicClosure K) = q.p := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure]
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow
        (n := q.exponent * 2) q.prime_p (by have := q.exponent_pos; omega)
        (by rw [hK, ← pow_mul])
    have hℓ2 : ringChar (AlgebraicClosure K) = 2 := hℓL.trans hqp
    haveI : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
    have hdata := hF Tag.E6 (AlgebraicClosure K) p₀ S (Or.inl rfl) p hp hp2 a hT hap h1 i hqi
    let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
    refine ⟨componentOrbitLength S.ρ (componentRoots (rootCharHom a) i), ?_, ?_⟩
    · have := (outer_componentOrbitLength_spec S hT i).1; omega
    · have hdataJ : GGCompFieldAtSL
          (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) J :=
        hdata.congr eJ.symm
      have hfs : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize (.twistedE6 q) = S.D.q := by
        rw [hSq]
        simp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize,
          TauCeti.PrimePower.card_def]
      rw [hfs]
      exact hdataJ

end CFSG.StandardType
