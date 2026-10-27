module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6CompLabCat
public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
public import Certificates.Certificate707002
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLangComp
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoCoset
import CFSG.LocalAnalysis.StandardType.GGLangRatComp
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Untw
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw2
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6LangComp
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
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
import CFSG.RankThree.PartOne.KEXC.Basic
import CFSG.RankThree.PartOne.TCX.Ree.Perm
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def CompLabE6TwoAt (untw : Prop) (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S →
    β ^ 3 = 1 → β ≠ 1 →
    ∀ K : Subgroup S,
      CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) →
      (∀ K' : Subgroup S,
        CFSG.Open.IsComponentOf K' (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) → K' = K) →
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
        (untw → E6TwoCompLabelW lab ∧ (lab = ⟨.A, 2, 2⟩ → Subgroup.center ↥K ≠ ⊥)) ∧
        (¬ untw → E6TwoCompLabelT lab)

section CompLabE6Two

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.StandardType.LangRat

private theorem e6TwoCompLab_ggHasLabel_of_centerQuotEquiv {G H : Type} [Group G] [Group H]
    {X : Subgroup G} {Y : Subgroup H} {lab : LargeEvenLabel}
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* ↥Y ⧸ Subgroup.center ↥Y)
    (h : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X)) :
    GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y) := by
  unfold GGHasLabel at h ⊢
  refine largeEvenRawDatum_mono ?_ h
  rintro R' _ I F ⟨ψ⟩
  exact ⟨θ.symm.trans ψ⟩

private theorem e6TwoCompLab_centre {J R : Type} [Group J] [Group R] (e : J ≃* R)
    (h : Subgroup.center R ≠ ⊥) : Subgroup.center J ≠ ⊥ := by
  intro hJ
  exact h (by rw [← Subgroup.map_center_eq e, hJ, Subgroup.map_bot])

private theorem e6TwoCompLab_of_mulEquiv {untw : Prop} {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (h : CompLabE6TwoAt untw S) : CompLabE6TwoAt untw S' := by
  intro b hbmem hbp hb1 K' hK' hK'uniq
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ innAutDerived S := by
    rw [← mem_innAutDerived_congr e, hconj]
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
  have hfix : (fixSubgroup b).map (e.symm : S' →* S) = fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hfix' : (fixSubgroup α).map (e : S →* S') = fixSubgroup b := by
    rw [← hfix, Subgroup.map_map]
    simp
  have hKcomp : CFSG.Open.IsComponentOf K (fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  have hKuniq : ∀ K'' : Subgroup S, CFSG.Open.IsComponentOf K'' (fixSubgroup α) → K'' = K := by
    intro K'' hK''
    have hK''b : CFSG.Open.IsComponentOf (K''.map (e : S →* S')) (fixSubgroup b) := by
      rw [← hfix']
      exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK''
    have h1 := hK'uniq (K''.map (e : S →* S')) hK''b
    have h2 : (K''.map (e : S →* S')).map (e.symm : S' →* S) = K'' := by
      rw [Subgroup.map_map]; simp
    have h3 : (K''.map (e : S →* S')).map (e.symm : S' →* S) = K := by
      rw [h1, hK]
    exact h2.symm.trans h3
  obtain ⟨lab, hlab, hhas, hW, hTlab⟩ := h α hαmem hαp hα1 K hKcomp hKuniq
  have hKmap : K.map (e : S →* S') = K' := by
    rw [hK, Subgroup.map_map]
    simp
  let ε : ↥K ≃* ↥K' :=
    (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
  refine ⟨lab, hlab, ?_, ?_, hTlab⟩
  · refine e6TwoCompLab_ggHasLabel_of_centerQuotEquiv ?_ hhas
    exact QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K') ε
      (Subgroup.map_center_eq ε)
  · intro hun
    refine ⟨(hW hun).1, ?_⟩
    intro hlabA
    exact e6TwoCompLab_centre ε.symm ((hW hun).2 hlabA)

private theorem e6TwoCompLab_core
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    {G : Type} [Group G] [Finite G] (ι : G →* ModGL Tag.E6 L) (hinj : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut G)
    (hconj : ∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {J : Subgroup G} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (hJuniq : ∀ K' : Subgroup G, CFSG.Open.IsComponentOf K' (fixSubgroup β) → K' = J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧
      (E6CosetW S.ρ → E6TwoCompLabelW lab ∧
        (lab = ⟨.A, 2, 2⟩ → Subgroup.center ↥J ≠ ⊥)) ∧
      (¬ E6CosetW S.ρ → E6TwoCompLabelT lab) := by
  classical
  obtain ⟨i, hqs, hJR⟩ :=
    components_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap h1 hTame hJ
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    rw [map_fixSubgroup_eq_of_conj ι hinj β (rootDiagUnit Tag.E6 a) hconj, hrange]
  have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}).comap ι =
      fixSubgroup β := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hinj _
  have hCd : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} ≤ ι.range := by
    rw [hrange]
    exact inf_le_left
  have huniq : ∀ i' : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
        rationalComponent S.ρ S.Γ (rootCharHom a) i' =
          rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro i' hqs'
    obtain ⟨hle', hsub'⟩ := langSubnormal_of_mem_torus S hT i'
    have hcompR' : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i')
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) :=
      ⟨hle', (CFSG.Open.IsSubnormal.iff_subgroupOf hle').2 hsub', open_isQuasisimple hqs'⟩
    have hRrange : rationalComponent S.ρ S.Γ (rootCharHom a) i' ≤ ι.range := hle'.trans hCd
    have hK'i : CFSG.Open.IsComponentOf ((rationalComponent S.ρ S.Γ (rootCharHom a) i').comap ι)
        (fixSubgroup β) := by
      have h := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isComponentOf_comap_of_injective
        ι hinj hRrange hCd hcompR'
      rwa [hcomapfix] at h
    have h := congrArg (Subgroup.map ι) (hJuniq _ hK'i)
    rwa [Subgroup.map_comap_eq_self hRrange, hJR] at h
  obtain ⟨lab, hRL, hW, hTlab, hmem⟩ :=
    e6Two_lang_rationalComponents S hq hAlg hT hap h1 i hqs huniq
  have hb : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar a γ = 1 := by
    rintro γ ⟨k, δ, hδ, rfl⟩
    have hker := rho_mem_kernelRoots_of_mem_torus S hT
    have hδk : δ ∈ kernelRoots (rootCharHom a) := hδ.1
    have hiter : ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k]) δ ∈
        kernelRoots (rootCharHom a) := by
      induction k with
      | zero => simpa using hδk
      | succ k ih => rw [Function.iterate_succ_apply']; exact hker _ ih
    exact hiter.2
  have hcenter : ∀ (hda : rootDiagUnit Tag.E6 a ∈
        rationalComponent S.ρ S.Γ (rootCharHom a) i),
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≠ ⊥ := by
    intro hda hbot
    have hdacen : (⟨rootDiagUnit Tag.E6 a, hda⟩ :
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∈
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hle := CFSG.StandardType.LangRat.rationalComponent_le_centralizer S i (b := a) hb
      have hy := hle y.2
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      exact hy
    have hne : (⟨rootDiagUnit Tag.E6 a, hda⟩ :
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 1 := by
      intro h
      exact h1 (congrArg Subtype.val h)
    exact hne (Subgroup.mem_bot.mp (hbot ▸ hdacen))
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hhasJ : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
    refine e6TwoCompLab_ggHasLabel_of_centerQuotEquiv ?_ hRL.2
    exact (QuotientGroup.congr (Subgroup.center ↥J)
      (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) eJ
      (Subgroup.map_center_eq eJ)).symm
  refine ⟨lab, hRL.1, hhasJ, ?_, hTlab⟩
  intro hcoset
  refine ⟨hW hcoset, ?_⟩
  intro hlab
  exact e6TwoCompLab_centre eJ (hcenter (hmem hlab))

private theorem e6TwoCompLab_untw
    (q : TauCeti.PrimePower) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.card) (hK2 : ringChar K = 2) (hcard : q.card = 2) :
    CompLabE6TwoAt (∃ q' : TauCeti.PrimePower,
      (TauCeti.LieTypeIndex.E6 q : TauCeti.LieTypeIndex) = .E6 q') ↥(adjointGroup .E6 K) := by
  classical
  intro β hβmem hβp hβ1 J hJ hJuniq
  haveI : Fintype K := Fintype.ofFinite K
  have hpℓ : 3 ≠ ringChar K := by rw [hK2]; norm_num
  have hpK : ¬ 3 ∣ Nat.card K := by rw [hK, hcard]; norm_num
  have hp₀K : ¬ 5 ∣ Nat.card K := by rw [hK, hcard]; norm_num
  have hq₀ : 5 ≤ (5 : ℕ) ∨ 4 ≤ Nat.card K := Or.inl le_rfl
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) Nat.prime_three (by norm_num)
  have hperf : commutator ↥(adjointGroup .E6 K) = ⊤ :=
    single_edge_perfect Tag.E6 K (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨h, hh, hβh, hp1, hh1⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
      (Or.inl rfl) Nat.prime_three β hβmem hβp hβ1
  obtain ⟨S, a, ι, hSq, hΦ, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (Or.inr (Or.inr (Or.inl rfl))) Nat.prime_three hpK
      Nat.prime_five hp₀K hq₀ hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hℓ2 : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  haveI : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three (by rw [hℓL]; exact hpℓ.symm)
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hpL
    (fun hG2 => absurd hG2 (by decide)) hT hap h1
  have hq2 : S.D.q = 2 := hSq.trans (by rw [hK, hcard])
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 1 (by rw [pow_one, hSq])
  have hΦ' : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
      (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr) := by
    obtain ⟨Fr, hFr, hΦeq⟩ := hΦ
    exact ⟨Fr, fun c => by rw [hSq]; exact hFr c, hΦeq⟩
  have hcoset : E6CosetW S.ρ := e6_cosetW_of_untw S.D S.frob hΦ'
  obtain ⟨lab, hlab, hhas, hW, _⟩ :=
    e6TwoCompLab_core S hq2 hAlg hT hap h1 ι hinj hrange β hconj hTame hJ hJuniq
  refine ⟨lab, hlab, hhas, ?_, ?_⟩
  · intro _
    exact hW hcoset
  · intro hntw
    exact absurd ⟨q, rfl⟩ hntw

private theorem e6TwoCompLab_tw
    (q : TauCeti.PrimePower) {K : Type} [Field K] (σ : K ≃+* K)
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 2)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) (hcard : q.p ^ q.exponent = 2) :
    CompLabE6TwoAt (∃ q' : TauCeti.PrimePower,
      (TauCeti.LieTypeIndex.twistedE6 q : TauCeti.LieTypeIndex) = .E6 q') ↥(twistedE6RootGroup K σ) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  have hqp : q.p = 2 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hcard]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  have hpq : 3 ≠ q.p := by rw [hqp]; norm_num
  intro β hβmem hβp hβ1 J hJ hJuniq
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ hσ
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
    exact hΘ hβmem
  obtain ⟨h, rfl⟩ := hmem
  have hp1 : h ^ 3 = 1 := twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
    (by rw [map_pow, hβp, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
  have hq₀ : 5 ≤ (5 : ℕ) ∨ 4 ≤ q.p ^ q.exponent := Or.inl le_rfl
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) Nat.prime_three (by norm_num)
  obtain ⟨S, a, ι, hSq, hΦ, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime q.prime_p q.exponent_pos hK σ hσ
      Nat.prime_three hpq Nat.prime_five (by rw [hqp]; norm_num) hq₀ hmon
      (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
  have hℓL : ringChar (AlgebraicClosure K) = q.p := by
    rw [ringChar_algebraicClosure]
    exact ringChar_eq_of_card_eq_pow (n := q.exponent * 2) q.prime_p
      (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
  have hℓ2 : ringChar (AlgebraicClosure K) = 2 := hℓL.trans hqp
  haveI : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
  have hTame := langSetup_hTame_of_prime S Nat.prime_three
    (natCast_ne_zero_algebraicClosure_of_ne q.prime_p Nat.prime_three hK hpq)
    (fun h => absurd h (by decide)) hT hap h1
  have hq2 : S.D.q = 2 := hSq.trans hcard
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 2 (by rw [hK, hSq])
  have hΦ' : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
      (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr := by
    obtain ⟨Fr, hFr, hΦeq⟩ := hΦ
    exact ⟨Fr, fun c => by rw [hSq]; exact hFr c, hΦeq⟩
  have hNC : ¬ E6CosetW S.ρ := e6_not_cosetW_of_tw S.D S.frob hΦ'
  obtain ⟨lab, hlab, hhas, hW, hTlab⟩ :=
    e6TwoCompLab_core S hq2 hAlg hT hap h1 ι hinj hrange
      (twistedE6InndiagConj K σ h) hconj hTame hJ hJuniq
  have hntw : ¬ (∃ q' : TauCeti.PrimePower,
      (TauCeti.LieTypeIndex.twistedE6 q : TauCeti.LieTypeIndex) = .E6 q') := by
    rintro ⟨q', hq'⟩
    have hnot : ¬ (TauCeti.LieTypeIndex.twistedE6 q).IsTypeE6 := by
      simp [TauCeti.LieTypeIndex.isTypeE6_iff]
    have hyes : (TauCeti.LieTypeIndex.twistedE6 q).IsTypeE6 := by
      rw [hq']
      simp [TauCeti.LieTypeIndex.isTypeE6_iff]
    exact hnot hyes
  refine ⟨lab, hlab, hhas, ?_, ?_⟩
  · intro huntw
    exact absurd huntw hntw
  · intro _
    exact hTlab hNC

end CompLabE6Two

theorem compLabE6Two_cat
    (d : TauCeti.ValidLieTypeIndex) (hch : d.1.characteristic = 2)
    (hd : (∃ q, d.1 = .E6 q) ∨ ∃ q, d.1 = .twistedE6 q)
    (hq : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = 2) :
    CompLabE6TwoAt (∃ q, d.1 = .E6 q) (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨e, hv⟩ := d
  rcases hd with ⟨q, hqE⟩ | ⟨q, hqE⟩
  · subst hqE
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    haveI := hKc
    have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_E6 q).symm.trans hch
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hK2 : ringChar K = 2 := hchar.trans hqp
    have hcard : q.card = 2 := by
      simpa only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize, TauCeti.PrimePower.card_def]
        using hq
    exact e6TwoCompLab_of_mulEquiv eK.symm (e6TwoCompLab_untw q hK hK2 hcard)
  · subst hqE
    obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hcard : q.p ^ q.exponent = 2 := by
      simpa only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize, TauCeti.PrimePower.card_def]
        using hq
    exact e6TwoCompLab_of_mulEquiv eK.symm (e6TwoCompLab_tw q σ hK hσ hcard)

end CFSG.StandardType.TablePThreeKG

end
