module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6UniqueCompLabel
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Untw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw2
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
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
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KEXC.Basic
import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms

section UniqueCompLabel

private theorem uniqueCompLabel_of_langSetup
    {P : LargeEvenLabel → Prop}
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 3)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    {G : Type} [Group G] [Finite G] (ι : G →* ModGL Tag.E6 L) (hinj : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut G)
    (hconj : ∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {J : Subgroup G} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (hJuniq : ∀ K' : Subgroup G, CFSG.Open.IsComponentOf K' (fixSubgroup β) → K' = J)
    (hR : ∀ {a : Fin Tag.E6.rank → Lˣ}, rootDiagUnit Tag.E6 a ∈ S.D.torus →
      (∀ j, a j ^ 3 = 1) → rootDiagUnit Tag.E6 a ≠ 1 →
      ∀ i : KernelComponent (rootCharHom a),
      (∀ i' : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
          rationalComponent S.ρ S.Γ (rootCharHom a) i' =
            rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
        GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∧ P lab) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧ P lab := by
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
  obtain ⟨lab, hlab, hHasRi, hPlab⟩ := hR hT hap h1 i huniq
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  refine ⟨lab, hlab, ?_, hPlab⟩
  exact ggHasLabel_of_mulEquiv
    ((QuotientGroup.congr (Subgroup.center ↥J)
      (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) eJ
      (Subgroup.map_center_eq eJ)).symm) hHasRi

private theorem uniqueCompLabelAt_e6_adjointGroup
    {P : LargeEvenLabel → Prop}
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) (hqK : 4 ≤ Nat.card K)
    (hinn : ∀ β : MulAut ↥(adjointGroup .E6 K),
      β ∈ innAutDerived ↥(adjointGroup .E6 K) →
      β ^ 3 = 1 → β ≠ 1 → ∃ h ∈ inndiagGroup .E6 K,
        (∀ c : adjointGroup .E6 K, (β c : ModGL .E6 K) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧ h ≠ 1)
    {d : TauCeti.LieTypeIndex}
    (hdf : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d = Nat.card K)
    (hR : ∀ (S : LangSetup Tag.E6 (AlgebraicClosure K) 3)
        (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
      (∀ c, Fr c = c ^ S.D.q) →
      S.D.Φ = Units.map (entrywiseHom Fr) →
      S.D.q = CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d →
      ∀ {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ},
        rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
        rootDiagUnit Tag.E6 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        (∀ i' : KernelComponent (rootCharHom a),
          CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
            rationalComponent S.ρ S.Γ (rootCharHom a) i' =
              rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
          GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∧ P lab) :
    UniqueCompLabelAt P ↥(adjointGroup .E6 K) := by
  classical
  intro β hβmem hβp hβ1 J hJ hJuniq
  obtain ⟨h, hh, hβh, hp1, hh1⟩ := hinn β hβmem hβp hβ1
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : 3 ≠ ringChar K := by rw [hK2]; norm_num
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK, hK2]
    intro hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  have hq₀' : 5 ≤ 3 ∨ 4 ≤ Nat.card K := Or.inr hqK
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) Nat.prime_three (by norm_num)
  have hperf : commutator ↥(adjointGroup .E6 K) = ⊤ :=
    single_edge_perfect Tag.E6 K (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (p₀ := 3) (Or.inr (Or.inr (Or.inl rfl)))
      Nat.prime_three hpK Nat.prime_three hpK hq₀' hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hℓ2 : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  have : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three (by rw [hℓL]; exact hpℓ.symm)
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hpL
    (fun hG2 => absurd hG2 (by decide)) hT hap h1
  exact uniqueCompLabel_of_langSetup (L := AlgebraicClosure K) (a := a)
    (G := ↥(adjointGroup .E6 K)) (J := J)
    S hT hap h1 ι hinj hrange β hconj hTame hJ hJuniq
    (fun {a} hT hap h1 i huniq =>
      hR S Fr (fun c => by rw [hSq]; exact hFr c) hΦ (hdf.trans hSq.symm).symm hT hap h1 i huniq)

end UniqueCompLabel

theorem uniqueCompLabelAt_e6_cat_of_lang
    {P : LargeEvenLabel → Prop}
    (d : TauCeti.ValidLieTypeIndex) (hch : d.1.characteristic = 2)
    (hd : (∃ q, d.1 = .E6 q) ∨ ∃ q, d.1 = .twistedE6 q)
    (hq : 4 ≤ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1)
    (hrat : ∀ {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (S : LangSetup Tag.E6 L 3)
      (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) →
      ((∃ q, d.1 = .E6 q) ∧ S.D.Φ = Units.map (entrywiseHom Fr) ∨
        (∃ q, d.1 = .twistedE6 q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr) →
      S.D.q = CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 →
      ∀ {a : Fin Tag.E6.rank → Lˣ}, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
        rootDiagUnit Tag.E6 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        (∀ i' : KernelComponent (rootCharHom a),
          CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
            rationalComponent S.ρ S.Γ (rootCharHom a) i' =
              rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
          GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∧ P lab) :
    UniqueCompLabelAt P (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨e, hv⟩ := d
  rcases hd with ⟨q, hqE⟩ | ⟨q, hqE⟩
  ·
    subst hqE
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    have := hKc
    have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_E6 q).symm.trans hch
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hK2 : ringChar K = 2 := hchar.trans hqp
    have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
    have hℓ2 : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
    have : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
    exact uniqueCompLabelAt_of_mulEquiv eK.symm
      (uniqueCompLabelAt_e6_adjointGroup hK2 (by rw [hK]; simpa only [
          CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize, TauCeti.PrimePower.card_def] using hq)
        (fun β hβ hβp hβ1 =>
          CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
            (Or.inl rfl) Nat.prime_three β hβ hβp hβ1)
        (by rw [hK]; rfl)
        (fun S Fr hFr hΦ hq' {a} hT hap h1 i huniq =>
          hrat S Fr hFr (Or.inl ⟨⟨q, rfl⟩, hΦ⟩) hq' hT hap h1 i huniq))
  ·
    subst hqE
    obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := exists_catEquiv_twistedE6 q hv
    have : Finite K := Nat.finite_of_card_ne_zero (by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    have : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
    have hqp : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_twistedE6 q).symm.trans hch
    have hpq : 3 ≠ q.p := by rw [hqp]; norm_num
    refine uniqueCompLabelAt_of_mulEquiv eK.symm ?_
    intro β hβ hβp hβ1 J hJ hJuniq
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
    have hp1 : h ^ 3 = 1 := twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
      (by rw [map_pow, hβp, map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
    have hq₀ : 5 ≤ 3 ∨ 4 ≤ q.p ^ q.exponent := Or.inr (by
      simpa only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize, TauCeti.PrimePower.card_def]
        using hq)
    have hmon : MonomialToralAt Tag.E6 3 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) Nat.prime_three (by norm_num)
    obtain ⟨S, a, ι, hSq, ⟨Fr, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inndiag_twE6_of_prime q.prime_p q.exponent_pos hK σ hσ
        Nat.prime_three hpq (p₀ := 3) Nat.prime_three hpq hq₀ hmon
        (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
        (twistedE6InndiagConj_apply h)
        (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
    have hTame := langSetup_hTame_of_prime S Nat.prime_three
      (natCast_ne_zero_algebraicClosure_of_ne q.prime_p Nat.prime_three hK hpq)
      (fun h => absurd h (by decide)) hT hap h1
    have hℓL : ringChar (AlgebraicClosure K) = q.p := by
      rw [ringChar_algebraicClosure]
      exact ringChar_eq_of_card_eq_pow (n := q.exponent * 2) q.prime_p
        (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
    have hℓ2 : ringChar (AlgebraicClosure K) = 2 := hℓL.trans hqp
    have : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
    have hfs : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize (.twistedE6 q) = S.D.q := by
      rw [hSq]
      simp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize, TauCeti.PrimePower.card_def]
    exact uniqueCompLabel_of_langSetup (L := AlgebraicClosure K) (a := a)
      (G := ↥(twistedE6RootGroup K σ)) (J := J)
      S hT hap h1 ι hinj hrange (twistedE6InndiagConj K σ h) hconj hTame hJ hJuniq
      (fun {a} hT hap h1 i huniq =>
        hrat S Fr (fun c => by rw [hSq]; exact hFr c) (Or.inr ⟨⟨q, rfl⟩, hΦ⟩) hfs.symm hT hap h1
          i huniq)

end CFSG.StandardType.TablePThreeKG

end
