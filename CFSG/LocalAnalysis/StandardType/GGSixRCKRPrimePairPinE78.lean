module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogE
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
import CFSG.ClassicalInvolution.WeakCT.SpAut
import CFSG.Timmesfeld.RankTwo.LevisExtras
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairPinAux
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairPinE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveJReflOfCore
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveQ2Char
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate10
public import Certificates.Certificate10050
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate1952
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8117
public import Certificates.Certificate9
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTwRigidLang
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3T
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
import CFSG.RankThree.PartOne.KGD.D4QA1

public section

namespace CFSG.StandardType.RCKRP

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.StandardType CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

section Transport

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}

private theorem rckTv_mul {F₀ : Type} [Field F₀] (i j : Fin 2) (c d : F₀) :
    (tv i j c * tv i j d : SL(2, F₀)) = tv i j (c + d) := by
  by_cases h : i = j
  · simp [tv, h]
  · rw [tv_of_ne h, tv_of_ne h, tv_of_ne h, Matrix.SpecialLinearGroup.transvection_add]

private theorem rckMem_closure_tv {X : Type} [Group X] {F₀ : Type} [Field F₀]
    (ρ : SL(2, F₀) →* X) (i j : Fin 2) (y : X) :
    y ∈ Subgroup.closure (Set.range fun c : F₀ => ρ (tv i j c)) ↔ ∃ c : F₀, ρ (tv i j c) = y := by
  have h0 : (tv i j (0 : F₀) : SL(2, F₀)) = 1 := by
    simpa using rckTv_mul i j (0 : F₀) 0
  constructor
  · intro hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, by rw [h0, map_one]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, by rw [← rckTv_mul, map_mul]⟩
    | inv x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      have hinv : (tv i j (-c) : SL(2, F₀)) = (tv i j c)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [rckTv_mul, neg_add_cancel, h0])
      exact ⟨-c, by rw [hinv, map_inv]⟩
  · rintro ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨c, rfl⟩

private theorem weakCT_of_frame_of_equiv_rootGroup {F₀ : Type} [Field F₀] (e : F₀ ≃+* F)
    {t : StatedLieTag} {n p f : ℕ} (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f)
    (hL : LeviConePresented D) (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin D.rank → SL(2, F₀) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F₀) →* X,
      ψ.comp (blk F₀ 0) = ρ i ∧ ψ.comp (blk F₀ 1) = ρ j) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧
      ∀ k (y : X), (y ∈ (D.rootGroup (Pi.single k 1)).map Ψ ↔ ∃ c : F₀, ρ k (tv 0 1 c) = y) ∧
        (y ∈ (D.rootGroup (-Pi.single k 1)).map Ψ ↔ ∃ c : F₀, ρ k (tv 1 0 c) = y) := by
  obtain ⟨Ψ, hsurj, hker, -, -, -, hpin⟩ :=
    weakCT_of_frame_of_equiv_pinned e hCT hL hD k₀ hgen hcomm hρ hψ
  refine ⟨Ψ, hsurj, hker, fun k y => ⟨?_, ?_⟩⟩
  · rw [show (Pi.single k 1 : Fin D.rank → ℤ) = sroot k from rfl, (hpin k).2.1]
    exact rckMem_closure_tv (ρ k) 0 1 y
  · rw [show (Pi.single k 1 : Fin D.rank → ℤ) = sroot k from rfl, (hpin k).2.2]
    exact rckMem_closure_tv (ρ k) 1 0 y

private theorem exists_cover_rootSpan_of_simple_roots
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : CurtisTits.IsCTGroupDatum (RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem
      (RootSystem.weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hdiv : D.divisible = ∅)
    {G : Type} [Group G] (Ψ : K →* G)
    (U_pos U_neg : Fin D.rank → Subgroup G)
    (hSimple : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ = U_pos k ∧
      (D.rootGroup (-Pi.single k 1)).map Ψ = U_neg k) :
    ∀ δ ∈ D.roots, ∃ k : Fin D.rank, ∃ u : K,
      (D.rootGroup δ).map Ψ = (U_pos k).map (MulAut.conj (Ψ u)).toMonoidHom ∧
      (D.rootGroup (-δ)).map Ψ = (U_neg k).map (MulAut.conj (Ψ u)).toMonoidHom := by
  intro δ hδ
  obtain ⟨w, k, hwk⟩ := s2jn_exists_weylAction_of_mem_roots D hdiv hδ
  obtain ⟨u, hu⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_map_conj_rootGroup hct w
  have hcomp : ∀ u : K, Ψ.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (Ψ u)).toMonoidHom.comp Ψ := fun u => by
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  refine ⟨k, u, ?_, ?_⟩
  · rw [hwk]
    rw [← hu (Pi.single k 1) (CFSG.Timmesfeld.LevisExtras.single_mem_roots k)]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, (hSimple k).1]
  · rw [hwk, ← map_neg]
    rw [← hu (-Pi.single k 1)
      (CFSG.Timmesfeld.LevisExtras.neg_mem_roots (CFSG.Timmesfeld.LevisExtras.single_mem_roots k))]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, (hSimple k).2]

end Transport

private theorem rckE78_tv01_eq_uSL {K : Type} [Field K] (c : K) :
    (tv (0 : Fin 2) 1 c : SL(2, K)) = uSL c := by
  rw [tv_of_ne (by decide : (0 : Fin 2) ≠ 1) c]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, uSL]

private theorem rckE78_tv10_eq_vSL {K : Type} [Field K] (c : K) :
    (tv (1 : Fin 2) 0 c : SL(2, K)) = vSL c := by
  rw [tv_of_ne (by decide : (1 : Fin 2) ≠ 0) c]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, vSL]

section Recog


private theorem rckSimple_images {τ : Tag} {K : Type} [Field K] [CharP K 2]
    {G : Subgroup (ModGL τ K)} {M : Type} [Group M] {R R' : Subgroup M} {Ψ : M →* ↥G}
    {ρ : SL(2, K) →* ↥G} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hρeq : ∀ A, ((ρ A : ↥G) : ModGL τ K) = rootSL2 τ K γ A)
    (hpin : ∀ y : ↥G, (y ∈ R.map Ψ ↔ ∃ c : K, ρ (tv 0 1 c) = y) ∧
      (y ∈ R'.map Ψ ↔ ∃ c : K, ρ (tv 1 0 c) = y)) :
    R.map (G.subtype.comp Ψ) = rootSubgroup τ K γ ∧
      R'.map (G.subtype.comp Ψ) = rootSubgroup τ K (-γ) := by
  have hu : ∀ c : K, G.subtype (ρ (tv 0 1 c)) = pinnedX τ K γ c := fun c => by
    rw [Subgroup.coe_subtype, hρeq, rckE78_tv01_eq_uSL,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_uSL_two]
  have hv : ∀ c : K, G.subtype (ρ (tv 1 0 c)) = pinnedX τ K (-γ) c := fun c => by
    rw [Subgroup.coe_subtype, hρeq, rckE78_tv10_eq_vSL,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_vSL_two hγ]
  constructor
  · ext y
    rw [← Subgroup.map_map, Subgroup.mem_map, CFSG.Blueprint.Chevalley.mem_rootSubgroup]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := ((hpin x).1).1 hx
      exact ⟨c, (hu c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨ρ (tv 0 1 c), ((hpin _).1).2 ⟨c, rfl⟩, hu c⟩
  · ext y
    rw [← Subgroup.map_map, Subgroup.mem_map, CFSG.Blueprint.Chevalley.mem_rootSubgroup]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := ((hpin x).2).1 hx
      exact ⟨c, (hv c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨ρ (tv 1 0 c), ((hpin _).2).2 ⟨c, rfl⟩, hv c⟩

theorem exists_cover_rootSpan_e7 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {g : ℕ} (hg : 0 < g) (hK : Nat.card K = 2 ^ g)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 7 → ι)
    (hgram : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 7, edgeE 7 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    ∃ Ψ : (ggU .E7 0 g).K →* ↥(rootSpan τ K (rootsOfFam β (Set.range l))),
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center (ggU .E7 0 g).K ∧
      ∀ δ ∈ (ggU .E7 0 g).D.roots, ∃ γ ∈ rootsOfFam β (Set.range l),
        ∃ m ∈ rootSpan τ K (rootsOfFam β (Set.range l)),
          ((ggU .E7 0 g).D.rootGroup δ).map
              ((rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ) =
            (rootSubgroup τ K γ).map (MulAut.conj m).toMonoidHom ∧
          ((ggU .E7 0 g).D.rootGroup (-δ)).map
              ((rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ) =
            (rootSubgroup τ K (-γ)).map (MulAut.conj m).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .E7 0 2 g := ⟨Nat.prime_two, hg, rfl⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ, hρeq⟩ :=
    rckPin_weakCT_data hτ β hroot l (edgeE 7) hgram hframe
  have hmemΨ := rckPin_mem_rootsOfFam β hroot l
  obtain ⟨e⟩ : Nonempty (K ≃+* GaloisField 2 g) := by
    have := Fintype.ofFinite K
    have := Fintype.ofFinite (GaloisField 2 g)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
        GaloisField.card 2 g (by omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e7Datum (GaloisField 2 g)).isFiniteType
    (Dv := (Steinberg.Minuscule.e7Datum (GaloisField 2 g)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis
    (Steinberg.Minuscule.e7_chevalleyExtras (GaloisField 2 g) O _
      (Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC (GaloisField 2 g)
        Steinberg.Minuscule.posDef_cartan_E7 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E7) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e7Data_valid.commC_natAbs (GaloisField 2 g) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e7Datum_steinbergExtras (GaloisField 2 g)).torus_iSupIndep
    (fun (k : Fin 7) => by
      have h := (Steinberg.Minuscule.e7Datum_isCTGroupDatum (GaloisField 2 g)).sq_mem k
      have e := Steinberg.Minuscule.e7Data_valid.weylElement_xm (GaloisField 2 g) k 1
      rw [e]
      exact h)
  obtain ⟨Ψ, hsurj, hker, hpin⟩ := weakCT_of_frame_of_equiv_rootGroup e
    (CurtisTits.curtisTitsConclusion_e7 2 g hadm) (leviConePresented_e7 _) hD
    (⟨0, by norm_num⟩ : Fin 7) hgen hcomm hρ hψ
  refine ⟨Ψ, hsurj, hker, fun δ hδ => ?_⟩
  obtain ⟨k, u, hδ1, hδ2⟩ := exists_cover_rootSpan_of_simple_roots
    (Steinberg.Minuscule.e7Datum_isCTGroupDatum (GaloisField 2 g))
    (s2jn_ggU_divisible_eq_empty (n := 0) (f := g) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    ((rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ)
    (fun k => rootSubgroup τ K (β (l k))) (fun k => rootSubgroup τ K (-β (l k)))
    (fun k => rckSimple_images (hroot (l k)) (hρeq k) (hpin k)) δ hδ
  exact ⟨β (l k), (hmemΨ k).1, _, (Ψ u).2, hδ1, hδ2⟩

theorem exists_cover_rootSpan_e8 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {g : ℕ} (hg : 0 < g) (hK : Nat.card K = 2 ^ g)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 8 → ι)
    (hgram : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 8, edgeE 8 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    ∃ Ψ : (ggU .E8 0 g).K →* ↥(rootSpan τ K (rootsOfFam β (Set.range l))),
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center (ggU .E8 0 g).K ∧
      ∀ δ ∈ (ggU .E8 0 g).D.roots, ∃ γ ∈ rootsOfFam β (Set.range l),
        ∃ m ∈ rootSpan τ K (rootsOfFam β (Set.range l)),
          ((ggU .E8 0 g).D.rootGroup δ).map
              ((rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ) =
            (rootSubgroup τ K γ).map (MulAut.conj m).toMonoidHom ∧
          ((ggU .E8 0 g).D.rootGroup (-δ)).map
              ((rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ) =
            (rootSubgroup τ K (-γ)).map (MulAut.conj m).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .E8 0 2 g := ⟨Nat.prime_two, hg, rfl⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ, hρeq⟩ :=
    rckPin_weakCT_data hτ β hroot l (edgeE 8) hgram hframe
  have hmemΨ := rckPin_mem_rootsOfFam β hroot l
  obtain ⟨e⟩ : Nonempty (K ≃+* GaloisField 2 g) := by
    have := Fintype.ofFinite K
    have := Fintype.ofFinite (GaloisField 2 g)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
        GaloisField.card 2 g (by omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Adjoint.e8Datum (GaloisField 2 g)).isFiniteType
    (Dv := (Steinberg.Adjoint.e8Datum (GaloisField 2 g)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E8) (Or.inr (Or.inr rfl))
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis
    (Steinberg.Adjoint.e8_chevalleyExtras (GaloisField 2 g) O _
      (Steinberg.Adjoint.commutatorFormula_commC Steinberg.Adjoint.e8Data_valid
        Steinberg.Adjoint.noG2_E8 _ (Steinberg.Adjoint.adjDatum_roots _ (GaloisField 2 g)) O))
    rfl (fun α hα β hβ hr hd => by
      rw [Steinberg.Adjoint.mem_adjDatum_roots] at hα hβ hr hd
      have hne : α + β ≠ 0 := hr.ne_zero
      rw [Steinberg.Adjoint.commC_11 hα hβ hne, Steinberg.Adjoint.RootOperatorFamily'.coeff11,
        Steinberg.Adjoint.RootOperatorFamily'.bracketCoeff_natAbs _ _ (fun h => hne (by
          change β = -α at h
          rw [h, add_neg_cancel])) hr]
      exact Steinberg.Adjoint.stringNorm_of_not_isRoot hd) h1 h2 h3 h4
    (Steinberg.Adjoint.e8_steinbergExtras (GaloisField 2 g)).torus_iSupIndep
    (fun (k : Fin 8) => by
      have h := (Steinberg.Adjoint.e8_isCTGroupDatum (GaloisField 2 g)).sq_mem k
      rw [Steinberg.Adjoint.weylElement_eq_xPar (Chevalley.rootOperatorFamily .E8) k] at h
      exact h)
  obtain ⟨Ψ, hsurj, hker, hpin⟩ := weakCT_of_frame_of_equiv_rootGroup e
    (CurtisTits.curtisTitsConclusion_e8 2 g hadm) (leviConePresented_e8 _) hD
    (⟨0, by norm_num⟩ : Fin 8) hgen hcomm hρ hψ
  refine ⟨Ψ, hsurj, hker, fun δ hδ => ?_⟩
  obtain ⟨k, u, hδ1, hδ2⟩ := exists_cover_rootSpan_of_simple_roots
    (Steinberg.Adjoint.e8_isCTGroupDatum (GaloisField 2 g))
    (s2jn_ggU_divisible_eq_empty (n := 0) (f := g) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    ((rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ)
    (fun k => rootSubgroup τ K (β (l k))) (fun k => rootSubgroup τ K (-β (l k)))
    (fun k => rckSimple_images (hroot (l k)) (hρeq k) (hpin k)) δ hδ
  exact ⟨β (l k), (hmemΨ k).1, _, (Ψ u).2, hδ1, hδ2⟩

end Recog

end CFSG.StandardType.RCKRP
