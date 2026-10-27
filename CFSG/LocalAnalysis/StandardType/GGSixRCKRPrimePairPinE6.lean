module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogE
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairPinAux
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

public section

namespace CFSG.StandardType.RCKRP

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open scoped MatrixGroups

theorem rckPin_tv01_eq_uSL {K : Type} [Field K] (c : K) :
    (tv (0 : Fin 2) 1 c : SL2 K) = uSL c := by
  rw [tv_of_ne (by decide : (0 : Fin 2) ≠ 1) c]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, uSL]

theorem rckPin_tv10_eq_vSL {K : Type} [Field K] (c : K) :
    (tv (1 : Fin 2) 0 c : SL2 K) = vSL c := by
  rw [tv_of_ne (by decide : (1 : Fin 2) ≠ 0) c]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, vSL]

theorem rckPin_mem_rootsOfFam {τ : Tag} {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) {n : ℕ} (l : Fin n → ι) (k : Fin n) :
    β (l k) ∈ rootsOfFam β (Set.range l) ∧ -β (l k) ∈ rootsOfFam β (Set.range l) := by
  classical
  have hsum : ∑ b, ((fun b => if b = l k then 1 else 0 : ι → ℕ) b : ℤ) • β b = β (l k) := by
    simp [ite_smul, Finset.sum_ite_eq']
  refine ⟨⟨hroot _, fun b => if b = l k then 1 else 0, fun b hb => ?_, Or.inl hsum.symm⟩,
    ⟨IsRoot.neg (hroot _), fun b => if b = l k then 1 else 0, fun b hb => ?_, Or.inr ?_⟩⟩
  · by_cases h : b = l k
    · exact ⟨k, h.symm⟩
    · exact absurd (by simp [h]) hb
  · by_cases h : b = l k
    · exact ⟨k, h.symm⟩
    · exact absurd (by simp [h]) hb
  · rw [hsum]

theorem rckPin_weakCT_data
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) {n : ℕ} (l : Fin n → ι) (adj : Fin n → Fin n → Prop)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ adj i j → ¬ adj j i → iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, adj i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    ∃ (U : Fin n → Subgroup ↥(rootSpan τ K (rootsOfFam β (Set.range l))))
      (ρ : Fin n → SL(2, K) →* ↥(rootSpan τ K (rootsOfFam β (Set.range l)))),
      ⨆ k, U k = ⊤ ∧
      (∀ i j : Fin n, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      (∀ i j : Fin n, adj i j → ∃ ψ : SL(3, K) →* ↥(rootSpan τ K (rootsOfFam β (Set.range l))),
        ψ.comp (blk K 0) = ρ i ∧ ψ.comp (blk K 1) = ρ j) ∧
      (∀ k (A : SL(2, K)), (rootSpan τ K (rootsOfFam β (Set.range l))).subtype (ρ k A) =
        rootSL2 τ K (β (l k)) A) := by
  classical
  set G : Subgroup (ModGL τ K) := rootSpan τ K (rootsOfFam β (Set.range l)) with hGdef
  have hmemΨ := rckPin_mem_rootsOfFam β hroot l
  have hGgen : G = ⨆ k, (rootSL2 τ K (β (l k))).range := by
    apply le_antisymm
    · calc G ≤ ⨆ b ∈ Set.range l, (rootSL2 τ K (β b)).range :=
          rootSpan_rootsOfFam_le hτ β hroot _
        _ = ⨆ k, (rootSL2 τ K (β (l k))).range := iSup_range
    · refine iSup_le fun k => ?_
      rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (hroot _)]
      exact sup_le (le_iSup₂ (f := fun γ (_ : γ ∈ rootsOfFam β (Set.range l)) =>
        rootSubgroup τ K γ) _ (hmemΨ k).1) (le_iSup₂ (f := fun γ
          (_ : γ ∈ rootsOfFam β (Set.range l)) => rootSubgroup τ K γ) _ (hmemΨ k).2)
  have hrangeG : ∀ k, (rootSL2 τ K (β (l k))).range ≤ G := fun k => by
    rw [hGgen]
    exact le_iSup (fun k => (rootSL2 τ K (β (l k))).range) k
  have hmem : ∀ k (A : SL(2, K)), rootSL2 τ K (β (l k)) A ∈ G := fun k A =>
    hrangeG k ⟨A, rfl⟩
  refine ⟨fun k => ((rootSL2 τ K (β (l k))).range).subgroupOf G,
    fun k => (rootSL2 τ K (β (l k))).codRestrict G (hmem k), ?_, ?_, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.map_subgroupOf_eq_of_le (hrangeG _)]
    exact hGgen.symm
  · intro i j hij h1 h2 a ha b hb
    obtain ⟨A, hA⟩ := ha
    obtain ⟨B, hB⟩ := hb
    have := CFSG.HardMathSupport.Timmesfeld.CrossChar.commute_rootSL2_of_iform_eq_zero hτ
      (hroot (l i)) (hroot (l j)) (hgram i j hij h1 h2) A B
    have hA' : (a : ModGL τ K) = rootSL2 τ K (β (l i)) A := hA.symm
    have hB' : (b : ModGL τ K) = rootSL2 τ K (β (l j)) B := hB.symm
    refine Subtype.ext ?_
    show (a : ModGL τ K) * (b : ModGL τ K) = (b : ModGL τ K) * (a : ModGL τ K)
    rw [hA', hB']
    exact this.eq
  · intro k
    refine ⟨fun a b h => ?_, range_codRestrict_eq' _ G (hmem k)⟩
    exact CFSG.RankThree.Chevalley.rootSL2_injective_of_field (β (l k)) (congrArg Subtype.val h)
  · intro i j hij
    obtain ⟨θ, h0, h1⟩ := hframe i j hij
    have hθG : ∀ x, θ x ∈ G := by
      intro x
      have hx : x ∈ B12 K ⊔ B23 K := by rw [B12_sup_B23]; exact Subgroup.mem_top x
      have h2 : θ x ∈ (B12 K ⊔ B23 K).map θ := Subgroup.mem_map_of_mem θ hx
      rw [Subgroup.map_sup] at h2
      have e0 : (B12 K).map θ = (rootSL2 τ K (β (l i))).range := by
        rw [B12, ← MonoidHom.range_comp, h0]
      have e1 : (B23 K).map θ = (rootSL2 τ K (β (l j))).range := by
        rw [B23, ← MonoidHom.range_comp, h1]
      rw [e0, e1] at h2
      exact sup_le (hrangeG i) (hrangeG j) h2
    refine ⟨θ.codRestrict G hθG, ?_, ?_⟩
    · refine MonoidHom.ext fun A => Subtype.ext ?_
      exact congrArg (fun φ : SL(2, K) →* ModGL τ K => φ A) h0
    · refine MonoidHom.ext fun A => Subtype.ext ?_
      exact congrArg (fun φ : SL(2, K) →* ModGL τ K => φ A) h1
  · intro k A
    rfl

theorem rckPin_map_rootGroup_pinned
    {τ : Tag} {K : Type} [Field K] {ι : Type} [Fintype ι] {β : ι → Fin τ.rank → ℤ}
    (hroot : ∀ b, IsRoot τ (β b)) {n : ℕ} (l : Fin n → ι) (k : Fin n) {G : Type} [Group G]
    {Ψ' : G →* ↥(rootSpan τ K (rootsOfFam β (Set.range l)))}
    {ρ : SL(2, K) →* ↥(rootSpan τ K (rootsOfFam β (Set.range l)))}
    (hρeq : ∀ A, (rootSpan τ K (rootsOfFam β (Set.range l))).subtype (ρ A) =
      rootSL2 τ K (β (l k)) A)
    {Y Y' : Subgroup G}
    (hY : Y.map Ψ' = Subgroup.closure (Set.range fun c : K => ρ (tv 0 1 c)))
    (hY' : Y'.map Ψ' = Subgroup.closure (Set.range fun c : K => ρ (tv 1 0 c))) :
    Y.map ((rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ') =
        rootSubgroup τ K (β (l k)) ∧
      Y'.map ((rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ') =
        rootSubgroup τ K (-β (l k)) := by
  have hmap : ∀ Z : Subgroup G,
      Z.map ((rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ') =
        (Z.map Ψ').map (rootSpan τ K (rootsOfFam β (Set.range l))).subtype := by
    intro Z
    rw [Subgroup.map_map]
  constructor
  · rw [hmap, hY]
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro x ⟨c, rfl⟩
      change (rootSpan τ K (rootsOfFam β (Set.range l))).subtype (ρ (tv 0 1 c)) ∈
        rootSubgroup τ K (β (l k))
      rw [rckPin_tv01_eq_uSL, hρeq, rootSL2_uSL_eq]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro y ⟨d, rfl⟩
      have hεε : (pinnedData τ (β (l k))).2.2 •
          ((pinnedData τ (β (l k))).2.2 • d) = d := by
        rcases pinnedSign_eq τ (β (l k)) with h | h <;> rw [h] <;> simp
      have he : pinnedX τ K (β (l k)) d =
          (rootSpan τ K (rootsOfFam β (Set.range l))).subtype
            (ρ (tv 0 1 ((pinnedData τ (β (l k))).2.2 • d))) := by
        rw [hρeq]
        show pinnedX τ K (β (l k)) d =
          rootSL2 τ K (β (l k)) (tv 0 1 ((pinnedData τ (β (l k))).2.2 • d))
        rw [rckPin_tv01_eq_uSL, rootSL2_uSL_eq, hεε]
      rw [he]
      exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Set.mem_range_self _))
  · obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) (β := β (l k)) (hroot (l k))
    rw [hmap, hY']
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro x ⟨c, rfl⟩
      change (rootSpan τ K (rootsOfFam β (Set.range l))).subtype (ρ (tv 1 0 c)) ∈
        rootSubgroup τ K (-β (l k))
      rw [rckPin_tv10_eq_vSL, hρeq, hv]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro y ⟨d, rfl⟩
      have hεε : ε * (ε * d) = d := by
        rw [← mul_assoc, hε, one_mul]
      have he : pinnedX τ K (-β (l k)) d =
          (rootSpan τ K (rootsOfFam β (Set.range l))).subtype (ρ (tv 1 0 (ε * d))) := by
        rw [hρeq]
        show pinnedX τ K (-β (l k)) d = rootSL2 τ K (β (l k)) (tv 1 0 (ε * d))
        rw [rckPin_tv10_eq_vSL, hv, hεε]
      rw [he]
      exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Set.mem_range_self _))

theorem innerRecogPinned_E6
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 6 → ι)
    (hgram : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 6, edgeE 6 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    ∃ Ψ : e6Data_valid.minGroup (GaloisField p f) →* ModGL τ K,
      Ψ.range = rootSpan τ K (rootsOfFam β (Set.range l)) ∧
      Ψ.ker ≤ Subgroup.center (e6Data_valid.minGroup (GaloisField p f)) ∧
      ∀ k : Fin 6,
        ((e6Datum (GaloisField p f)).rootGroup (Pi.single k 1)).map Ψ =
            rootSubgroup τ K (β (l k)) ∧
        ((e6Datum (GaloisField p f)).rootGroup (-Pi.single k 1)).map Ψ =
            rootSubgroup τ K (-β (l k)) := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ, hρeq⟩ :=
    rckPin_weakCT_data hτ β hroot l (edgeE 6) hgram hframe
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨Fact.out, hf, rfl⟩
  obtain ⟨Ψ', hsurj, hker, hqs, hcent, hmodel, hpin⟩ :=
    weakCT_e6_of_frame_pinned p f hadm hK U hgen hcomm hρ hψ
  refine ⟨(rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ', ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [MonoidHom.comp_apply] at hx
    have hx' : Ψ' x = 1 := (rootSpan τ K (rootsOfFam β (Set.range l))).subtype_injective (by
      rw [hx, map_one])
    exact hker (by rwa [MonoidHom.mem_ker])
  · intro k
    exact rckPin_map_rootGroup_pinned hroot l k (ρ := ρ k) (fun A => hρeq k A)
      (hpin k).1 (hpin k).2

end CFSG.StandardType.RCKRP

end
