module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacEAll
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyGen
public import CFSG.Sporadic.Schreier.J4SProfileNode
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
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
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
public import Certificates.Certificate1953
public import Certificates.Certificate1954
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
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.RCKRP

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE
open scoped MatrixGroups


theorem rckLab_tree_len
    {τ : Tag} (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)}
    {tp : ℕ → ℕ → List ℕ} (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 6 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = eRootCount c.length →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 6 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeE P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i))) :
    ∃ (v : WeylGroup τ) (n : ℕ) (l : Fin n → Option (Fin τ.rank)), Function.Injective l ∧
      n = compRank (componentRoots (rootCharHom a) i) ∧
      componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l) ∧
      (∀ c d : Fin n, c ≠ d → ¬ edgeE n c d → ¬ edgeE n d c →
        iform (K.extRoot (l c)) (K.extRoot (l d)) = 0) ∧
      ∀ c d : Fin n, edgeE n c d → (nodeIdx (l c), nodeIdx (l d)) ∈ E := by
  classical
  obtain ⟨v, μ, -, hall⟩ := S.exists_kacT_of_prime hp hpL hK hTp
  obtain ⟨x, hx, hi⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := K.exists_comp_eq_of_check hT hadj (adm := fun _ => true) hcheck rfl hx
  set C : Finset (Option (Fin τ.rank)) := (c.map (idxNode (r := τ.rank))).toFinset with hCdef
  have hCset : K.comp p μ x = (C : Set (Option (Fin τ.rank))) := by
    rw [hcomp]
    ext y
    simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (hlt c hc w hw)]
      exact hw
  have hCp : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp K hp.pos μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hi' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' K.rootsOf (C : Set (Option (Fin τ.rank))) := by
    rw [hi, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hi', compRank_image, compRank_rootsOf K hK hCp, hcard c hc]
  have hncard : (componentRoots (rootCharHom a) i).ncard =
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset := by
    rw [hi', ncard_image_smul, ncard_rootsOf K hK hCp]
  rw [hrank] at h6 hn
  rw [hncard] at hn
  obtain ⟨P, hP, hsame⟩ := hcount c hc h6 hn
  obtain ⟨hnd, hlen, hnon, hE⟩ := htrees P hP
  have hCP : (C : Set (Option (Fin τ.rank))) = Set.range P.get := by
    rw [Set.range_list_get, ← hCset, hcomp]
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [mem_iff_of_sameSet hsame, List.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      rwa [← nodeIdx_injective hzy]
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hinj : Function.Injective P.get := List.nodup_iff_injective_get.1 hnd
  have hlenP : P.length = c.length := by
    have h1 : (C : Set (Option (Fin τ.rank))).ncard = c.length := by
      rw [Set.ncard_coe_finset, hCdef, hcard c hc]
    rw [hCP, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h1
    exact h1
  exact ⟨v, P.length, P.get, hinj, by rw [hlenP, hrank], by rw [hi', hCP], hnon, hE⟩

theorem rckLab_rootsOfFam_range {τ : Tag} {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) {n : ℕ}
    (l : Fin n → ι) (hl : Function.Injective l) :
    rootsOfFam β (Set.range l) = rootsOfFam (fun k => β (l k)) Set.univ := by
  classical
  have hsum : ∀ n' : ι → ℕ, (∀ b, n' b ≠ 0 → b ∈ Set.range l) →
      ∑ b, (n' b : ℤ) • β b = ∑ k, (n' (l k) : ℤ) • β (l k) := by
    intro n' hsupp
    rw [← Finset.sum_image (f := fun b => (n' b : ℤ) • β b) (g := l) (s := Finset.univ)
      (fun x _ y _ h => hl h)]
    refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_).symm
    have : n' b = 0 := by
      by_contra hne
      obtain ⟨k, hk⟩ := hsupp b hne
      exact hb (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩)
    simp [this]
  ext γ
  constructor
  · rintro ⟨hγ, n', hsupp, h⟩
    refine ⟨hγ, fun k => n' (l k), fun _ _ => Set.mem_univ _, ?_⟩
    rcases h with h | h
    · exact Or.inl (h.trans (hsum n' hsupp))
    · exact Or.inr (by rw [h, hsum n' hsupp])
  · rintro ⟨hγ, m, -, h⟩
    have hsupp : ∀ b, Function.extend l m (fun _ => 0) b ≠ 0 → b ∈ Set.range l := by
      intro b hb
      by_contra hnot
      rw [Function.extend_apply' _ _ _ (by rintro ⟨k, hk⟩; exact hnot ⟨k, hk⟩)] at hb
      exact hb rfl
    have key := hsum (Function.extend l m (fun _ => 0)) hsupp
    simp only [hl.extend_apply] at key
    refine ⟨hγ, Function.extend l m (fun _ => 0), hsupp, ?_⟩
    rcases h with h | h
    · exact Or.inl (h.trans key.symm)
    · exact Or.inr (by rw [h, key])

theorem rckLab_iform_add_left {τ : Tag} (x x' y : Fin τ.rank → ℤ) :
    iform (x + x') y = iform x y + iform x' y := by
  simp only [iform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem rckLab_iform_add_right
    {τ : Tag} (x y y' : Fin τ.rank → ℤ) :
    iform x (y + y') = iform x y + iform x y' := by
  rw [iform_comm x (y + y'), rckLab_iform_add_left, iform_comm y x, iform_comm y' x]

theorem rckLab_iform_edge
    {τ : Tag} (hτ : SimplyLacedTag τ) {L : Type} [Field L] {ρ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hF : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ) : iform (σ 0 1) (σ 1 2) = -1 := by
  have h2 : ∀ i j : Fin 3, i ≠ j → iform (σ i j) (σ i j) = 2 := fun i j hij =>
    iform_self_eq_two hτ (hF.isRoot i j hij)
  have h02 := h2 0 2 (by decide)
  have e1 : iform (σ 0 1 + σ 1 2) (σ 0 1 + σ 1 2) = iform (σ 0 1) (σ 0 1) +
      iform (σ 0 1) (σ 1 2) + (iform (σ 1 2) (σ 0 1) + iform (σ 1 2) (σ 1 2)) := by
    rw [rckLab_iform_add_left, rckLab_iform_add_right, rckLab_iform_add_right, add_assoc]
  rw [hF.add 0 1 2, h02, iform_comm (σ 1 2) (σ 0 1), h2 0 1 (by decide),
    h2 1 2 (by decide)] at e1
  omega

theorem rckLab_of_data
    {τ : Tag} (hτ : SimplyLacedTag τ) (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)}
    {tp : ℕ → ℕ → List ℕ} (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 6 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = eRootCount c.length →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 6 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeE P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h6 : compRank (componentRoots (rootCharHom a) i) = 6)
    (hn : (componentRoots (rootCharHom a) i).ncard = 72) :
    ∃ β : Fin 6 → Fin τ.rank → ℤ, (∀ b, IsRoot τ (β b)) ∧
      componentRoots (rootCharHom a) i = rootsOfFam β Set.univ ∧
      (∀ c d : Fin 6, c ≠ d → ¬ edgeE 6 c d → ¬ edgeE 6 d c → iform (β c) (β d) = 0) ∧
      (∀ c d : Fin 6, edgeE 6 c d → iform (β c) (β d) = -1) ∧
      ∀ {F : Type} [Field F] (c d : Fin 6), edgeE 6 c d →
        ∃ θ : SL(3, F) →* ModGL τ F,
          θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β c) ∧
            θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β d) := by
  classical
  have hn' : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
    rw [h6, hn]; simp [eRootCount]
  obtain ⟨v, n, l, hlinj, hnc, hroots, hnon, hE⟩ := rckLab_tree_len K hK hT hadj hcheck hlt hcard
    hcount htrees S hp hpL hTp i (by omega) hn'
  have hn6 : n = 6 := hnc.trans h6
  subst hn6
  set β : Option (Fin τ.rank) → Fin τ.rank → ℤ := fun x => v • K.extRoot x with hβ
  have hsmulcombo : ∀ n' : Option (Fin τ.rank) → ℕ,
      v • K.combo n' = ∑ x, (n' x : ℤ) • β x := by
    intro n'
    unfold KacData.combo
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm v ((n' x : ℕ) : ℤ) (K.extRoot x)
  have hset : (fun α => v • α) '' K.rootsOf (Set.range l) = rootsOfFam β (Set.range l) := by
    ext γ
    constructor
    · rintro ⟨γ₀, ⟨hr0, n', hn', hγ⟩, rfl⟩
      refine ⟨IsRoot.smul hr0 v, n', hn', ?_⟩
      rcases hγ with rfl | rfl
      · exact Or.inl (hsmulcombo n')
      · exact Or.inr (by show v • (-K.combo n') = _; rw [smul_neg, hsmulcombo])
    · rintro ⟨hr, n', hn', hγ⟩
      refine ⟨v⁻¹ • γ, ⟨IsRoot.smul hr v⁻¹, n', hn', ?_⟩, smul_inv_smul v γ⟩
      rcases hγ with rfl | rfl
      · left
        rw [← hsmulcombo, inv_smul_smul]
      · right
        rw [smul_neg, ← hsmulcombo, inv_smul_smul]
  refine ⟨fun k => β (l k), fun k => IsRoot.smul (K.isRoot_extRoot (l k)) v, ?_, ?_, ?_, ?_⟩
  · rw [hroots, hset, rckLab_rootsOfFam_range β l hlinj]
  · intro c d hcd h1 h2
    show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
    rw [iform_smul]
    exact hnon c d hcd h1 h2
  · intro c d hcd
    obtain ⟨ρ, σ, hρ, h01, h12⟩ := hframes (F := L) (l c) (l d) (hE c d hcd)
    show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = -1
    rw [iform_smul, ← h01, ← h12]
    exact rckLab_iform_edge hτ hρ
  · intro F _ c d hcd
    exact treeFrames K hframes v l (edgeE 6) hE (F := F) c d hcd

theorem rckE6_labelled
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : compRank (componentRoots (rootCharHom a) i) = 6)
    (hn : (componentRoots (rootCharHom a) i).ncard = 72) :
    ∃ β : Fin 6 → Fin τ.rank → ℤ, (∀ b, IsRoot τ (β b)) ∧
      componentRoots (rootCharHom a) i = rootsOfFam β Set.univ ∧
      (∀ c d : Fin 6, c ≠ d → ¬ edgeE 6 c d → ¬ edgeE 6 d c → iform (β c) (β d) = 0) ∧
      (∀ c d : Fin 6, edgeE 6 c d → iform (β c) (β d) = -1) ∧
      ∀ {F : Type} [Field F] (c d : Fin 6), edgeE 6 c d →
        ∃ θ : SL(3, F) →* ModGL τ F,
          θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β c) ∧
            θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β d) := by
  classical
  rcases hτ with rfl | rfl | rfl
  · exact rckLab_of_data (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_ecount e6_etrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTp i h6 hn
  · exact rckLab_of_data (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_ecount e7_etrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTp i h6 hn
  · exact rckLab_of_data (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_ecount e8_etrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTp i h6 hn

end CFSG.StandardType.RCKRP

end
