module

public import CFSG.LocalAnalysis.StandardType.GGFamInnerCover
public import CFSG.LocalAnalysis.StandardType.GGFamInnerFiniteRecog
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacD
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMain
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.Models.TwistedPairs
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDChain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDDatum
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDKlein
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMinus
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDefs
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

theorem fam_strongRecogIn_of_tree
       {τ : Tag} (K : KacData τ) {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {P : StatedLieTag → ℕ → Prop}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hinner : twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)]))
    (v : WeylGroup τ) {n : ℕ} (l : Fin n → Option (Fin τ.rank))
    (hroots : componentRoots χ i = (fun α => v • α) '' K.rootsOf (Set.range l))
    (hrec : ∀ (K' : Type) [Field K'] [Finite K'] (p f : ℕ), p.Prime → 0 < f →
      Nat.card K' = p ^ f →
      GGStrongRecogIn P p (p ^ f)
        ↥(rootSpan τ K' (rootsOfFam (fun x => v • K.extRoot x) (Set.range l)))) :
    GGStrongRecogIn P (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i))
      ↥(rationalComponentM S.ρ S.Γ χ i) := by
  classical
  refine fam_strongRecogIn_of_inner S hρ i hinner (fun K' hK' _ => ?_)
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
  have hcomp : componentRootSpan K' χ i =
      rootSpan τ K' (rootsOfFam β (Set.range l)) := by
    show rootSpan τ K' (componentRoots χ i) = _
    rw [hroots, hset]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardK⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardK
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardK]
  rw [hK'card]
  exact hrec ↥K' (ringChar L) f hprime f.pos hK'card

theorem fam_strongRecogIn_of_dClass
       {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
    (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {b : Fin τ.rank → Lˣ} (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (hTp : rootDiagUnit τ b ^ p = 1) (i : KernelComponent χ)
    (j : KernelComponent (rootCharHom b))
    (hiso : componentRoots (rootCharHom b) j = componentRoots χ i)
    (h4 : 4 ≤ compRank (componentRoots χ i))
    (hn : (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) - 1))
    (hinner : twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)])) :
    GGStrongRecogIn (fun t k => t = .POmegaPlus ∧ k = compRank (componentRoots χ i)) (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i))
      ↥(rationalComponentM S.ρ S.Γ χ i) := by
  classical
  have h4' : 4 ≤ compRank (componentRoots (rootCharHom b) j) := by rw [hiso]; exact h4
  have hn' : (componentRoots (rootCharHom b) j).ncard =
      2 * compRank (componentRoots (rootCharHom b) j) *
        (compRank (componentRoots (rootCharHom b) j) - 1) := by rw [hiso]; exact hn
  obtain ⟨v, n, l, hn4, -, hrootsb, hnon, hE, hnr⟩ :=
    CompsPTwoDMain.exists_tree_of_class' K hK hT hadj hcheck hlt hcard edgeD 4
      (fun n => 2 * n * (n - 1)) hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp
      j h4' hn'
  have hroots : componentRoots χ i = (fun α => v • α) '' K.rootsOf (Set.range l) := by
    rw [← hiso]; exact hrootsb
  have hnr' : n = compRank (componentRoots χ i) := by rw [← hiso]; exact hnr
  refine fam_strongRecogIn_of_tree K S hρ i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  exact (ggStrongRecogIn_D hτ hn4 hp' hf hK' (fun x => v • K.extRoot x)
    (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (treeFrames K hframes v l (edgeD n) hE)).mono (fun t k h => ⟨h.1, h.2.trans hnr'⟩)

theorem fam_strongRecogIn_of_eClass
       {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
    (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
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
    (hlen : ∀ P ∈ trees, P.length = 6 ∨ P.length = 7 ∨ P.length = 8)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {b : Fin τ.rank → Lˣ} (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (hTp : rootDiagUnit τ b ^ p = 1) (i : KernelComponent χ)
    (j : KernelComponent (rootCharHom b))
    (hiso : componentRoots (rootCharHom b) j = componentRoots χ i)
    (h6 : 6 ≤ compRank (componentRoots χ i))
    (hn : (componentRoots χ i).ncard =
      eRootCount (compRank (componentRoots χ i)))
    (hinner : twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)])) :
    GGStrongRecogIn (fun t k =>
        (t = .E6 ∧ k = 0 ∧ compRank (componentRoots χ i) = 6) ∨
        (t = .E7 ∧ k = 0 ∧ compRank (componentRoots χ i) = 7) ∨
        (t = .E8 ∧ k = 0 ∧ compRank (componentRoots χ i) = 8)) (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i))
      ↥(rationalComponentM S.ρ S.Γ χ i) := by
  classical
  have h6' : 6 ≤ compRank (componentRoots (rootCharHom b) j) := by rw [hiso]; exact h6
  have hn' : (componentRoots (rootCharHom b) j).ncard =
      eRootCount (compRank (componentRoots (rootCharHom b) j)) := by rw [hiso]; exact hn
  obtain ⟨v, n, l, -, hQ, hrootsb, hnon, hE, hnr⟩ :=
    CompsPTwoDMain.exists_tree_of_class' K hK hT hadj hcheck hlt hcard edgeE 6 eRootCount hcount
      htrees (fun n => n = 6 ∨ n = 7 ∨ n = 8) hlen S hp hpL hTp j h6' hn'
  have hroots : componentRoots χ i = (fun α => v • α) '' K.rootsOf (Set.range l) := by
    rw [← hiso]; exact hrootsb
  have hnr' : n = compRank (componentRoots χ i) := by rw [← hiso]; exact hnr
  refine fam_strongRecogIn_of_tree K S hρ i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  have hgr : ∀ c d : Fin n, c ≠ d → ¬ edgeE n c d → ¬ edgeE n d c →
      iform ((fun x => v • K.extRoot x) (l c)) ((fun x => v • K.extRoot x) (l d)) = 0 := by
    intro c d hcd h1 h2
    show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
    rw [iform_smul]
    exact hnon c d hcd h1 h2
  have hfr := treeFrames K hframes v l (edgeE n) hE (F := K')
  have hroot : ∀ b, IsRoot τ ((fun x => v • K.extRoot x) b) :=
    fun b => IsRoot.smul (K.isRoot_extRoot b) v
  rcases hQ with rfl | rfl | rfl
  · exact (ggStrongRecogIn_E6 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr).mono
      (fun t k h => Or.inl ⟨h.1, h.2, hnr'.symm⟩)
  · exact (ggStrongRecogIn_E7 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr).mono
      (fun t k h => Or.inr (Or.inl ⟨h.1, h.2, hnr'.symm⟩))
  · exact (ggStrongRecogIn_E8 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr).mono
      (fun t k h => Or.inr (Or.inr ⟨h.1, h.2, hnr'.symm⟩))

end CFSG.StandardType.TableCRes
