module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMain
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgTyped
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType.RCKRP

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.K155X (l154_smul_image_rootsOf_eq)
open scoped MatrixGroups

theorem rckD_twistInner {τ : Tag} {L : Type} [Field L] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} {i : KernelComponent χ}
    (hkind : twistKind ρ χ i = .inner) (h4 : 4 ≤ compRank (componentRoots χ i))
    (hn : (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1)) :
    twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) := by
  by_contra hno
  simp only [twistKind, hno, if_false] at hkind
  split_ifs at hkind
  all_goals simp_all

private theorem rckD_labelled_of_data
    {τ : Tag} (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
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
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1)) :
    ∃ (n : ℕ) (β : Option (Fin τ.rank) → Fin τ.rank → ℤ) (l : Fin n → Option (Fin τ.rank)),
      n = compRank (componentRoots (rootCharHom a) i) ∧ (∀ b, IsRoot τ (β b)) ∧
      componentRoots (rootCharHom a) i = rootsOfFam β (Set.range l) ∧
      (∀ c d : Fin n, c ≠ d → ¬ edgeD n c d → ¬ edgeD n d c →
        iform (β (l c)) (β (l d)) = 0) ∧
      ∀ {F : Type} [Field F] (c d : Fin n), edgeD n c d →
        ∃ θ : SL(3, F) →* ModGL τ F,
          θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β (l c)) ∧
            θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β (l d)) := by
  classical
  obtain ⟨v, n, l, -, -, hroots, hnon, hE, hnrank⟩ :=
    CompsPTwoDMain.exists_tree_of_class' K hK hT hadj hcheck hlt hcard edgeD 4
      (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  exact ⟨n, fun x => v • K.extRoot x, l, hnrank,
    fun b => IsRoot.smul (K.isRoot_extRoot b) v,
    by rw [hroots, l154_smul_image_rootsOf_eq],
    fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2,
    fun {F} _ c d hcd => treeFrames K hframes v l (edgeD n) hE (F := F) c d hcd⟩

theorem rckD_labelled
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1)) :
    ∃ (n : ℕ) (β : Option (Fin τ.rank) → Fin τ.rank → ℤ) (l : Fin n → Option (Fin τ.rank)),
      n = compRank (componentRoots (rootCharHom a) i) ∧ (∀ b, IsRoot τ (β b)) ∧
      componentRoots (rootCharHom a) i = rootsOfFam β (Set.range l) ∧
      (∀ c d : Fin n, c ≠ d → ¬ edgeD n c d → ¬ edgeD n d c → iform (β (l c)) (β (l d)) = 0) ∧
      ∀ {F : Type} [Field F] (c d : Fin n), edgeD n c d →
        ∃ θ : SL(3, F) →* ModGL τ F,
          θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β (l c)) ∧
            θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β (l d)) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact rckD_labelled_of_data kacD4 facts_D4 d4_tree d4_adj d4_check d4_lt d4_card
      d4_dcount d4_dtrees (fun {F} _ x y h => d4_frames x y h) S hp hpL hTp i h4 hn
  · exact rckD_labelled_of_data kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card
      e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTp i h4 hn
  · exact rckD_labelled_of_data kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card
      e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTp i h4 hn
  · exact rckD_labelled_of_data kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card
      e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTp i h4 hn

end CFSG.StandardType.RCKRP

end
