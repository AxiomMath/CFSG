module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Frame
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgE7
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacEAll
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.LieType.Chevalley.OrthogonalUnionBruhat
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.ThirdLineE8

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups Matrix


theorem exists_tree_mem_of_class_rank
    {τ : Tag}
    (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)}
    {tp : ℕ → ℕ → List ℕ} (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    (adjf : ∀ n : ℕ, Fin n → Fin n → Prop) (nmin : ℕ) (cnt : ℕ → ℕ)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, nmin ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = cnt c.length →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ nmin ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ adjf P.length c d → ¬ adjf P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, adjf P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (Q : ℕ → Prop) (hQ : ∀ P ∈ trees, Q P.length)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h4 : nmin ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      cnt (compRank (componentRoots (rootCharHom a) i))) :
    ∃ (v : WeylGroup τ) (n : ℕ) (l : Fin n → Option (Fin τ.rank)), nmin ≤ n ∧ Q n ∧
      compRank (componentRoots (rootCharHom a) i) = n ∧
      componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l) ∧
      (∀ c d : Fin n, c ≠ d → ¬ adjf n c d → ¬ adjf n d c →
        iform (K.extRoot (l c)) (K.extRoot (l d)) = 0) ∧
      (∀ c d : Fin n, adjf n c d → (nodeIdx (l c), nodeIdx (l d)) ∈ E) ∧
      ∃ P ∈ trees, Set.range l = {x | x ∈ P} := by
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
  have hrank' := hrank
  rw [hrank] at h4 hn
  rw [hncard] at hn
  obtain ⟨P, hP, hsame⟩ := hcount c hc h4 hn
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
  have hcP : c.length = P.length := by
    have h1 : (C : Set (Option (Fin τ.rank))).ncard = c.length := by
      rw [Set.ncard_coe_finset]
      exact hcard c hc
    have h2 : (Set.range P.get).ncard = P.length := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ (List.nodup_iff_injective_get.mp hnd),
        Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [← h1, hCP, h2]
  refine ⟨v, P.length, P.get, hlen, hQ P hP, hrank'.trans hcP, by rw [hi', hCP], hnon, hE, ?_⟩
  exact ⟨P, hP, Set.range_list_get P⟩

theorem rckRetE7_levi
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 7)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 126) :
    (τ = .E7 ∨ τ = .E8) ∧ ∃ v : WeylGroup τ,
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots τ {j : Fin τ.rank | j.val < Tag.E7.rank} := by
  classical
  have hpL : (p : GGL) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff GGL 2 p).1 h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have hle : 7 ≤ τ.rank := hrank ▸ compRank_le_rank _
  have hτ : τ = .E7 ∨ τ = .E8 := by
    cases τ <;> simp [Tag.rank] at hle ⊢
  refine ⟨hτ, ?_⟩
  rcases hτ with rfl | rfl
  ·
    have hsub : componentRoots (rootCharHom a) i ⊆ {δ : Fin Tag.E7.rank → ℤ | IsRoot .E7 δ} := by
      intro δ hδ
      exact isRoot_of_mem_componentRoots hδ
    have hrootfin : {δ : Fin Tag.E7.rank → ℤ | IsRoot .E7 δ} = ↑(rootFinset .E7) := by
      ext δ
      simp only [Set.mem_ofPred_eq, Finset.mem_coe]
      exact mem_rootFinset.symm
    have heq : componentRoots (rootCharHom a) i = {δ : Fin Tag.E7.rank → ℤ | IsRoot .E7 δ} :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, ncard_isRoot_E7]) (by
        rw [hrootfin]
        exact Finset.finite_toSet _)
    have hJ : {j : Fin Tag.E7.rank | j.val < Tag.E7.rank} = Set.univ := by
      ext j
      simp
    have hpar : parabolicRoots .E7 {j : Fin Tag.E7.rank | j.val < Tag.E7.rank} =
        {δ : Fin Tag.E7.rank → ℤ | IsRoot .E7 δ} := by
      rw [hJ]
      ext δ
      simp [parabolicRoots]
    refine ⟨1, ?_⟩
    rw [heq, hpar]
    simp
  ·
    have h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    have hn' : (componentRoots (rootCharHom a) i).ncard =
        eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
      rw [hcard, hrank]
      rfl
    obtain ⟨v, n, l, -, -, hrk, hroots, hnon, hE, ⟨P, hP, hrange⟩⟩ :=
      exists_tree_mem_of_class_rank kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card
        edgeE 6 eRootCount e8_ecount e8_etrees (fun n => n = 6 ∨ n = 7 ∨ n = 8) e8_elen S hp hpL
        hTp i h6 hn'
    have hn7 : n = 7 := by rw [← hrk, hrank]
    subst hn7
    have hP_cases : P = [some 0, some 1, some 2, some 3, some 4, some 5] ∨
        P = [some 0, some 1, some 2, some 3, some 4, some 5, some 6] ∨
        P = [some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7] := by
      change P ∈ [[some 0, some 1, some 2, some 3, some 4, some 5],
        [some 0, some 1, some 2, some 3, some 4, some 5, some 6],
        [some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7]] at hP
      rcases List.mem_cons.1 hP with h | h
      · exact Or.inl h
      rcases List.mem_cons.1 h with h | h
      · exact Or.inr (Or.inl h)
      rcases List.mem_cons.1 h with h | h
      · exact Or.inr (Or.inr h)
      · exact absurd h List.not_mem_nil
    have hC : none ∉ P.toFinset := by
      rcases hP_cases with rfl | rfl | rfl <;> simp
    have hnd : P.Nodup := (e8_etrees P hP).1
    have hset : Set.range l = ↑(P.toFinset) := by
      rw [hrange]
      ext x
      simp [List.mem_toFinset]
    have hcomp : compRank (kacE8.rootsOf (Set.range l)) = 7 := by
      rw [← compRank_image v (kacE8.rootsOf (Set.range l)), ← hroots, hrank]
    have hPlen : P.length = 7 := by
      rw [hset] at hcomp
      have h1 : compRank (kacE8.rootsOf ↑(P.toFinset)) = P.toFinset.card :=
        compRank_rootsOf kacE8 facts_E8 (C := P.toFinset) ⟨none, hC⟩
      rw [hcomp] at h1
      rw [List.toFinset_card_of_nodup hnd] at h1
      exact h1.symm
    have hP_eq : P = [some 0, some 1, some 2, some 3, some 4, some 5, some 6] := by
      rcases hP_cases with rfl | rfl | rfl <;> simp_all
    have hCJ : ∀ j : Fin Tag.E8.rank, some j ∈ P.toFinset ↔ j.val < 7 := by
      rw [hP_eq]
      decide
    have hpar : kacE8.rootsOf (Set.range l) = parabolicRoots Tag.E8 {j | j.val < 7} := by
      rw [hset]
      exact rootsOf_eq_parabolicRoots kacE8 facts_E8 hC hCJ
    refine ⟨v, ?_⟩
    rw [hroots, hpar]
    rfl

theorem rckRetE7_rho_mem {τ : Tag} {p₀ : ℕ}
    (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hτ : τ = .E7 ∨ τ = .E8)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 126) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  obtain ⟨j, hj⟩ := outer_exists_image_component S hT i
  by_cases hij : i = j
  · subst hij
    intro γ hγ
    rw [← hj]
    exact Set.mem_image_of_mem _ hγ
  · exfalso
    have hcard' : (componentRoots (rootCharHom a) j).ncard = 126 := by
      rw [← hj, Set.ncard_image_of_injective _ S.ρ.injective, hcard]
    have hdisj : Disjoint (componentRoots (rootCharHom a) i) (componentRoots (rootCharHom a) j) :=
      Set.disjoint_left.2 fun α hα hα' => hij (eq_of_mem_componentRoots hα hα')
    have hfin : {α : Fin τ.rank → ℤ | IsRoot τ α}.Finite := finite_setOf_isRoot τ
    have hsub : ∀ k : KernelComponent (rootCharHom a),
        componentRoots (rootCharHom a) k ⊆ {α : Fin τ.rank → ℤ | IsRoot τ α} :=
      fun k α hα => hα.1.1
    have hunion : (componentRoots (rootCharHom a) i ∪ componentRoots (rootCharHom a) j).ncard =
        252 := by
      rw [Set.ncard_union_eq hdisj (hfin.subset (hsub i)) (hfin.subset (hsub j)), hcard, hcard']
    have hle := Set.ncard_le_ncard (Set.union_subset (hsub i) (hsub j)) hfin
    rw [hunion] at hle
    rcases hτ with rfl | rfl
    · rw [ncard_isRoot_E7] at hle
      omega
    · rw [CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.ncard_isRoot_E8] at hle
      omega

theorem rckRetE7_twistKind {τ : Tag} {L : Type} [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (hrank : compRank (componentRoots χ i) = 7) (hcard : (componentRoots χ i).ncard = 126) :
    twistKind ρ χ i = .inner := by
  unfold twistKind
  rw [hrank, hcard]
  split_ifs with h1 h2 h3 h4
  · rfl
  · exfalso
    rcases h2 with h | h <;> omega
  · omega
  · omega
  · rfl

theorem compRank_roots_E7 : compRank {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ} = 7 := by
  unfold compRank
  have hspan : Submodule.span ℚ ((fun γ (i : Fin Tag.E7.rank) => (γ i : ℚ)) ''
      {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ}) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ (Fin Tag.E7.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨Pi.single k 1, isRoot_single Tag.E7 k, ?_⟩
    funext i
    simp [Pi.single_apply]
  rw [hspan, finrank_top, Module.finrank_fin_fun]
  rfl

end CFSG.StandardType.RCKRP

end
