module

public import CFSG.Timmesfeld.RankTwo.SimplyLaced

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.Blueprint

variable {K : Type} [Group K] {D : UniversalRootDatum K}

structure LeviEmbedding (D : UniversalRootDatum K) (i j : Fin D.rank) where
  L : Type
  [inst : Group L]
  emb : L →* K
  inj : Function.Injective emb
  le : ∀ γ ∈ pairRoots D i j, D.rootGroup γ ≤ emb.range

attribute [instance] LeviEmbedding.inst

namespace LeviEmbedding

variable {i j : Fin D.rank}

noncomputable def preimage (E : LeviEmbedding D i j) (g : K) : E.L := Function.invFun E.emb g

theorem emb_preimage (E : LeviEmbedding D i j) {g : K} (hg : g ∈ E.emb.range) :
    E.emb (E.preimage g) = g :=
  Function.invFun_eq hg

theorem preimage_emb (E : LeviEmbedding D i j) (a : E.L) : E.preimage (E.emb a) = a :=
  Function.leftInverse_invFun E.inj a

end LeviEmbedding

theorem eq_of_mem_pairRoots_self {k k' : Fin D.rank} {γ : Fin D.rank → ℤ}
    (h : γ ∈ pairRoots D k k) (h' : γ ∈ pairRoots D k' k') : k = k' := by
  by_contra hkk
  apply RootSystem.ne_zero_of_mem_roots D.isFiniteType D.divisible h.1
  funext l
  by_cases hl : l = k
  · subst hl
    exact h'.2 l hkk hkk
  · exact h.2 l hl hl

theorem eq_of_mem_pairRoots_of_mem_pairRoots {i j i' j' : Fin D.rank} {γ : Fin D.rank → ℤ}
    (hij : i < j) (hij' : i' < j') (h : γ ∈ pairRoots D i j) (h' : γ ∈ pairRoots D i' j')
    (hn : ∀ k, γ ∉ pairRoots D k k) : i = i' ∧ j = j' := by
  have hsupp : ∀ l, γ l ≠ 0 → (l = i ∨ l = j) ∧ (l = i' ∨ l = j') := by
    intro l hl
    refine ⟨?_, ?_⟩
    · by_contra hc
      push Not at hc
      exact hl (h.2 l hc.1 hc.2)
    · by_contra hc
      push Not at hc
      exact hl (h'.2 l hc.1 hc.2)
  have hi : γ i ≠ 0 := by
    intro hi
    apply hn j
    refine ⟨h.1, fun l hl _ => ?_⟩
    by_cases hli : l = i
    · rw [hli]; exact hi
    · exact h.2 l hli hl
  have hj : γ j ≠ 0 := by
    intro hj
    apply hn i
    refine ⟨h.1, fun l hl _ => ?_⟩
    by_cases hlj : l = j
    · rw [hlj]; exact hj
    · exact h.2 l hl hlj
  have hne : i ≠ j := ne_of_lt hij
  have hne' : i' ≠ j' := ne_of_lt hij'
  rcases (hsupp i hi).2 with hi1 | hi1 <;> rcases (hsupp j hj).2 with hj1 | hj1
  · exact absurd (hi1.trans hj1.symm) hne
  · exact ⟨hi1, hj1⟩
  · exfalso
    rw [hi1, hj1] at hij
    exact absurd (hij.trans hij') (lt_irrefl _)
  · exact absurd (hi1.trans hj1.symm) hne

variable (E : ∀ i j, i ≤ j → LeviEmbedding D i j) {H : Type} [Group H]
  (φ : ∀ i j (h : i ≤ j), (E i j h).L →* H)

noncomputable def frameMap (γ : Fin D.rank → ℤ) (g : D.rootGroup γ) : H := by
  classical
  exact if h1 : ∃ k, γ ∈ pairRoots D k k then
      φ _ _ le_rfl ((E (Classical.choose h1) (Classical.choose h1) le_rfl).preimage g)
    else if h2 : ∃ p : Fin D.rank × Fin D.rank, p.1 < p.2 ∧ γ ∈ pairRoots D p.1 p.2 then
      φ _ _ (Classical.choose_spec h2).1.le
        ((E _ _ (Classical.choose_spec h2).1.le).preimage g)
    else 1

variable {E φ}

theorem frameMap_of_mem_self {k : Fin D.rank} {γ : Fin D.rank → ℤ} (hγ : γ ∈ pairRoots D k k)
    (g : D.rootGroup γ) : frameMap E φ γ g = φ k k le_rfl ((E k k le_rfl).preimage g) := by
  classical
  have h1 : ∃ k, γ ∈ pairRoots D k k := ⟨k, hγ⟩
  have hk : Classical.choose h1 = k :=
    eq_of_mem_pairRoots_self (Classical.choose_spec h1) hγ
  unfold frameMap
  rw [dite_eq_left_of_eq_true (eq_true h1)]
  have key : ∀ k', k' = k → φ k' k' le_rfl ((E k' k' le_rfl).preimage g) =
      φ k k le_rfl ((E k k le_rfl).preimage g) := by
    rintro _ rfl; rfl
  exact key _ hk

theorem frameMap_of_mem_pair {i j : Fin D.rank} (hij : i < j) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ pairRoots D i j) (hn : ∀ k, γ ∉ pairRoots D k k) (g : D.rootGroup γ) :
    frameMap E φ γ g = φ i j hij.le ((E i j hij.le).preimage g) := by
  classical
  have h1 : ¬ ∃ k, γ ∈ pairRoots D k k := fun ⟨k, hk⟩ => hn k hk
  have h2 : ∃ p : Fin D.rank × Fin D.rank, p.1 < p.2 ∧ γ ∈ pairRoots D p.1 p.2 :=
    ⟨(i, j), hij, hγ⟩
  unfold frameMap
  rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_left_of_eq_true (eq_true h2)]
  have key : ∀ (p : Fin D.rank × Fin D.rank) (hp : p.1 < p.2), γ ∈ pairRoots D p.1 p.2 →
      φ p.1 p.2 hp.le ((E p.1 p.2 hp.le).preimage g) =
        φ i j hij.le ((E i j hij.le).preimage g) := by
    rintro ⟨i', j'⟩ hp hp'
    obtain ⟨rfl, rfl⟩ := eq_of_mem_pairRoots_of_mem_pairRoots hij hp hγ hp' hn
    rfl
  exact key _ (Classical.choose_spec h2).1 (Classical.choose_spec h2).2

theorem lieModel_of_leviEmbeddings {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hZ : Subgroup.center H = ⊥)
    (hcompat : ∀ i j (h : i ≤ j) k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots D k k,
      ∀ g ∈ D.rootGroup γ,
        φ i j h ((E i j h).preimage g) = φ k k le_rfl ((E k k le_rfl).preimage g))
    (hgen : Subgroup.closure (⋃ k, Set.range (frameMap E φ (Pi.single k 1)) ∪
      Set.range (frameMap E φ (-Pi.single k 1))) = ⊤)
    (hnt : ∃ k, ∃ x, frameMap E φ (Pi.single k 1) x ≠ 1) :
    LieModel H t n p f := by
  have hpair : ∀ i j (h : i ≤ j), ExtendsToHom D.rootGroup (pairRoots D i j) (frameMap E φ) := by
    intro i j h
    refine extendsToHom_of_injective (E i j h).inj (φ i j h) fun γ hγ g => ?_
    have hg : (g : K) ∈ (E i j h).emb.range := (E i j h).le γ hγ g.2
    refine ⟨(E i j h).preimage g, (E i j h).emb_preimage hg, ?_⟩
    by_cases hs : ∃ k, γ ∈ pairRoots D k k
    · obtain ⟨k, hk⟩ := hs
      rw [frameMap_of_mem_self hk]
      have hki : k = i ∨ k = j := by
        by_contra hc
        push Not at hc
        apply RootSystem.ne_zero_of_mem_roots D.isFiniteType D.divisible hk.1
        funext l
        by_cases hl : l = k
        · subst hl; exact hγ.2 l hc.1 hc.2
        · exact hk.2 l hl hl
      exact (hcompat i j h k hki γ hk g g.2).symm
    · push Not at hs
      rcases lt_or_eq_of_le h with hlt | rfl
      · rw [frameMap_of_mem_pair hlt hγ hs]
      · exact absurd hγ (hs i)
  have hpair' : ∀ i j, ExtendsToHom D.rootGroup (pairRoots D i j) (frameMap E φ) := by
    intro i j
    rcases le_total i j with h | h
    · exact hpair i j h
    · rw [pairRoots_comm]; exact hpair j i h
  refine lieModel_of_frame hCT hL hZ (frameMap E φ)
    (fun i j _ _ _ _ _ => (hpair' i j).mono Set.inter_subset_right)
    (fun k => (hpair' k k).mono fun γ hγ => ?_) hgen hnt
  rcases hγ with rfl | rfl
  exacts [(Levi.single_mem_pairRoots (Or.inl rfl)).1, (Levi.single_mem_pairRoots (Or.inl rfl)).2]

end CFSG.Timmesfeld
