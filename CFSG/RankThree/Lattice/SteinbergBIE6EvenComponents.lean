module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenProduct

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley.C2E6Std Matrix

@[expose] def e6ComponentOrbits (J : Set (Fin Tag.E6.rank)) : Set (Set (Fin Tag.E6.rank → ℤ)) :=
  {Ξ | ∃ i ∈ J, Ξ = e6Xi J i}

@[expose] def rootSetSupport (Ξ : Set (Fin Tag.E6.rank → ℤ)) : Set (Fin Tag.E6.rank) :=
  {j | Pi.single j 1 ∈ Ξ}

section Orbits

variable (m : Fin 15)

theorem e6Xi_eq_parabolicRoots_union {i : Fin Tag.E6.rank} (hi : i ∈ e6QpSupport m) :
    e6Xi (e6QpSupport m) i = parabolicRoots Tag.E6
      (e6JComponent (e6QpSupport m) i ∪ e6JComponent (e6QpSupport m) (e6QpPerm m i)) := by
  set C := e6JComponent (e6QpSupport m) i
  set C' := e6JComponent (e6QpSupport m) (e6QpPerm m i)
  have hπ := (e6QpPerm_mem_iff m i).1 hi
  rw [e6Xi_eq m hi]
  ext α
  constructor
  · rintro (h | h)
    · exact ⟨h.1, fun j hj => h.2 j fun hc => hj (Or.inl hc)⟩
    · exact ⟨h.1, fun j hj => h.2 j fun hc => hj (Or.inr hc)⟩
  · intro hα
    by_cases hCC : C = C'
    · left
      refine ⟨hα.1, fun j hj => hα.2 j fun hs => ?_⟩
      rcases hs with h | h
      · exact hj h
      · exact hj (show j ∈ C from hCC ▸ h)
    · have hsep : ∀ a ∈ C, ∀ b ∈ C', Tag.E6.cartan a b = 0 := by
        intro a ha b hb
        by_contra hne
        exact hCC (e6JComponent_eq_of_adj m hi hπ ha hb (Or.inr hne))
      have hs : ∀ j, α j ≠ 0 → j ∈ C ∨ j ∈ C' := fun j hj => by
        by_contra h
        exact hj (hα.2 j h)
      rcases support_split hα.1 hsep hs with h | h
      · exact Or.inl ⟨hα.1, fun j hj => by by_contra h'; exact hj (h j h')⟩
      · exact Or.inr ⟨hα.1, fun j hj => by by_contra h'; exact hj (h j h')⟩

theorem rootSetSupport_e6Xi {i : Fin Tag.E6.rank} (hi : i ∈ e6QpSupport m) :
    rootSetSupport (e6Xi (e6QpSupport m) i) =
      e6JComponent (e6QpSupport m) i ∪ e6JComponent (e6QpSupport m) (e6QpPerm m i) := by
  ext j
  change Pi.single j 1 ∈ e6Xi (e6QpSupport m) i ↔ _
  rw [e6Xi_eq_parabolicRoots_union m hi, single_mem_parabolicRoots_iff]

theorem e6Xi_eq_parabolicRoots_support {i : Fin Tag.E6.rank} (hi : i ∈ e6QpSupport m) :
    e6Xi (e6QpSupport m) i = parabolicRoots Tag.E6 (rootSetSupport (e6Xi (e6QpSupport m) i)) := by
  rw [rootSetSupport_e6Xi m hi]
  exact e6Xi_eq_parabolicRoots_union m hi

theorem e6Xi_eq_of_e6JComponent_eq {x y : Fin Tag.E6.rank} (hx : x ∈ e6QpSupport m)
    (hy : y ∈ e6QpSupport m)
    (h : e6JComponent (e6QpSupport m) x = e6JComponent (e6QpSupport m) y) :
    e6Xi (e6QpSupport m) x = e6Xi (e6QpSupport m) y := by
  rw [e6Xi_eq m hx, e6Xi_eq m hy, h]
  have hyx : y ∈ e6JComponent (e6QpSupport m) x := h ▸ mem_e6JComponent_self _ y
  have h' := e6JComponent_eq (e6QpPerm_mem_e6JComponent m hyx)
  rw [h']

theorem e6Xi_e6QpPerm {x : Fin Tag.E6.rank} (hx : x ∈ e6QpSupport m) :
    e6Xi (e6QpSupport m) (e6QpPerm m x) = e6Xi (e6QpSupport m) x := by
  rw [e6Xi_eq m ((e6QpPerm_mem_iff m x).1 hx), e6Xi_eq m hx, e6QpPerm_perm_of_mem m hx,
    Set.union_comm]

theorem mem_e6QpSupport_of_mem_rootSetSupport {i : Fin Tag.E6.rank} (hi : i ∈ e6QpSupport m)
    {j : Fin Tag.E6.rank} (hj : j ∈ rootSetSupport (e6Xi (e6QpSupport m) i)) :
    j ∈ e6QpSupport m := by
  rw [rootSetSupport_e6Xi m hi] at hj
  rcases hj with h | h
  · exact mem_of_mem_e6JComponent hi h
  · exact mem_of_mem_e6JComponent ((e6QpPerm_mem_iff m i).1 hi) h

theorem isSeparated_rootSetSupport {i i' : Fin Tag.E6.rank} (hi : i ∈ e6QpSupport m)
    (hi' : i' ∈ e6QpSupport m) (hne : e6Xi (e6QpSupport m) i ≠ e6Xi (e6QpSupport m) i') :
    IsSeparated (rootSetSupport (e6Xi (e6QpSupport m) i))
      (rootSetSupport (e6Xi (e6QpSupport m) i')) := by
  have key : ∀ {x y : Fin Tag.E6.rank}, (x = i ∨ x = e6QpPerm m i) →
      (y = i' ∨ y = e6QpPerm m i') →
      ∀ a ∈ e6JComponent (e6QpSupport m) x, ∀ b ∈ e6JComponent (e6QpSupport m) y,
        a ≠ b ∧ Tag.E6.cartan a b = 0 := by
    intro x y hx hy a ha b hb
    have hxJ : x ∈ e6QpSupport m := by
      rcases hx with rfl | rfl
      · exact hi
      · exact (e6QpPerm_mem_iff m i).1 hi
    have hyJ : y ∈ e6QpSupport m := by
      rcases hy with rfl | rfl
      · exact hi'
      · exact (e6QpPerm_mem_iff m i').1 hi'
    have hXx : e6Xi (e6QpSupport m) x = e6Xi (e6QpSupport m) i := by
      rcases hx with rfl | rfl
      · rfl
      · exact e6Xi_e6QpPerm m hi
    have hXy : e6Xi (e6QpSupport m) y = e6Xi (e6QpSupport m) i' := by
      rcases hy with rfl | rfl
      · rfl
      · exact e6Xi_e6QpPerm m hi'
    by_contra h
    have h' : a = b ∨ Tag.E6.cartan a b ≠ 0 := by
      by_cases hab : a = b
      · exact Or.inl hab
      · exact Or.inr fun hc => h ⟨hab, hc⟩
    exact hne (hXx.symm.trans ((e6Xi_eq_of_e6JComponent_eq m hxJ hyJ
      (e6JComponent_eq_of_adj m hxJ hyJ ha hb h')).trans hXy))
  intro a ha b hb
  rw [rootSetSupport_e6Xi m hi] at ha
  rw [rootSetSupport_e6Xi m hi'] at hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact key (Or.inl rfl) (Or.inl rfl) a ha b hb
  · exact key (Or.inl rfl) (Or.inr rfl) a ha b hb
  · exact key (Or.inr rfl) (Or.inl rfl) a ha b hb
  · exact key (Or.inr rfl) (Or.inr rfl) a ha b hb

theorem mem_iff_exists_rootSetSupport (j : Fin Tag.E6.rank) :
    j ∈ e6QpSupport m ↔ ∃ Ξ ∈ e6ComponentOrbits (e6QpSupport m), j ∈ rootSetSupport Ξ := by
  constructor
  · intro hj
    refine ⟨_, ⟨j, hj, rfl⟩, ?_⟩
    rw [rootSetSupport_e6Xi m hj]
    exact Or.inl (mem_e6JComponent_self _ j)
  · rintro ⟨_, ⟨i, hi, rfl⟩, hj⟩
    exact mem_e6QpSupport_of_mem_rootSetSupport m hi hj

end Orbits

section Orth

@[expose] def e6QpOrthIdx (m : Fin 15) : Fin 15 :=
  if m = 12 then 0 else if m = 13 then 1 else m

theorem e6Qp_orth_check : ∀ m : Fin 15, ∀ k : Fin 72,
    (∀ i : Fin Tag.E6.rank, i ∉ e6QpSupportList (e6QpOrthIdx m) → e6Root k i = 0) →
    toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ e6Root k ≠ e6Root k →
    iform (e6Root k) (toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ e6Root k) = 0 := by
  decide +kernel

theorem orth_of_mem_parabolicRoots (m : Fin 15) {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 (e6QpSupport (e6QpOrthIdx m)))
    (hne : e6Delta (e6QpSupport m) α ≠ α) : iform α (e6Delta (e6QpSupport m) α) = 0 := by
  obtain ⟨k, rfl⟩ := exists_e6Root_eq hα.1
  rw [e6Delta_qp] at hne ⊢
  exact e6Qp_orth_check m k (fun i hi => hα.2 i hi) hne

theorem e6XiOrth_of_subset (m : Fin 15) {i : Fin Tag.E6.rank} {T : Set (Fin Tag.E6.rank)}
    (hT : e6Xi (e6QpSupport m) i ⊆ parabolicRoots Tag.E6 T)
    (h : ∀ α ∈ parabolicRoots Tag.E6 T, e6Delta (e6QpSupport m) α ≠ α →
      iform α (e6Delta (e6QpSupport m) α) = 0) :
    e6XiOrth (e6QpSupport m) i := by
  intro α hα k hk
  rw [e6Delta_qp_iterate] at hk ⊢
  split_ifs at hk ⊢
  · exact absurd rfl hk
  · exact h α (hT hα) hk

theorem e6JComponent_subset {J T : Set (Fin Tag.E6.rank)} {i : Fin Tag.E6.rank} (hi : i ∈ T)
    (hT : ∀ a ∈ T, ∀ b, e6JAdj J a b → b ∈ T) : e6JComponent J i ⊆ T := by
  intro j hj
  induction hj with
  | refl => exact hi
  | tail _ h ih => exact hT _ ih _ h

theorem parabolicRoots_mono {T T' : Set (Fin Tag.E6.rank)} (h : T ⊆ T') :
    parabolicRoots Tag.E6 T ⊆ parabolicRoots Tag.E6 T' :=
  fun _ hα => ⟨hα.1, fun i hi => hα.2 i fun h' => hi (h h')⟩

theorem e6Supp24_closed (m : Fin 15) (hm : m = 12 ∨ m = 13) :
    ∀ a ∈ e6Supp24, ∀ b, e6JAdj (e6QpSupport m) a b → b ∈ e6Supp24 := by
  intro a ha b hab
  obtain ⟨-, h2, -, h4⟩ := hab
  change a ∈ e6QpSupportList 12 at ha
  change b ∈ e6QpSupportList 12
  rcases hm with rfl | rfl
  · change b ∈ e6QpSupportList 12 at h2
    revert ha h2 h4
    fin_cases a <;> fin_cases b <;> decide
  · change b ∈ e6QpSupportList 13 at h2
    revert ha h2 h4
    fin_cases a <;> fin_cases b <;> decide

theorem e6Supp16_closed :
    ∀ a ∈ e6QpSupport 1, ∀ b, e6JAdj (e6QpSupport 13) a b → b ∈ e6QpSupport 1 := by
  intro a ha b hab
  obtain ⟨-, h2, -, h4⟩ := hab
  change a ∈ e6QpSupportList 1 at ha
  change b ∈ e6QpSupportList 1
  change b ∈ e6QpSupportList 13 at h2
  revert ha h2 h4
  fin_cases a <;> fin_cases b <;> decide

theorem e6XiOrth_or_e6Supp24 (m : Fin 15) {i : Fin Tag.E6.rank} (hi : i ∈ e6QpSupport m) :
    e6XiOrth (e6QpSupport m) i ∨
      ((m = 12 ∨ m = 13) ∧ e6Xi (e6QpSupport m) i = parabolicRoots Tag.E6 e6Supp24) := by
  have hπ := (e6QpPerm_mem_iff m i).1 hi
  by_cases hm : m = 12 ∨ m = 13
  · by_cases h13 : i = 1 ∨ i = 3
    · right
      refine ⟨hm, ?_⟩
      have hi24 : i ∈ e6Supp24 := mem_e6Supp24_iff.2 h13
      have hπ24 : e6QpPerm m i ∈ e6Supp24 := by
        refine mem_e6Supp24_iff.2 ?_
        rcases hm with rfl | rfl <;> rcases h13 with rfl | rfl <;> decide
      rw [e6Xi_eq_parabolicRoots_union m hi]
      congr 1
      refine Set.Subset.antisymm (Set.union_subset
        (e6JComponent_subset hi24 (e6Supp24_closed m hm))
        (e6JComponent_subset hπ24 (e6Supp24_closed m hm))) fun j hj => Or.inl ?_
      have hadj : ∀ a b : Fin Tag.E6.rank, a ∈ e6Supp24 → b ∈ e6Supp24 →
          b ∈ e6JComponent (e6QpSupport m) a := by
        intro a b ha hb
        have haJ : a ∈ e6QpSupport m := by
          rcases hm with rfl | rfl
          · exact ha
          · change a ∈ e6QpSupportList 13
            rcases mem_e6Supp24_iff.1 ha with rfl | rfl <;> decide
        have hbJ : b ∈ e6QpSupport m := by
          rcases hm with rfl | rfl
          · exact hb
          · change b ∈ e6QpSupportList 13
            rcases mem_e6Supp24_iff.1 hb with rfl | rfl <;> decide
        by_cases hab : a = b
        · rw [hab]
          exact mem_e6JComponent_self _ b
        · refine Relation.ReflTransGen.single ⟨haJ, hbJ, hab, ?_⟩
          rcases mem_e6Supp24_iff.1 ha with rfl | rfl <;>
            rcases mem_e6Supp24_iff.1 hb with rfl | rfl
          · exact absurd rfl hab
          · decide
          · decide
          · exact absurd rfl hab
      exact hadj i j hi24 hj
    · left
      have hm13 : m = 13 := by
        rcases hm with rfl | rfl
        · exfalso
          exact h13 ((mem_e6Supp24_iff).1 hi)
        · rfl
      subst hm13
      have hi16 : i ∈ e6QpSupport 1 := by
        have hi' : i ∈ e6QpSupportList 13 := hi
        change i ∈ e6QpSupportList 1
        clear hi hπ
        revert h13 hi'
        fin_cases i <;> decide
      have hπ16 : e6QpPerm 13 i ∈ e6QpSupport 1 := by
        have hi' : i ∈ e6QpSupportList 1 := hi16
        change e6QpPerm 13 i ∈ e6QpSupportList 1
        clear hi hπ hi16
        revert hi'
        fin_cases i <;> decide
      refine e6XiOrth_of_subset 13 (T := e6QpSupport 1) ?_ fun α hα hne =>
        orth_of_mem_parabolicRoots 13 hα hne
      rw [e6Xi_eq_parabolicRoots_union 13 hi]
      exact parabolicRoots_mono (Set.union_subset (e6JComponent_subset hi16 e6Supp16_closed)
        (e6JComponent_subset hπ16 e6Supp16_closed))
  · left
    have hidx : e6QpOrthIdx m = m := by
      unfold e6QpOrthIdx
      split_ifs with h1 h2
      · exact absurd (Or.inl h1) hm
      · exact absurd (Or.inr h2) hm
      · rfl
    refine e6XiOrth_of_subset m (T := e6QpSupport m) ?_ fun α hα hne => ?_
    · rw [e6Xi_eq_parabolicRoots_union m hi]
      exact parabolicRoots_mono (Set.union_subset (fun j hj => mem_of_mem_e6JComponent hi hj)
        (fun j hj => mem_of_mem_e6JComponent hπ hj))
    · exact orth_of_mem_parabolicRoots m (by rw [hidx]; exact hα) hne

end Orth

section Factor

variable (Ω : Type) [Field Ω] [CharP Ω 2] [IsAlgClosed Ω]

@[expose] def IsE6EvenFactor (J : Set (Fin Tag.E6.rank)) (f : ℕ) (Ξ : Set (Fin Tag.E6.rank → ℤ))
    (P : Subgroup (ModGL Tag.E6 Ω)) : Prop :=
  (∃ D : E6EvenFixedRootDatum Ω, D.J = J ∧ D.f = f ∧ D.Ξ = Ξ ∧ P = D.orbitGroup) ∨
    ((J = e6QpSupport 12 ∨ J = e6QpSupport 13) ∧ Ξ = parabolicRoots Tag.E6 e6Supp24 ∧
      P = e6P24 Ω J f)

variable {Ω}

theorem rootSetSupport_parabolicRoots (S : Set (Fin Tag.E6.rank)) :
    rootSetSupport (parabolicRoots Tag.E6 S) = S := by
  ext j
  exact single_mem_parabolicRoots_iff

theorem IsE6EvenFactor.le {J : Set (Fin Tag.E6.rank)} {f : ℕ} {Ξ : Set (Fin Tag.E6.rank → ℤ)}
    {P : Subgroup (ModGL Tag.E6 Ω)} (h : IsE6EvenFactor Ω J f Ξ P) :
    P ≤ subsystemGroup Tag.E6 Ω (rootSetSupport Ξ) := by
  rcases h with ⟨D, -, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · exact D.orbitGroup_le_subsystemGroup
  · rw [rootSetSupport_parabolicRoots]
    exact e6P24_le_subsystemGroup f

theorem IsE6EvenFactor.e6Commutant_eq {J : Set (Fin Tag.E6.rank)} {f : ℕ} (hf : 2 ≤ f)
    {Ξ : Set (Fin Tag.E6.rank → ℤ)} {P : Subgroup (ModGL Tag.E6 Ω)}
    (h : IsE6EvenFactor Ω J f Ξ P) :
    e6Commutant (P : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω (rootSetSupport Ξ) : Set (ModGL Tag.E6 Ω)) := by
  rcases h with ⟨D, -, -, rfl, rfl⟩ | ⟨hJ, rfl, rfl⟩
  · exact D.e6Commutant_orbitGroup_subsystemGroup
  · rw [rootSetSupport_parabolicRoots]
    exact e6Commutant_e6P24_subsystemGroup hJ hf

theorem exists_isE6EvenFactor
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {J : Set (Fin Tag.E6.rank)} (hJ : J ≠ Set.univ) (hst : ∀ i, i ∈ J ↔ e6Rho i ∈ J) {f : ℕ}
    (hf : 2 ≤ f) {Ξ : Set (Fin Tag.E6.rank → ℤ)} (hΞ : Ξ ∈ e6ComponentOrbits J) :
    ∃ P, IsE6EvenFactor Ω J f Ξ P := by
  obtain ⟨i, hi, rfl⟩ := hΞ
  obtain ⟨m, rfl⟩ := (gammaStable_iff_mem_e6QpSupport J).1 ⟨hJ, hst⟩
  rcases e6XiOrth_or_e6Supp24 m hi with horth | ⟨hm, hΞ⟩
  · exact ⟨_, Or.inl ⟨⟨halg, f, hf, e6QpSupport m, hJ, hst, i, hi, horth⟩, rfl, rfl, rfl, rfl⟩⟩
  · refine ⟨e6P24 Ω (e6QpSupport m) f, Or.inr ⟨?_, hΞ, rfl⟩⟩
    rcases hm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

end Factor

end CFSG.RankThree.Lattice
