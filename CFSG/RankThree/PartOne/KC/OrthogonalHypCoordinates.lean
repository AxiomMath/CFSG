module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin

section Coordinates

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {r : ℕ}

@[expose] def pairVec (P : Fin r → HypPair Q) : Fin r ⊕ Fin r → V :=
  Sum.elim (fun i => (P i).e) (fun i => (P i).f)

@[expose] noncomputable def hypCoordSymm (P : Fin r → HypPair Q) :
    ((Fin r ⊕ Fin r → K) × ↥(pairsPerp P)) →ₗ[K] V :=
  (Fintype.linearCombination K (pairVec P)).coprod (pairsPerp P).subtype

theorem hypCoordSymm_apply (P : Fin r → HypPair Q) (z : Fin r ⊕ Fin r → K)
    (u : ↥(pairsPerp P)) :
    hypCoordSymm P (z, u) = ∑ x, z x • pairVec P x + (u : V) := by
  simp [hypCoordSymm, Fintype.linearCombination_apply]

variable {P : Fin r → HypPair Q}

theorem polar_pairVec_f (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (x : Fin r ⊕ Fin r) (j : Fin r) :
    polar Q (pairVec P x) (P j).f = if x = Sum.inl j then 1 else 0 := by
  obtain ⟨hef, -, -, hff⟩ := polar_pairs hP
  rcases x with i | i
  · simp [pairVec, hef]
  · simp [pairVec, hff]

theorem polar_pairVec_e (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (x : Fin r ⊕ Fin r) (j : Fin r) :
    polar Q (pairVec P x) (P j).e = if x = Sum.inr j then 1 else 0 := by
  obtain ⟨-, hfe, hee, -⟩ := polar_pairs hP
  rcases x with i | i
  · simp [pairVec, hee]
  · simp [pairVec, hfe]

theorem polar_hypCoordSymm_f (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (z : Fin r ⊕ Fin r → K)
    (u : ↥(pairsPerp P)) (j : Fin r) :
    polar Q (hypCoordSymm P (z, u)) (P j).f = z (Sum.inl j) := by
  have hu : polar Q (u : V) (P j).f = 0 := by
    have := (HypPair.mem_perp.mp ((mem_pairsPerp P).mp u.2 j)).2
    rwa [polar_comm] at this
  rw [hypCoordSymm_apply, polar_add_left, polar_sum_smul_left]
  simp [polar_pairVec_f hP, hu]

theorem polar_hypCoordSymm_e (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (z : Fin r ⊕ Fin r → K)
    (u : ↥(pairsPerp P)) (j : Fin r) :
    polar Q (hypCoordSymm P (z, u)) (P j).e = z (Sum.inr j) := by
  have hu : polar Q (u : V) (P j).e = 0 := by
    have := (HypPair.mem_perp.mp ((mem_pairsPerp P).mp u.2 j)).1
    rwa [polar_comm] at this
  rw [hypCoordSymm_apply, polar_add_left, polar_sum_smul_left]
  simp [polar_pairVec_e hP, hu]

theorem hypCoordSymm_injective (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    Function.Injective (hypCoordSymm P) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨z, u⟩ h
  have hz : z = 0 := by
    funext x
    rcases x with j | j
    · have := polar_hypCoordSymm_f hP z u j
      rwa [h, polar_zero_left, eq_comm] at this
    · have := polar_hypCoordSymm_e hP z u j
      rwa [h, polar_zero_left, eq_comm] at this
  subst hz
  have hu : (u : V) = 0 := by
    rw [hypCoordSymm_apply] at h
    simpa using h
  exact Prod.ext rfl (Subtype.ext hu)

theorem hypCoordSymm_surjective (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    Function.Surjective (hypCoordSymm P) := by
  intro v
  refine ⟨(Sum.elim (fun i => polar Q v (P i).f) (fun i => polar Q v (P i).e),
    ⟨v - ∑ i, (polar Q v (P i).f • (P i).e + polar Q v (P i).e • (P i).f),
      sub_sum_mem_pairsPerp hP v⟩), ?_⟩
  rw [hypCoordSymm_apply, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, pairVec, Finset.sum_add_distrib]
  abel

@[expose] noncomputable def hypCoordEquiv (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    V ≃ₗ[K] (Fin r ⊕ Fin r → K) × ↥(pairsPerp P) :=
  (LinearEquiv.ofBijective (hypCoordSymm P)
    ⟨hypCoordSymm_injective hP, hypCoordSymm_surjective hP⟩).symm

theorem hypCoordEquiv_symm_apply (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    (w : (Fin r ⊕ Fin r → K) × ↥(pairsPerp P)) :
    (hypCoordEquiv hP).symm w = hypCoordSymm P w :=
  rfl

theorem hypCoordEquiv_apply_eq (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (v : V)
    (w : (Fin r ⊕ Fin r → K) × ↥(pairsPerp P)) :
    hypCoordEquiv hP v = w ↔ hypCoordSymm P w = v := by
  constructor
  · rintro rfl
    exact (hypCoordEquiv hP).symm_apply_apply v
  · intro h
    rw [← h]
    exact (hypCoordEquiv hP).apply_symm_apply w

theorem hypCoordEquiv_e (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (i : Fin r) :
    hypCoordEquiv hP (P i).e = hypVec K ↥(pairsPerp P) (Sum.inl i) := by
  rw [hypCoordEquiv_apply_eq, hypVec, hypCoordSymm_apply]
  simp [pairVec, Pi.single_apply]

theorem hypCoordEquiv_f (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (i : Fin r) :
    hypCoordEquiv hP (P i).f = hypVec K ↥(pairsPerp P) (Sum.inr i) := by
  rw [hypCoordEquiv_apply_eq, hypVec, hypCoordSymm_apply]
  simp [pairVec, Pi.single_apply]

theorem hypCoordEquiv_of_mem (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) {u : V}
    (hu : u ∈ pairsPerp P) : hypCoordEquiv hP u = (0, ⟨u, hu⟩) := by
  rw [hypCoordEquiv_apply_eq, hypCoordSymm_apply]
  simp

theorem quadTail_hypCoordSymm (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (z : Fin r ⊕ Fin r → K)
    (u : ↥(pairsPerp P)) :
    Q (hypCoordSymm P (z, u)) = quadTail r (Q.comp (pairsPerp P).subtype) (z, u) := by
  obtain ⟨hef, hfe, hee, hff⟩ := polar_pairs hP
  set E : V := ∑ i, z (Sum.inl i) • (P i).e with hE
  set F : V := ∑ i, z (Sum.inr i) • (P i).f with hF
  have hsplit : ∑ x, z x • pairVec P x = E + F := by
    rw [Fintype.sum_sum_type]
    rfl
  have hEmem : E ∈ Submodule.span K (Set.range fun i => (P i).e) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hFmem : F ∈ Submodule.span K (Set.range fun i => (P i).f) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hQE : Q E = 0 :=
    map_eq_zero_of_mem_span (S := Set.range fun i => (P i).e)
      (by rintro _ ⟨i, rfl⟩; exact (P i).Q_e)
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hee i j) hEmem
  have hQF : Q F = 0 :=
    map_eq_zero_of_mem_span (S := Set.range fun i => (P i).f)
      (by rintro _ ⟨i, rfl⟩; exact (P i).Q_f)
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hff i j) hFmem
  have hEF : polar Q E F = ∑ i, z (Sum.inl i) * z (Sum.inr i) := by
    rw [hE, hF, polar_sum_smul_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [polar_sum_smul_right]
    simp [hef]
  have hEFS : E + F ∈ pairsSpan P := by
    refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl ⟨i, rfl⟩))) (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))
  rw [hypCoordSymm_apply, hsplit, QuadraticMap.map_add Q, QuadraticMap.map_add Q, hQE, hQF, hEF,
    polar_pairsSpan_pairsPerp P hEFS u.2, quadTail_apply, quadPlus_apply]
  simp

theorem quadTail_hypCoordEquiv (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (v : V) :
    quadTail r (Q.comp (pairsPerp P).subtype) (hypCoordEquiv hP v) = Q v := by
  have h : hypCoordSymm P (hypCoordEquiv hP v) = v := (hypCoordEquiv hP).symm_apply_apply v
  rcases hw : hypCoordEquiv hP v with ⟨z, u⟩
  rw [hw] at h
  rw [← h, quadTail_hypCoordSymm hP]

@[expose] noncomputable def hypCoordIsometry (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    Q.IsometryEquiv (quadTail r (Q.comp (pairsPerp P).subtype)) :=
  { hypCoordEquiv hP with map_app' := quadTail_hypCoordEquiv hP }

section Split

variable (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (hU : pairsPerp P = ⊥)
include hU

@[expose] noncomputable def hypCoordSplitEquiv : V ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  haveI : Unique ↥(pairsPerp P) :=
    haveI : Subsingleton ↥(pairsPerp P) := Submodule.subsingleton_iff_eq_bot.mpr hU
    Unique.mk' _
  (hypCoordEquiv hP).trans LinearEquiv.prodUnique

theorem hypCoordSplitEquiv_apply (v : V) : hypCoordSplitEquiv hP hU v = (hypCoordEquiv hP v).1 :=
  rfl

theorem quadPlus_hypCoordSplitEquiv (v : V) : quadPlus r K (hypCoordSplitEquiv hP hU v) = Q v := by
  have h := quadTail_hypCoordEquiv hP v
  have hu : ∀ u : ↥(pairsPerp P), u = 0 := fun u => Subtype.ext
    ((Submodule.mem_bot K).mp (hU ▸ u.2))
  rw [← h, quadTail_apply, hypCoordSplitEquiv_apply, hu (hypCoordEquiv hP v).2]
  simp

theorem hypCoordSplitEquiv_e (i : Fin r) :
    hypCoordSplitEquiv hP hU (P i).e = Pi.single (Sum.inl i) 1 := by
  rw [hypCoordSplitEquiv_apply, hypCoordEquiv_e]
  rfl

theorem hypCoordSplitEquiv_f (i : Fin r) :
    hypCoordSplitEquiv hP hU (P i).f = Pi.single (Sum.inr i) 1 := by
  rw [hypCoordSplitEquiv_apply, hypCoordEquiv_f]
  rfl

@[expose] noncomputable def hypCoordSplitIsometry : Q.IsometryEquiv (quadPlus r K) :=
  { hypCoordSplitEquiv hP hU with map_app' := quadPlus_hypCoordSplitEquiv hP hU }

end Split

end Coordinates

end CFSG.RankThree.PartOne.KCOrthogonal
