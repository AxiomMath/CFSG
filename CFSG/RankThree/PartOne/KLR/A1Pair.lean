module

public import CFSG.RankThree.PartOne.KLR.A1Swap
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Ree.Duality
public import CFSG.RankThree.PartOne.KE.SigmaCentralizer
public import CFSG.RankThree.SteinbergR3EEvenQuadraticSL2Fixed

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

structure A1Pair (i j : Fin ReeTag.F4.tag.rank) : Prop where
  ne : i ≠ j
  cartan : Tag.F4.cartan i j = 0
  long : ReeTag.F4.quadForm (Pi.single i 1) = 4
  short : ReeTag.F4.quadForm (Pi.single j 1) = 2
  roots : ∀ γ : Fin ReeTag.F4.tag.rank → ℤ, IsRoot ReeTag.F4.tag γ →
    (∀ k, k ≠ i → k ≠ j → γ k = 0) →
      γ = Pi.single i 1 ∨ γ = -Pi.single i 1 ∨ γ = Pi.single j 1 ∨ γ = -Pi.single j 1


theorem a1Pair_mk (i j : Fin ReeTag.F4.tag.rank) (hij : i ≠ j) (hc : Tag.F4.cartan i j = 0)
    (hl : ReeTag.F4.quadForm (Pi.single i 1) = 4) (hs : ReeTag.F4.quadForm (Pi.single j 1) = 2)
    (hr : ∀ γ ∈ rootFinset ReeTag.F4.tag, (∀ k, k ≠ i → k ≠ j → γ k = 0) →
      γ = Pi.single i 1 ∨ γ = -Pi.single i 1 ∨ γ = Pi.single j 1 ∨ γ = -Pi.single j 1) :
    A1Pair i j :=
  ⟨hij, hc, hl, hs, fun γ hγ => hr γ (mem_rootFinset.2 hγ)⟩

theorem a1Pair_zero_two : A1Pair ⟨0, by decide⟩ ⟨2, by decide⟩ :=
  a1Pair_mk _ _ (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

theorem a1Pair_zero_three : A1Pair ⟨0, by decide⟩ ⟨3, by decide⟩ :=
  a1Pair_mk _ _ (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

theorem a1Pair_one_three : A1Pair ⟨1, by decide⟩ ⟨3, by decide⟩ :=
  a1Pair_mk _ _ (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

section Pair

variable {L : Type} [Field L] {i j : Fin ReeTag.F4.tag.rank}

theorem A1Pair.no_root_comb (h : A1Pair i j) {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hs₂ : s₂ = 1 ∨ s₂ = -1) (p : ℕ × ℕ) (h1 : 0 < p.1) (h2 : 0 < p.2) :
    ¬ IsRoot ReeTag.F4.tag (p.1 • (s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) +
      p.2 • (s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ))) := by
  intro hroot
  have hvi : (p.1 • (s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) +
      p.2 • (s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ))) i = p.1 * s₁ := by
    simp [h.ne]
  have hvj : (p.1 • (s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) +
      p.2 • (s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ))) j = p.2 * s₂ := by
    simp [h.ne.symm]
  rcases hroot.nonneg_or_nonpos with hnn | hnp
  · have e1 := hnn i
    have e2 := hnn j
    rw [hvi] at e1
    rw [hvj] at e2
    rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl
    · simp only [one_smul] at hroot
      exact not_isRoot_nsmul_single_add_nsmul_single h.ne h.cartan h1 h2 hroot
    · omega
    · omega
    · omega
  · have e1 := hnp i
    have e2 := hnp j
    rw [hvi] at e1
    rw [hvj] at e2
    rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl
    · omega
    · omega
    · omega
    · have hneg := IsRoot.neg hroot
      refine not_isRoot_nsmul_single_add_nsmul_single h.ne h.cartan h1 h2 ?_
      convert hneg using 1
      ext k
      simp [Pi.single_apply]
      ring

theorem A1Pair.commute_pinnedX (h : A1Pair i j) {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hs₂ : s₂ = 1 ∨ s₂ = -1) (c d : L) :
    pinnedX ReeTag.F4.tag L (s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) c *
        pinnedX ReeTag.F4.tag L (s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) d =
      pinnedX ReeTag.F4.tag L (s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) d *
        pinnedX ReeTag.F4.tag L (s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) c := by
  have hα : IsRoot ReeTag.F4.tag (s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) := by
    rcases hs₁ with rfl | rfl
    · simpa using isRoot_single ReeTag.F4.tag i
    · simpa using IsRoot.neg (isRoot_single ReeTag.F4.tag i)
  have hβ : IsRoot ReeTag.F4.tag (s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) := by
    rcases hs₂ with rfl | rfl
    · simpa using isRoot_single ReeTag.F4.tag j
    · simpa using IsRoot.neg (isRoot_single ReeTag.F4.tag j)
  have hne : s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) ≠
      s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) := fun he => by
    have := congrFun he i
    simp [h.ne] at this
    rcases hs₁ with rfl | rfl <;> simp at this
  have hne' : s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) ≠
      -(s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) := fun he => by
    have := congrFun he i
    simp [h.ne] at this
    rcases hs₁ with rfl | rfl <;> simp at this
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula ReeTag.F4.tag hα hβ hne hne'
  have hnil : commPairs ReeTag.F4.tag (s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ))
      (s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) = [] := by
    refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
    obtain ⟨h1, h2, hroot⟩ := (hmem p).1 hp
    exact h.no_root_comb hs₁ hs₂ p h1 h2 hroot
  have hF' := hF L c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg,
    ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at hF'
  exact hF'

theorem A1Pair.commute_rootSubgroup (h : A1Pair i j) {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hs₂ : s₂ = 1 ∨ s₂ = -1) :
    ∀ x ∈ rootSubgroup ReeTag.F4.tag L (s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)),
      ∀ y ∈ rootSubgroup ReeTag.F4.tag L (s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)),
        x * y = y * x :=
  commute_of_closure (s := Set.range (pinnedX ReeTag.F4.tag L
    (s₁ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ))))
    (t := Set.range (pinnedX ReeTag.F4.tag L
    (s₂ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ))))
    (fun _ ⟨c, hc⟩ _ ⟨d, hd⟩ => hc ▸ hd ▸ h.commute_pinnedX hs₁ hs₂ c d)

theorem rankOne_eq_sup {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β) :
    rootRankOneGroup ReeTag.F4.tag L β =
      rootSubgroup ReeTag.F4.tag L β ⊔ rootSubgroup ReeTag.F4.tag L (-β) :=
  (exceptional_Lang_root_rank_one_torus_transport ReeTag.F4.tag L hβ).1

theorem A1Pair.commute_rankOne (h : A1Pair i j) :
    ∀ x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1),
      ∀ y ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1), x * y = y * x := by
  rw [rankOne_eq_sup (isRoot_single _ i), rankOne_eq_sup (isRoot_single _ j),
    Subgroup.sup_eq_closure, Subgroup.sup_eq_closure]
  refine commute_of_closure fun x hx y hy => ?_
  have h1 : (-(Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      (-1 : ℤ) • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) := (neg_one_smul ℤ _).symm
  have h2 : (-(Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      (-1 : ℤ) • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) := (neg_one_smul ℤ _).symm
  have e1 : (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      (1 : ℤ) • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) := (one_smul ℤ _).symm
  have e2 : (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      (1 : ℤ) • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) := (one_smul ℤ _).symm
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rw [e1] at hx
    rw [e2] at hy
    exact h.commute_rootSubgroup (Or.inl rfl) (Or.inl rfl) x hx y hy
  · rw [e1] at hx
    rw [h2] at hy
    exact h.commute_rootSubgroup (Or.inl rfl) (Or.inr rfl) x hx y hy
  · rw [h1] at hx
    rw [e2] at hy
    exact h.commute_rootSubgroup (Or.inr rfl) (Or.inl rfl) x hx y hy
  · rw [h1] at hx
    rw [h2] at hy
    exact h.commute_rootSubgroup (Or.inr rfl) (Or.inr rfl) x hx y hy

theorem A1Pair.disjoint [CharP L 2] (h : A1Pair i j) :
    rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊓
      rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨β₀, rfl⟩, hxB⟩
  rw [Subgroup.mem_bot]
  have hinj := rootSL2_injective_of_field (K := L) (τ := ReeTag.F4.tag) (Pi.single i 1)
  have hc : ∀ g : SL2 L, rootSL2 ReeTag.F4.tag L (Pi.single i 1) g *
      rootSL2 ReeTag.F4.tag L (Pi.single i 1) β₀ =
      rootSL2 ReeTag.F4.tag L (Pi.single i 1) β₀ * rootSL2 ReeTag.F4.tag L (Pi.single i 1) g :=
    fun g => h.commute_rankOne _ ⟨g, rfl⟩ _ hxB
  have hu : uSL 1 * β₀ = β₀ * uSL 1 := hinj (by rw [map_mul, map_mul]; exact hc (uSL 1))
  have hv : vSL 1 * β₀ = β₀ * vSL 1 := hinj (by rw [map_mul, map_mul]; exact hc (vSL 1))
  have hum := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L)) hu
  have hvm := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L)) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hum hvm
  rw [coe_uSL] at hum
  rw [coe_vSL] at hvm
  have hscal := CFSG.RankThree.QuadraticSL2.eq_scalar_of_commute (β₀ : Matrix (Fin 2) (Fin 2) L)
    hum.symm hvm.symm
  have hdet : (β₀ : Matrix (Fin 2) (Fin 2) L).det = 1 := β₀.2
  have h1 : (β₀ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
    rw [hscal] at hdet
    simp [Matrix.scalar_apply] at hdet
    rcases hdet with h | h
    · exact h
    · rw [h]
      exact CharTwo.neg_eq 1
  have hβ : β₀ = 1 := by
    refine Subtype.ext ?_
    rw [hscal, h1]
    simp
  rw [hβ, map_one]

theorem A1Pair.parabolicRoots_eq (h : A1Pair i j) :
    parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)) =
      {Pi.single i 1, -Pi.single i 1, Pi.single j 1, -Pi.single j 1} := by
  ext γ
  constructor
  · rintro ⟨hγ, hsupp⟩
    have := h.roots γ hγ fun k hki hkj => hsupp k (by simp [hki, hkj])
    simpa [Set.mem_insert_iff] using this
  · intro hγ
    have hk : ∀ k, k ∉ (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
        Set (Fin ReeTag.F4.tag.rank)) → k ≠ i ∧ k ≠ j := fun k hk => by
      simpa [not_or] using hk
    rcases hγ with rfl | rfl | rfl | rfl
    · exact ⟨isRoot_single _ i, fun k hkJ => Pi.single_eq_of_ne (hk k hkJ).1 _⟩
    · refine ⟨IsRoot.neg (isRoot_single _ i), fun k hkJ => ?_⟩
      simp [Pi.single_eq_of_ne (hk k hkJ).1]
    · exact ⟨isRoot_single _ j, fun k hkJ => Pi.single_eq_of_ne (hk k hkJ).2 _⟩
    · refine ⟨IsRoot.neg (isRoot_single _ j), fun k hkJ => ?_⟩
      simp [Pi.single_eq_of_ne (hk k hkJ).2]

theorem A1Pair.rootSpan_eq (h : A1Pair i j) :
    rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) =
      rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
        rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) := by
  rw [h.parabolicRoots_eq, rankOne_eq_sup (isRoot_single _ i),
    rankOne_eq_sup (isRoot_single _ j)]
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    rcases hγ with rfl | rfl | rfl | rfl
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_of_le_right le_sup_left
    · exact le_sup_of_le_right le_sup_right
  · refine sup_le ?_ ?_
    · rw [← rankOne_eq_sup (isRoot_single _ i)]
      exact rootRankOneGroup_le_rootSpan (isRoot_single _ i) (by simp) (by simp)
    · rw [← rankOne_eq_sup (isRoot_single _ j)]
      exact rootRankOneGroup_le_rootSpan (isRoot_single _ j) (by simp) (by simp)

end Pair

end CFSG.RankThree.PartOne.KLR
