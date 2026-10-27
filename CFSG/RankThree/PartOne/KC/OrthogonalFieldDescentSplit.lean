module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.Blueprint.SourceClassicalModels

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Blueprint.EvenSource

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W]

section Perp

variable [FiniteDimensional F W] {Q : QuadraticForm F W}

theorem finrank_le_of_perp_singular (hnd : (polarBilin Q).Nondegenerate) {E S : Submodule F W}
    (hE : ∀ x : W, (∀ e ∈ E, polar Q x e = 0) → Q x = 0 → x ∈ E)
    (hS : ∀ x ∈ S, Q x = 0) : finrank F S ≤ finrank F E := by
  have hrefl : (polarBilin Q).IsRefl := (QuadraticMap.isSymm_polarBilin Q).isRefl
  let perp : Submodule F W → Submodule F W := fun X =>
    LinearMap.BilinForm.orthogonal (polarBilin Q) X
  have hdim : ∀ X : Submodule F W, finrank F (perp X) = finrank F W - finrank F X := fun X =>
    LinearMap.BilinForm.finrank_orthogonal hnd X
  have hdd : ∀ X : Submodule F W, perp (perp X) = X := fun X =>
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl X
  have hmem : ∀ (X : Submodule F W) (x : W), x ∈ perp X ↔ ∀ y ∈ X, polar Q y x = 0 :=
    fun X x => Iff.rfl
  have hanti : ∀ {X Y : Submodule F W}, X ≤ Y → perp Y ≤ perp X := fun h =>
    LinearMap.BilinForm.orthogonal_le h
  have hSS : S ≤ perp S := by
    intro x hx
    rw [hmem]
    intro y hy
    have h : polar Q y x = Q (y + x) - Q y - Q x := rfl
    rw [h, hS _ (S.add_mem hy hx), hS y hy, hS x hx]
    simp
  set S₁ : Submodule F W := S ⊓ perp E with hS₁
  have hS₁E : S₁ ≤ E := by
    intro x hx
    refine hE x (fun e he => ?_) (hS x hx.1)
    rw [polar_comm]
    exact (hmem E x).mp hx.2 e he
  have hS₁E' : S₁ ≤ E ⊓ perp S := le_inf hS₁E fun x hx => hSS hx.1
  have hperp : perp (E ⊔ perp S) = S₁ := by
    apply le_antisymm
    · intro x hx
      refine ⟨?_, ?_⟩
      · rw [← hdd S]
        exact hanti le_sup_right hx
      · exact hanti le_sup_left hx
    · rintro x ⟨hxS, hxE⟩
      rw [hmem]
      intro y hy
      obtain ⟨e, he, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
      have h1 : polar Q e x = 0 := (hmem E x).mp hxE e he
      have h2 : polar Q x t = 0 := (hmem S t).mp ht x hxS
      rw [polar_add_left, h1, polar_comm Q t x, h2, add_zero]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq E (perp S)
  have h2 := hdim (E ⊔ perp S)
  have h3 := hdim S
  have h4 := Submodule.finrank_mono hS₁E'
  have h5 := Submodule.finrank_le (E ⊔ perp S)
  have h6 := Submodule.finrank_le S
  rw [hperp] at h2
  omega

end Perp

structure HypSplit (Q : QuadraticForm F W) (m δ : ℕ) where
  b : Basis (Fin m ⊕ Fin m ⊕ Fin δ) F W
  eval : ∀ (x y : Fin m → F) (z : Fin δ → F),
    Q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr (.inl i)) + ∑ j, z j • b (.inr (.inr j))) =
      ∑ i, x i * y i + Q (∑ j, z j • b (.inr (.inr j)))
  aniso : ∀ z : Fin δ → F, Q (∑ j, z j • b (.inr (.inr j))) = 0 → z = 0

namespace HypSplit

variable {Q : QuadraticForm F W} {m δ : ℕ} (H : HypSplit Q m δ)

@[expose] noncomputable def vec (x y : Fin m → F) (z : Fin δ → F) : W :=
  ∑ i, x i • H.b (.inl i) + ∑ i, y i • H.b (.inr (.inl i)) + ∑ j, z j • H.b (.inr (.inr j))

theorem Q_vec (x y : Fin m → F) (z : Fin δ → F) :
    Q (H.vec x y z) = ∑ i, x i * y i + Q (H.vec 0 0 z) := by
  have h := H.eval x y z
  have h0 : H.vec 0 0 z = ∑ j, z j • H.b (.inr (.inr j)) := by simp [vec]
  rw [h0]
  exact h

theorem vec_repr (v : W) :
    H.vec (fun i => H.b.repr v (.inl i)) (fun i => H.b.repr v (.inr (.inl i)))
      (fun j => H.b.repr v (.inr (.inr j))) = v := by
  have h := H.b.sum_repr v
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  unfold vec
  rw [add_assoc]
  exact h

theorem Q_inl (j : Fin m) : Q (H.b (.inl j)) = 0 := by
  have h := H.Q_vec (Pi.single j 1) 0 0
  have h1 : H.vec (Pi.single j 1) 0 0 = H.b (.inl j) := by
    simp [vec, Pi.single_apply]
  rw [h1] at h
  simpa [vec] using h

theorem vec_add_inl (x y : Fin m → F) (z : Fin δ → F) (j : Fin m) :
    H.vec (x + Pi.single j 1) y z = H.vec x y z + H.b (.inl j) := by
  simp only [vec, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have : ∑ i, (Pi.single j (1 : F) : Fin m → F) i • H.b (.inl i) = H.b (.inl j) := by
    simp [Pi.single_apply]
  rw [this]
  abel

theorem vec_add_inr (x y : Fin m → F) (z : Fin δ → F) (j : Fin m) :
    H.vec x (y + Pi.single j 1) z = H.vec x y z + H.b (.inr (.inl j)) := by
  simp only [vec, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have : ∑ i, (Pi.single j (1 : F) : Fin m → F) i • H.b (.inr (.inl i)) =
      H.b (.inr (.inl j)) := by
    simp [Pi.single_apply]
  rw [this]
  abel

theorem Q_inr (j : Fin m) : Q (H.b (.inr (.inl j))) = 0 := by
  have h := H.Q_vec 0 (Pi.single j 1) 0
  have h1 : H.vec 0 (Pi.single j 1) 0 = H.b (.inr (.inl j)) := by
    simp [vec, Pi.single_apply]
  rw [h1] at h
  simpa [vec] using h

theorem polar_inl (v : W) (j : Fin m) :
    polar Q v (H.b (.inl j)) = H.b.repr v (.inr (.inl j)) := by
  set X := fun i => H.b.repr v (.inl i) with hX
  set Y := fun i => H.b.repr v (.inr (.inl i)) with hY
  set Z := fun j => H.b.repr v (.inr (.inr j)) with hZ
  have hv : v = H.vec X Y Z := (H.vec_repr v).symm
  have h1 := H.Q_vec (X + Pi.single j 1) Y Z
  have h2 := H.Q_vec X Y Z
  have h3 := H.Q_inl j
  have h4 : polar Q v (H.b (.inl j)) =
      Q (H.vec X Y Z + H.b (.inl j)) - Q (H.vec X Y Z) - Q (H.b (.inl j)) := by rw [← hv]; rfl
  rw [h4, ← H.vec_add_inl, h1, h2, h3]
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply, hY]

theorem polar_inr (v : W) (j : Fin m) :
    polar Q v (H.b (.inr (.inl j))) = H.b.repr v (.inl j) := by
  set X := fun i => H.b.repr v (.inl i) with hX
  set Y := fun i => H.b.repr v (.inr (.inl i)) with hY
  set Z := fun j => H.b.repr v (.inr (.inr j)) with hZ
  have hv : v = H.vec X Y Z := (H.vec_repr v).symm
  have h1 := H.Q_vec X (Y + Pi.single j 1) Z
  have h2 := H.Q_vec X Y Z
  have h3 := H.Q_inr j
  have h4 : polar Q v (H.b (.inr (.inl j))) =
      Q (H.vec X Y Z + H.b (.inr (.inl j))) - Q (H.vec X Y Z) - Q (H.b (.inr (.inl j))) := by
    rw [← hv]
    rfl
  rw [h4, ← H.vec_add_inr, h1, h2, h3]
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply, hX]

@[expose] noncomputable def hypPair (i : Fin m) : HypPair Q where
  e := H.b (.inl i)
  f := H.b (.inr (.inl i))
  Q_e := H.Q_inl i
  Q_f := H.Q_inr i
  polar_ef := by
    rw [polar_comm, H.polar_inl]
    simp

theorem hypPair_orth {i j : Fin m} (hij : i ≠ j) : (H.hypPair i).Orth (H.hypPair j) where
  ee := by
    change polar Q (H.b (.inl i)) (H.b (.inl j)) = 0
    rw [H.polar_inl]
    simp
  ef := by
    change polar Q (H.b (.inl i)) (H.b (.inr (.inl j))) = 0
    rw [H.polar_inr]
    simp [hij]
  fe := by
    change polar Q (H.b (.inr (.inl i))) (H.b (.inl j)) = 0
    rw [H.polar_inl]
    simp [hij]
  ff := by
    change polar Q (H.b (.inr (.inl i))) (H.b (.inr (.inl j))) = 0
    rw [H.polar_inr]
    simp

theorem tail_mem_perp (j : Fin δ) (i : Fin m) : H.b (.inr (.inr j)) ∈ (H.hypPair i).perp := by
  rw [HypPair.mem_perp]
  constructor
  · change polar Q (H.b (.inl i)) (H.b (.inr (.inr j))) = 0
    rw [polar_comm, H.polar_inl]
    simp
  · change polar Q (H.b (.inr (.inl i))) (H.b (.inr (.inr j))) = 0
    rw [polar_comm, H.polar_inr]
    simp

include H in
theorem finrank_eq [FiniteDimensional F W] : finrank F W = 2 * m + δ := by
  rw [finrank_eq_card_basis H.b]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

@[expose] def E : Submodule F W := Submodule.span F (Set.range fun i : Fin m => H.b (.inl i))

theorem finrank_E : finrank F H.E = m := by
  have hli : LinearIndependent F (fun i : Fin m => H.b (.inl i)) :=
    H.b.linearIndependent.comp _ Sum.inl_injective
  rw [E, finrank_span_eq_card hli, Fintype.card_fin]

theorem Q_eq_zero_of_mem_E {v : W} (hv : v ∈ H.E) : Q v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hv
  have h := H.Q_vec c 0 0
  have h1 : H.vec c 0 0 = ∑ i, c i • H.b (.inl i) := by simp [vec]
  rw [← h1, h]
  simp [vec]

include H in
theorem exists_totallySingular_three (hm : 3 ≤ m) :
    ∃ T : Submodule F W, finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  let f : Fin 3 → Fin m ⊕ Fin m ⊕ Fin δ := fun i => .inl ⟨i, by omega⟩
  have hf : Function.Injective f := fun i j h => by
    have := Sum.inl.inj h
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hli : LinearIndependent F (H.b ∘ f) := H.b.linearIndependent.comp f hf
  refine ⟨Submodule.span F (Set.range (H.b ∘ f)), ?_, fun x hx => ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · refine H.Q_eq_zero_of_mem_E ?_
    refine (Submodule.span_le.mpr ?_) hx
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩

include H in
theorem le_sourceWittIndex [FiniteDimensional F W] : m ≤ sourceWittIndex ⇑Q := by
  have := CFSG.Blueprint.EvenSource.le_sourceWittIndex (K := F) (V := W) (⇑Q)
    (W := H.E) (fun w hw => H.Q_eq_zero_of_mem_E hw)
  rwa [H.finrank_E] at this

include H in
theorem sourceWittIndex_eq [FiniteDimensional F W] (hnd : (polarBilin Q).Nondegenerate) :
    sourceWittIndex ⇑Q = m := by
  refine le_antisymm ?_ H.le_sourceWittIndex
  obtain ⟨S, hS, hSd⟩ := exists_sourceWittIndex (K := F) (V := W) (Q := ⇑Q)
    (QuadraticMap.map_zero Q)
  rw [← hSd, ← H.finrank_E]
  refine finrank_le_of_perp_singular hnd (fun x hx hQx => ?_) hS
  set X := fun i => H.b.repr x (.inl i)
  set Y := fun i => H.b.repr x (.inr (.inl i))
  set Z := fun j => H.b.repr x (.inr (.inr j))
  have hY : Y = 0 := by
    funext j
    have := hx (H.b (.inl j)) (Submodule.subset_span ⟨j, rfl⟩)
    rw [H.polar_inl] at this
    exact this
  have hxv : x = H.vec X 0 Z := by
    rw [← hY]
    exact (H.vec_repr x).symm
  have hQ0 : Q (H.vec 0 0 Z) = 0 := by
    have := H.Q_vec X 0 Z
    rw [← hxv, hQx] at this
    simpa using this.symm
  have hZ : Z = 0 := H.aniso Z (by simpa [vec] using hQ0)
  have h2 : H.vec X 0 0 = ∑ i, X i • H.b (.inl i) := by simp [vec]
  rw [hxv, hZ, h2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end HypSplit

end CFSG.RankThree.PartOne.KCOrthogonalDescent
