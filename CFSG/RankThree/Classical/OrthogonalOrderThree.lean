module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly.LowTwoRank

open scoped Matrix commutatorElement

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

noncomputable abbrev permGL : Equiv.Perm ι →* GL ι K :=
  (Matrix.permMatrixHom).toHomUnits

theorem permGL_mulVec (π : Equiv.Perm ι) (v : ι → K) :
    ((permGL π : GL ι K) : Matrix ι ι K) *ᵥ v = v ∘ ⇑π⁻¹ := by
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]

theorem permGL_not_mem_statedScalars {π : Equiv.Perm ι} (hπ : π ≠ 1) :
    (permGL π : GL ι K) ∉ StatedScalars ι K := by
  rintro ⟨c, hc⟩
  obtain ⟨i, hi⟩ : ∃ i, π i ≠ i := by
    by_contra h
    push Not at h
    exact hπ (Equiv.ext h)
  have h1 := congrArg (fun A : GL ι K => ((A : Matrix ι ι K) *ᵥ Pi.single i (1 : K)) (π i)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, permGL_mulVec, Function.comp_apply,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply, Pi.single_eq_same] at h1
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.single_eq_of_ne hi, mul_zero] at h1
  exact zero_ne_one h1

theorem permGL_mem_isometryGroup {Q : (ι → K) → K} {π : Equiv.Perm ι}
    (hπ : ∀ v, Q (v ∘ ⇑π⁻¹) = Q v) :
    permGL π ∈ Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
  Subgroup.subset_closure fun v => by rw [permGL_mulVec]; exact hπ v

theorem orderOf_commutator_swap_swap {m : ℕ} (hm : 3 ≤ m) :
    ⁅Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩,
      Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨2, by omega⟩⁆ ^ 3 = 1 ∧
    ⁅Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩,
      Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨2, by omega⟩⁆ ≠ 1 := by
  set s := Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩
  set t := Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨2, by omega⟩
  have h3 : (s * t).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  have hρ : ⁅s, t⁆ = (s * t) ^ 2 := by
    rw [commutatorElement_def, Equiv.swap_inv, Equiv.swap_inv, pow_two]
    simp only [mul_assoc]
    rfl
  have hst3 : (s * t) ^ 3 = 1 := by rw [← h3.orderOf]; exact pow_orderOf_eq_one _
  refine ⟨by rw [hρ, ← pow_mul, mul_comm, pow_mul, hst3, one_pow], fun h => ?_⟩
  rw [hρ] at h
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [h3.orderOf] at hdvd
  omega

theorem exists_orderOf_eq_three_statedProj_statedOmega {m : ℕ} (hm : 3 ≤ m)
    (Q : (ι → K) → K) (φ : Equiv.Perm (Fin m) →* Equiv.Perm ι) (hφ : Function.Injective φ)
    (hQ : ∀ x v, Q (v ∘ ⇑(φ x)) = Q v) :
    ∃ y : StatedProj (StatedOmega Q), orderOf y = 3 := by
  obtain ⟨h3, hne⟩ := orderOf_commutator_swap_swap hm
  set s := Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩
  set t := Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨2, by omega⟩
  set ρ := ⁅s, t⁆ with hρdef
  have hiso : ∀ x, permGL (K := K) (φ x) ∈
      Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} := fun x =>
    permGL_mem_isometryGroup fun v => by rw [← map_inv]; exact hQ x⁻¹ v
  have hg : permGL (K := K) (φ ρ) ∈ StatedOmega Q := by
    rw [hρdef, map_commutatorElement, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hiso s) (hiso t)
  refine ⟨(QuotientGroup.mk ⟨_, hg⟩ : StatedProj (StatedOmega Q)), orderOf_eq_prime ?_ ?_⟩
  · rw [← QuotientGroup.mk_pow]
    have : (⟨_, hg⟩ : StatedOmega Q) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, ← map_pow, h3, map_one, map_one]; rfl)
    rw [this, QuotientGroup.mk_one]
  · rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine permGL_not_mem_statedScalars fun h1 => hne (hφ ?_)
    rw [h1, map_one]

end Generic

@[expose] def pairPermHom (m : ℕ) (X : Type) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin m ⊕ Fin m ⊕ X) :=
  (Equiv.Perm.sumCongrHom _ _).comp ((MonoidHom.id _).prod
    ((Equiv.Perm.sumCongrHom _ _).comp (MonoidHom.inl _ _)))

theorem pairPermHom_inl {m : ℕ} {X : Type} (x : Equiv.Perm (Fin m)) (i : Fin m) :
    pairPermHom m X x (Sum.inl i) = Sum.inl (x i) :=
  rfl

theorem pairPermHom_inr_inl {m : ℕ} {X : Type} (x : Equiv.Perm (Fin m)) (i : Fin m) :
    pairPermHom m X x (Sum.inr (Sum.inl i)) = Sum.inr (Sum.inl (x i)) :=
  rfl

theorem pairPermHom_inr_inr {m : ℕ} {X : Type} (x : Equiv.Perm (Fin m)) (u : X) :
    pairPermHom m X x (Sum.inr (Sum.inr u)) = Sum.inr (Sum.inr u) :=
  rfl

theorem pairPermHom_injective (m : ℕ) (X : Type) : Function.Injective (pairPermHom m X) := by
  intro x y h
  ext i
  have := congrArg (fun π : Equiv.Perm (Fin m ⊕ Fin m ⊕ X) => π (Sum.inl i)) h
  simp only [pairPermHom_inl, Sum.inl.injEq] at this
  rw [this]

@[expose] def pairPermHomPlus (m : ℕ) : Equiv.Perm (Fin m) →* Equiv.Perm (Fin m ⊕ Fin m) :=
  (Equiv.Perm.sumCongrHom _ _).comp ((MonoidHom.id _).prod (MonoidHom.id _))

theorem pairPermHomPlus_inl {m : ℕ} (x : Equiv.Perm (Fin m)) (i : Fin m) :
    pairPermHomPlus m x (Sum.inl i) = Sum.inl (x i) :=
  rfl

theorem pairPermHomPlus_inr {m : ℕ} (x : Equiv.Perm (Fin m)) (i : Fin m) :
    pairPermHomPlus m x (Sum.inr i) = Sum.inr (x i) :=
  rfl

theorem pairPermHomPlus_injective (m : ℕ) : Function.Injective (pairPermHomPlus m) := by
  intro x y h
  ext i
  have := congrArg (fun π : Equiv.Perm (Fin m ⊕ Fin m) => π (Sum.inl i)) h
  simp only [pairPermHomPlus_inl, Sum.inl.injEq] at this
  rw [this]

variable {K : Type} [Field K]

theorem statedQuadOdd_comp_pairPermHom (n : ℕ) (x : Equiv.Perm (Fin n))
    (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    StatedQuadOdd n K (v ∘ ⇑(pairPermHom n Unit x)) = StatedQuadOdd n K v := by
  simp only [StatedQuadOdd, Function.comp_apply, pairPermHom_inl, pairPermHom_inr_inl,
    pairPermHom_inr_inr]
  rw [Equiv.sum_comp x (fun i => v (Sum.inl i) * v (Sum.inr (Sum.inl i)))]

theorem statedQuadPlus_comp_pairPermHomPlus (n : ℕ) (x : Equiv.Perm (Fin n))
    (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n K (v ∘ ⇑(pairPermHomPlus n x)) = StatedQuadPlus n K v := by
  simp only [StatedQuadPlus, Function.comp_apply, pairPermHomPlus_inl, pairPermHomPlus_inr]
  rw [Equiv.sum_comp x (fun i => v (Sum.inl i) * v (Sum.inr i))]

theorem statedQuadMinus_comp_pairPermHom (n : ℕ) (b c : K) (x : Equiv.Perm (Fin (n - 1)))
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c (v ∘ ⇑(pairPermHom (n - 1) (Fin 2) x)) = StatedQuadMinus n K b c v := by
  simp only [StatedQuadMinus, Function.comp_apply, pairPermHom_inl, pairPermHom_inr_inl,
    pairPermHom_inr_inr]
  rw [Equiv.sum_comp x (fun i => v (Sum.inl i) * v (Sum.inr (Sum.inl i)))]

theorem orthogonal_model_exists_orderOf_eq_three {T : Type} [Group T] {t : StatedLieTag}
    {n p f : ℕ} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hT : StatedClassicalModel T t n p f) : (∃ x : T, orderOf x = 3) ∧ 3 ∣ Nat.card T := by
  suffices h : ∃ x : T, orderOf x = 3 by
    obtain ⟨x, hx⟩ := h
    exact ⟨⟨x, hx⟩, hx ▸ orderOf_dvd_natCard x⟩
  rcases ht with rfl | rfl | rfl
  · obtain ⟨-, -, hn, -⟩ := hT.1
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := hT.2
    obtain ⟨y, hy⟩ := exists_orderOf_eq_three_statedProj_statedOmega hn (StatedQuadOdd n K)
      (pairPermHom n Unit) (pairPermHom_injective n Unit) (statedQuadOdd_comp_pairPermHom n)
    exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq, hy]⟩
  · obtain ⟨-, -, hn⟩ := hT.1
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := hT.2
    obtain ⟨y, hy⟩ := exists_orderOf_eq_three_statedProj_statedOmega (by omega : 3 ≤ n)
      (StatedQuadPlus n K) (pairPermHomPlus n) (pairPermHomPlus_injective n)
      (statedQuadPlus_comp_pairPermHomPlus n)
    exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq, hy]⟩
  · obtain ⟨-, -, hn⟩ := hT.1
    obtain ⟨K, _, _, -, b, c, -, ⟨e⟩⟩ := hT.2
    obtain ⟨y, hy⟩ := exists_orderOf_eq_three_statedProj_statedOmega (by omega : 3 ≤ n - 1)
      (StatedQuadMinus n K b c) (pairPermHom (n - 1) (Fin 2))
      (pairPermHom_injective (n - 1) (Fin 2)) (statedQuadMinus_comp_pairPermHom n b c)
    exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq, hy]⟩

end CFSG.RankThree.Classical
