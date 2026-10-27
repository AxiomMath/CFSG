module

public import CFSG.Quasithin.Vol2.Ch12Sec2Affine

public section

namespace CFSG.Quasithin.H13.AffN

open Matrix CFSG.Assembly.LowTwoRank

variable {n : ℕ}

section Affine

@[expose] def affM (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A (Matrix.of fun i (_ : Fin 1) => b i)
      (0 : Matrix (Fin 1) (Fin n) (ZMod 2)) (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)))

theorem affM_mul (A A' : Matrix (Fin n) (Fin n) (ZMod 2)) (b b' : Fin n → ZMod 2) :
    affM A b * affM A' b' = affM (A * A') (A *ᵥ b' + b) := by
  unfold affM
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, add_comm]
  · simp
  · simp

theorem affM_one : affM (1 : Matrix (Fin n) (Fin n) (ZMod 2)) 0 = 1 := by
  unfold affM
  rw [Matrix.reindex_apply]
  have : (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) (ZMod 2))
      (Matrix.of fun i (_ : Fin 1) => (0 : Fin n → ZMod 2) i)
      (0 : Matrix (Fin 1) (Fin n) (ZMod 2)) (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))) = 1 := by
    rw [← Matrix.fromBlocks_one]
    congr 1
  rw [this]
  exact Matrix.submatrix_one_equiv _

theorem affM_det (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2) :
    (affM A b).det = A.det := by
  unfold affM
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem affM_cc (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2) (i j : Fin n) :
    affM A b (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  simp only [affM, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.castSucc i) = Sum.inl i from
      finSumFinEquiv_symm_apply_castAdd i,
    show finSumFinEquiv.symm (Fin.castSucc j) = Sum.inl j from
      finSumFinEquiv_symm_apply_castAdd j]
  rfl

theorem affM_cl (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2) (i : Fin n) :
    affM A b (Fin.castSucc i) (Fin.last n) = b i := by
  simp only [affM, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.castSucc i) = Sum.inl i from
      finSumFinEquiv_symm_apply_castAdd i,
    show finSumFinEquiv.symm (Fin.last n) = Sum.inr 0 from finSumFinEquiv_symm_last]
  rfl

theorem affM_lc (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2) (j : Fin n) :
    affM A b (Fin.last n) (Fin.castSucc j) = 0 := by
  simp only [affM, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.castSucc j) = Sum.inl j from
      finSumFinEquiv_symm_apply_castAdd j,
    show finSumFinEquiv.symm (Fin.last n) = Sum.inr 0 from finSumFinEquiv_symm_last]
  rfl

theorem affM_ll (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2) :
    affM A b (Fin.last n) (Fin.last n) = 1 := by
  simp only [affM, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.last n) = Sum.inr 0 from finSumFinEquiv_symm_last]
  rfl

theorem affM_inj {A A' : Matrix (Fin n) (Fin n) (ZMod 2)} {b b' : Fin n → ZMod 2}
    (h : affM A b = affM A' b') : A = A' ∧ b = b' := by
  refine ⟨?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h (Fin.castSucc i)) (Fin.castSucc j)
    rwa [affM_cc, affM_cc] at this
  · funext i
    have := congrFun (congrFun h (Fin.castSucc i)) (Fin.last n)
    rwa [affM_cl, affM_cl] at this

theorem eq_affM_of_shape (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))
    (hrow : ∀ j : Fin n, g (Fin.last n) (Fin.castSucc j) = 0)
    (hll : g (Fin.last n) (Fin.last n) = 1) :
    g = affM (fun i j => g (Fin.castSucc i) (Fin.castSucc j))
      (fun i => g (Fin.castSucc i) (Fin.last n)) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact hll.trans (affM_ll _ _).symm
    | cast j => exact (hrow j).trans (affM_lc _ _ j).symm
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      exact (affM_cl (fun i j => g (Fin.castSucc i) (Fin.castSucc j))
        (fun i => g (Fin.castSucc i) (Fin.last n)) i).symm
    | cast j =>
      exact (affM_cc (fun i j => g (Fin.castSucc i) (Fin.castSucc j))
        (fun i => g (Fin.castSucc i) (Fin.last n)) i j).symm

@[expose] def tM (n : ℕ) [NeZero n] : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
  affM 1 (Pi.single 0 1)

theorem tM_mul_self (n : ℕ) [NeZero n] : tM n * tM n = 1 := by
  unfold tM
  rw [affM_mul, Matrix.one_mul, Matrix.one_mulVec]
  have : (Pi.single 0 1 : Fin n → ZMod 2) + Pi.single 0 1 = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero _
  rw [this, affM_one]

@[expose] def tGL (n : ℕ) [NeZero n] : GL (Fin (n + 1)) (ZMod 2) :=
  ⟨tM n, tM n, tM_mul_self n, tM_mul_self n⟩

theorem shape_of_commute [NeZero n] (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))
    (hg : g * tM n = tM n * g) (hdet : g.det ≠ 0) :
    (∀ j : Fin n, g (Fin.last n) (Fin.castSucc j) = 0) ∧ g (Fin.last n) (Fin.last n) = 1 := by
  have key : ∀ j : Fin n, g (Fin.last n) (Fin.castSucc j) = 0 := by
    intro j
    have h := congrFun (congrFun hg (Fin.castSucc 0)) (Fin.castSucc j)
    simp only [tM, Matrix.mul_apply, Fin.sum_univ_castSucc, affM_cc, affM_cl, affM_lc] at h
    simpa [Matrix.one_apply, Pi.single_apply] using h
  refine ⟨key, ?_⟩
  by_contra hne
  apply hdet
  apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last n)
  intro j
  induction j using Fin.lastCases with
  | last =>
    revert hne
    generalize g (Fin.last n) (Fin.last n) = x
    revert x
    decide
  | cast j => exact key j

end Affine

section Embedding

variable {G : Type*} [Group G] {L V : Subgroup G}
  (hLV : L ≤ Subgroup.normalizer (V : Set G))
  (α : ↥L →* ↥(StatedSL n (ZMod 2)))
  (hker : α.ker = V.subgroupOf L)
  (s : ↥(StatedSL n (ZMod 2)) →* ↥L) (hs : ∀ g, α (s g) = g)
  (β : ↥V →* Multiplicative (Fin n → ZMod 2))
  (hβeq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) =
      ((α ℓ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        (Multiplicative.toAdd (β u)))

include hker hs in
theorem nu_mem (l : ↥L) : l * (s (α l))⁻¹ ∈ V.subgroupOf L := by
  rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]

@[expose] noncomputable def nuV (l : ↥L) : ↥V :=
  ⟨((l * (s (α l))⁻¹ : ↥L) : G), Subgroup.mem_subgroupOf.mp (nu_mem α hker s hs l)⟩

theorem coe_nuV (l : ↥L) : ((nuV α hker s hs l : ↥V) : G) = ((l * (s (α l))⁻¹ : ↥L) : G) :=
  rfl

theorem nuV_mul (l₁ l₂ : ↥L) :
    ((nuV α hker s hs (l₁ * l₂) : ↥V) : G) =
      (l₁ : G) * (nuV α hker s hs l₂ : G) * (l₁ : G)⁻¹ * (nuV α hker s hs l₁ : G) := by
  simp only [nuV, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
  group

@[expose] noncomputable def psiM (l : ↥L) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
  affM ((α l : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
    (Multiplicative.toAdd (β (nuV α hker s hs l)))

include hβeq hLV in
theorem psiM_mul (l₁ l₂ : ↥L) :
    psiM α hker s hs β (l₁ * l₂) = psiM α hker s hs β l₁ * psiM α hker s hs β l₂ := by
  unfold psiM
  rw [affM_mul]
  congr 1
  · rw [map_mul]
    rfl
  · have hmem : (l₁ : G) * (nuV α hker s hs l₂ : G) * (l₁ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV l₁.2) _).mp (nuV α hker s hs l₂).2
    have hsplit : nuV α hker s hs (l₁ * l₂) =
        (⟨_, hmem⟩ : ↥V) * nuV α hker s hs l₁ :=
      Subtype.ext (by rw [nuV_mul α hker s hs l₁ l₂]; rfl)
    rw [hsplit, map_mul, toAdd_mul, hβeq l₁ (nuV α hker s hs l₂) _ rfl]

theorem psiM_one : psiM α hker s hs β 1 = 1 := by
  unfold psiM
  have hnu : nuV α hker s hs 1 = 1 := Subtype.ext (by simp [nuV])
  rw [hnu, map_one, map_one, toAdd_one]
  exact affM_one

@[expose] noncomputable def psiHom : ↥L →* GL (Fin (n + 1)) (ZMod 2) :=
  MonoidHom.toHomUnits
    { toFun := psiM α hker s hs β
      map_one' := psiM_one α hker s hs β
      map_mul' := psiM_mul hLV α hker s hs β hβeq }

theorem coe_psiHom (l : ↥L) :
    ((psiHom hLV α hker s hs β hβeq l : GL (Fin (n + 1)) (ZMod 2)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) = psiM α hker s hs β l :=
  rfl

include hβeq hLV in
theorem psiHom_injective (hβ : Function.Injective β) :
    Function.Injective (psiHom hLV α hker s hs β hβeq) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have hM : psiM α hker s hs β l = affM 1 0 := by
    rw [← coe_psiHom hLV α hker s hs β hβeq, hl, affM_one]
    rfl
  obtain ⟨hA, hb⟩ := affM_inj hM
  have hα : α l = 1 := Subtype.ext (Units.ext hA)
  have hν : nuV α hker s hs l = 1 :=
    hβ ((Multiplicative.toAdd.injective hb).trans (map_one β).symm)
  have := congrArg Subtype.val hν
  rw [coe_nuV, hα, map_one, inv_one, mul_one] at this
  exact Subtype.ext this

theorem psiM_of_mem (v : ↥V) (hvL : (v : G) ∈ L) :
    psiM α hker s hs β ⟨v, hvL⟩ = affM 1 (Multiplicative.toAdd (β v)) := by
  have hα : α ⟨v, hvL⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact v.2
  have hν : nuV α hker s hs ⟨v, hvL⟩ = v := Subtype.ext (by
    rw [coe_nuV, hα, map_one, inv_one, mul_one])
  unfold psiM
  rw [hν, hα]
  rfl

include hs in
theorem exists_psiM_eq (hβ : Function.Surjective β) (A : ↥(StatedSL n (ZMod 2)))
    (b : Fin n → ZMod 2) (hVL : V ≤ L) :
    ∃ l : ↥L, psiM α hker s hs β l = affM ((A : GL (Fin n) (ZMod 2)) : Matrix _ _ _) b := by
  obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd b)
  refine ⟨⟨v, hVL v.2⟩ * s A, ?_⟩
  have hα : α (⟨v, hVL v.2⟩ * s A) = A := by
    have h1 : α ⟨v, hVL v.2⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact v.2
    rw [map_mul, h1, one_mul, hs]
  have hν : nuV α hker s hs (⟨v, hVL v.2⟩ * s A) = v := Subtype.ext (by
    rw [coe_nuV, hα]
    simp)
  unfold psiM
  rw [hν, hα, hv, toAdd_ofAdd]

end Embedding

section Centralizers

variable [NeZero n] {G : Type*} [Group G] {L V : Subgroup G}
  (hLV : L ≤ Subgroup.normalizer (V : Set G))
  (α : ↥L →* ↥(StatedSL n (ZMod 2)))
  (hker : α.ker = V.subgroupOf L)
  (s : ↥(StatedSL n (ZMod 2)) →* ↥L) (hs : ∀ g, α (s g) = g)
  (β : ↥V →* Multiplicative (Fin n → ZMod 2))
  (hβeq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) =
      ((α ℓ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        (Multiplicative.toAdd (β u)))

theorem psiHom_eq_tGL (hVL : V ≤ L) (z : ↥V)
    (hz : β z = Multiplicative.ofAdd (Pi.single 0 1)) :
    psiHom hLV α hker s hs β hβeq ⟨z, hVL z.2⟩ = tGL n := by
  apply Units.ext
  rw [coe_psiHom, psiM_of_mem, hz, toAdd_ofAdd]
  rfl

theorem mem_centralizer_iff_psiHom (hVL : V ≤ L) (hβ : Function.Injective β) (z : ↥V)
    (hz : β z = Multiplicative.ofAdd (Pi.single 0 1)) (l : ↥L) :
    l ∈ Subgroup.centralizer ({⟨z, hVL z.2⟩} : Set ↥L) ↔
      psiHom hLV α hker s hs β hβeq l ∈
        Subgroup.centralizer ({tGL n} : Set (GL (Fin (n + 1)) (ZMod 2))) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← psiHom_eq_tGL hLV α hker s hs β hβeq hVL z hz, ← map_mul, ← map_mul]
  exact (psiHom_injective hLV α hker s hs β hβeq hβ).eq_iff.symm

include hs in
theorem exists_psiHom_eq_of_mem_centralizer (hVL : V ≤ L) (hβ : Function.Surjective β)
    {g : GL (Fin (n + 1)) (ZMod 2)}
    (hg : g ∈ Subgroup.centralizer ({tGL n} : Set (GL (Fin (n + 1)) (ZMod 2)))) :
    ∃ l : ↥L, psiHom hLV α hker s hs β hβeq l = g := by
  have hcomm : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) * tM n =
      tM n * (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) :=
    congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hdet0 : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  obtain ⟨hrow, hll⟩ := shape_of_commute _ hcomm hdet0
  obtain ⟨A, b, hshape⟩ : ∃ (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2),
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) = affM A b :=
    ⟨_, _, eq_affM_of_shape _ hrow hll⟩
  have hdet : A.det = 1 := by
    apply zmod_two_eq_one_of_ne_zero
    rw [← affM_det A b, ← hshape]
    exact hdet0
  have hne : A.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hAG : Matrix.GeneralLinearGroup.mkOfDetNeZero A hne ∈ StatedSL n (ZMod 2) :=
    Subgroup.subset_closure (show ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hne :
      GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 from hdet)
  obtain ⟨l, hl⟩ := exists_psiM_eq α hker s hs β hβ ⟨_, hAG⟩ b hVL
  refine ⟨l, Units.ext ?_⟩
  rw [coe_psiHom, hl, hshape]
  rfl

@[expose] noncomputable def centralizerEquivGL (hVL : V ≤ L) (hβ : Function.Bijective β) (z : ↥V)
    (hz : β z = Multiplicative.ofAdd (Pi.single 0 1)) :
    ↥(Subgroup.centralizer ({⟨z, hVL z.2⟩} : Set ↥L)) ≃*
      ↥(Subgroup.centralizer ({tGL n} : Set (GL (Fin (n + 1)) (ZMod 2)))) :=
  MulEquiv.ofBijective
    (((psiHom hLV α hker s hs β hβeq).comp
        (Subgroup.centralizer ({⟨z, hVL z.2⟩} : Set ↥L)).subtype).codRestrict
      (Subgroup.centralizer ({tGL n} : Set (GL (Fin (n + 1)) (ZMod 2)))) fun l =>
        (mem_centralizer_iff_psiHom hLV α hker s hs β hβeq hVL hβ.1 z hz l).mp l.2)
    ⟨fun a b hab => Subtype.ext ((psiHom_injective hLV α hker s hs β hβeq hβ.1)
        (congrArg Subtype.val hab)),
      fun g => by
        obtain ⟨l, hl⟩ :=
          exists_psiHom_eq_of_mem_centralizer hLV α hker s hs β hβeq hVL hβ.2 g.2
        refine ⟨⟨l, (mem_centralizer_iff_psiHom hLV α hker s hs β hβeq hVL hβ.1 z hz l).mpr
          (hl ▸ g.2)⟩, Subtype.ext hl⟩⟩

end Centralizers

end CFSG.Quasithin.H13.AffN
