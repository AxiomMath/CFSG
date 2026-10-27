module

public import CFSG.GroupTheory.GL52.InvolutionsTransvection
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.GroupTheory.GL52 (G52 M5 invT0 invT0M inv_t0_shape)

section Affine

@[expose] def affM (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (b : Fin 4 → ZMod 2) : M5 :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A (Matrix.of fun i (_ : Fin 1) => b i)
      (0 : Matrix (Fin 1) (Fin 4) (ZMod 2)) (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)))

theorem affM_mul (A A' : Matrix (Fin 4) (Fin 4) (ZMod 2)) (b b' : Fin 4 → ZMod 2) :
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

theorem affM_one : affM 1 0 = 1 := by
  unfold affM
  rw [Matrix.reindex_apply]
  have : (Matrix.fromBlocks (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
      (Matrix.of fun i (_ : Fin 1) => (0 : Fin 4 → ZMod 2) i)
      (0 : Matrix (Fin 1) (Fin 4) (ZMod 2)) (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))) = 1 := by
    rw [← Matrix.fromBlocks_one]
    congr 1
  rw [this]
  exact Matrix.submatrix_one_equiv _

theorem affM_det (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (b : Fin 4 → ZMod 2) :
    (affM A b).det = A.det := by
  unfold affM
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem affM_cc (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (b : Fin 4 → ZMod 2) (i j : Fin 4) :
    affM A b (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  simp only [affM, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.castSucc i) = Sum.inl i from
      finSumFinEquiv_symm_apply_castAdd i,
    show finSumFinEquiv.symm (Fin.castSucc j) = Sum.inl j from
      finSumFinEquiv_symm_apply_castAdd j]
  rfl

theorem affM_cl (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (b : Fin 4 → ZMod 2) (i : Fin 4) :
    affM A b (Fin.castSucc i) (Fin.last 4) = b i := by
  simp only [affM, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.castSucc i) = Sum.inl i from
      finSumFinEquiv_symm_apply_castAdd i,
    show finSumFinEquiv.symm (Fin.last 4) = Sum.inr 0 from finSumFinEquiv_symm_last]
  rfl

theorem affM_lc (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (b : Fin 4 → ZMod 2) (j : Fin 4) :
    affM A b (Fin.last 4) (Fin.castSucc j) = 0 := by
  simp only [affM, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.castSucc j) = Sum.inl j from
      finSumFinEquiv_symm_apply_castAdd j,
    show finSumFinEquiv.symm (Fin.last 4) = Sum.inr 0 from finSumFinEquiv_symm_last]
  rfl

theorem affM_ll (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (b : Fin 4 → ZMod 2) :
    affM A b (Fin.last 4) (Fin.last 4) = 1 := by
  simp only [affM, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.last 4) = Sum.inr 0 from finSumFinEquiv_symm_last]
  rfl

theorem affM_inj {A A' : Matrix (Fin 4) (Fin 4) (ZMod 2)} {b b' : Fin 4 → ZMod 2}
    (h : affM A b = affM A' b') : A = A' ∧ b = b' := by
  refine ⟨?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h (Fin.castSucc i)) (Fin.castSucc j)
    rwa [affM_cc, affM_cc] at this
  · funext i
    have := congrFun (congrFun h (Fin.castSucc i)) (Fin.last 4)
    rwa [affM_cl, affM_cl] at this

theorem eq_affM_of_shape (g : M5) (hrow : ∀ j : Fin 5, j ≠ 4 → g 4 j = 0) (h44 : g 4 4 = 1) :
    g = affM (fun i j => g (Fin.castSucc i) (Fin.castSucc j))
      (fun i => g (Fin.castSucc i) (Fin.last 4)) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h44.trans (affM_ll _ _).symm
    | cast j => exact (hrow _ (Fin.castSucc_ne_last j)).trans (affM_lc _ _ j).symm
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      exact (affM_cl (fun i j => g (Fin.castSucc i) (Fin.castSucc j))
        (fun i => g (Fin.castSucc i) (Fin.last 4)) i).symm
    | cast j =>
      exact (affM_cc (fun i j => g (Fin.castSucc i) (Fin.castSucc j))
        (fun i => g (Fin.castSucc i) (Fin.last 4)) i j).symm

theorem affM_one_single : affM 1 (Pi.single 0 1) = invT0M := by
  decide

theorem coe_transvection15 :
    ((transvection15 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : M5) = invT0M := by
  decide

theorem zmod_two_eq_one_of_ne_zero (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  revert x
  decide

end Affine

section Embedding

variable {G : Type*} [Group G] {L V : Subgroup G}
  (hLV : L ≤ Subgroup.normalizer (V : Set G))
  (α : ↥L →* ↥(StatedSL 4 (ZMod 2)))
  (hker : α.ker = V.subgroupOf L)
  (s : ↥(StatedSL 4 (ZMod 2)) →* ↥L) (hs : ∀ g, α (s g) = g)
  (β : ↥V →* Multiplicative (Fin 4 → ZMod 2))
  (hβeq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) =
      ((α ℓ : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
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

@[expose] noncomputable def psiM (l : ↥L) : M5 :=
  affM ((α l : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
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

@[expose] noncomputable def psiHom : ↥L →* GL (Fin 5) (ZMod 2) :=
  MonoidHom.toHomUnits
    { toFun := psiM α hker s hs β
      map_one' := psiM_one α hker s hs β
      map_mul' := psiM_mul hLV α hker s hs β hβeq }

theorem coe_psiHom (l : ↥L) :
    ((psiHom hLV α hker s hs β hβeq l : GL (Fin 5) (ZMod 2)) : M5) = psiM α hker s hs β l :=
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
theorem exists_psiM_eq (hβ : Function.Surjective β) (A : ↥(StatedSL 4 (ZMod 2)))
    (b : Fin 4 → ZMod 2) (hVL : V ≤ L) :
    ∃ l : ↥L, psiM α hker s hs β l = affM ((A : GL (Fin 4) (ZMod 2)) : Matrix _ _ _) b := by
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

variable {G : Type*} [Group G] {L V : Subgroup G}
  (hLV : L ≤ Subgroup.normalizer (V : Set G))
  (α : ↥L →* ↥(StatedSL 4 (ZMod 2)))
  (hker : α.ker = V.subgroupOf L)
  (s : ↥(StatedSL 4 (ZMod 2)) →* ↥L) (hs : ∀ g, α (s g) = g)
  (β : ↥V →* Multiplicative (Fin 4 → ZMod 2))
  (hβeq : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) =
      ((α ℓ : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        (Multiplicative.toAdd (β u)))

theorem psiHom_eq_invT0 (hVL : V ≤ L) (z : ↥V)
    (hz : β z = Multiplicative.ofAdd (Pi.single 0 1)) :
    psiHom hLV α hker s hs β hβeq ⟨z, hVL z.2⟩ = invT0 := by
  apply Units.ext
  rw [coe_psiHom, psiM_of_mem, hz, toAdd_ofAdd, affM_one_single]
  rfl

theorem mem_centralizer_iff_psiHom (hVL : V ≤ L) (hβ : Function.Injective β) (z : ↥V)
    (hz : β z = Multiplicative.ofAdd (Pi.single 0 1)) (l : ↥L) :
    l ∈ Subgroup.centralizer ({⟨z, hVL z.2⟩} : Set ↥L) ↔
      psiHom hLV α hker s hs β hβeq l ∈ Subgroup.centralizer ({invT0} : Set G52) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← psiHom_eq_invT0 hLV α hker s hs β hβeq hVL z hz, ← map_mul, ← map_mul]
  exact (psiHom_injective hLV α hker s hs β hβeq hβ).eq_iff.symm

include hs in
theorem exists_psiHom_eq_of_mem_centralizer (hVL : V ≤ L) (hβ : Function.Surjective β)
    {g : G52} (hg : g ∈ Subgroup.centralizer ({invT0} : Set G52)) :
    ∃ l : ↥L, psiHom hLV α hker s hs β hβeq l = g := by
  obtain ⟨-, hrow, -, h44⟩ := inv_t0_shape hg
  obtain ⟨A, b, hshape⟩ : ∃ (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (b : Fin 4 → ZMod 2),
      (g : M5) = affM A b := ⟨_, _, eq_affM_of_shape (g : M5) hrow h44⟩
  have hdet : A.det = 1 := by
    apply zmod_two_eq_one_of_ne_zero
    rw [← affM_det A b, ← hshape]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hne : A.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hAG : Matrix.GeneralLinearGroup.mkOfDetNeZero A hne ∈ StatedSL 4 (ZMod 2) :=
    Subgroup.subset_closure (show ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hne :
      GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).det = 1 from hdet)
  obtain ⟨l, hl⟩ := exists_psiM_eq α hker s hs β hβ ⟨_, hAG⟩ b hVL
  refine ⟨l, Units.ext ?_⟩
  rw [coe_psiHom, hl, hshape]
  rfl

noncomputable def centralizerEquivGL (hVL : V ≤ L) (hβ : Function.Bijective β) (z : ↥V)
    (hz : β z = Multiplicative.ofAdd (Pi.single 0 1)) :
    ↥(Subgroup.centralizer ({⟨z, hVL z.2⟩} : Set ↥L)) ≃*
      ↥(Subgroup.centralizer ({invT0} : Set G52)) :=
  MulEquiv.ofBijective
    (((psiHom hLV α hker s hs β hβeq).comp
        (Subgroup.centralizer ({⟨z, hVL z.2⟩} : Set ↥L)).subtype).codRestrict
      (Subgroup.centralizer ({invT0} : Set G52)) fun l =>
        (mem_centralizer_iff_psiHom hLV α hker s hs β hβeq hVL hβ.1 z hz l).mp l.2)
    ⟨fun a b hab => Subtype.ext ((psiHom_injective hLV α hker s hs β hβeq hβ.1)
        (congrArg Subtype.val hab)),
      fun g => by
        obtain ⟨l, hl⟩ :=
          exists_psiHom_eq_of_mem_centralizer hLV α hker s hs β hβeq hVL hβ.2 g.2
        refine ⟨⟨l, (mem_centralizer_iff_psiHom hLV α hker s hs β hβeq hVL hβ.1 z hz l).mpr
          (hl ▸ g.2)⟩, Subtype.ext hl⟩⟩

end Centralizers

noncomputable def centralizerTransvectionEquiv :
    ↥(Subgroup.centralizer
        ({transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))) ≃*
      ↥(Subgroup.centralizer ({invT0} : Set G52)) := by
  have htoGL : Matrix.SpecialLinearGroup.toGL transvection15 = invT0 :=
    Units.ext (by rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_transvection15]; rfl)
  have hinj : Function.Injective
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) →* G52) :=
    fun a b h => Subtype.ext (by
      have := congrArg (fun x : G52 => (x : M5)) h
      simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using this)
  have hmem : ∀ x : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
      x ∈ Subgroup.centralizer ({transvection15} : Set _) ↔
        Matrix.SpecialLinearGroup.toGL x ∈ Subgroup.centralizer ({invT0} : Set G52) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← htoGL,
      ← map_mul, ← map_mul]
    exact hinj.eq_iff.symm
  exact MulEquiv.ofBijective
    ((Matrix.SpecialLinearGroup.toGL.comp
        (Subgroup.centralizer ({transvection15} : Set _)).subtype).codRestrict
      (Subgroup.centralizer ({invT0} : Set G52)) fun x => (hmem x).mp x.2)
    ⟨fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab)), fun g => by
      have hdet : ((g : G52) : M5).det = 1 := zmod_two_eq_one_of_ne_zero _
        ((Matrix.isUnit_iff_isUnit_det _).mp (g : G52).isUnit).ne_zero
      have hto : Matrix.SpecialLinearGroup.toGL ⟨((g : G52) : M5), hdet⟩ = (g : G52) :=
        Units.ext (Matrix.SpecialLinearGroup.coe_GL_coe_matrix _)
      exact ⟨⟨⟨((g : G52) : M5), hdet⟩, (hmem _).mpr (by rw [hto]; exact g.2)⟩,
        Subtype.ext hto⟩⟩

end CFSG.Quasithin.H13
