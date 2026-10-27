module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksDefs
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksBasic
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIdem
import CFSG.LocalAnalysis.StandardType.GGTorCPlane
import CFSG.GroupTheory.F4ModuleFromOperator
import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K]

private def fromBlocksOneHom {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (K : Type) [Field K] : Matrix α α K →* Matrix (α ⊕ β) (α ⊕ β) K where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := by rw [Matrix.fromBlocks_one]
  map_mul' A B := by
    rw [Matrix.fromBlocks_multiply]
    simp

private theorem one_sub_fromBlocks_one_zero {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {K : Type} [Field K] :
    (1 : Matrix (α ⊕ β) (α ⊕ β) K) -
        Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K) =
      Matrix.fromBlocks 0 0 0 (1 : Matrix β β K) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

private theorem fromBlocksOneHom_mem_levi {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {K : Type} [Field K] (A : GL α K) :
    (Units.map (fromBlocksOneHom (α := α) (β := β) K) A : GL (α ⊕ β) K) ∈
      levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K)) := by
  constructor
  · change (Matrix.fromBlocks (A : Matrix α α K) 0 0 1) *
        (1 - Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K)) =
      1 - Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K)
    rw [one_sub_fromBlocks_one_zero, Matrix.fromBlocks_multiply]
    simp
  · change (1 - Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K)) *
        (Matrix.fromBlocks (A : Matrix α α K) 0 0 1) =
      1 - Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K)
    rw [one_sub_fromBlocks_one_zero, Matrix.fromBlocks_multiply]
    simp

private def fromBlocksOneHomUnits {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (K : Type) [Field K] :
    GL α K →* ↥(levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K))) where
  toFun A := ⟨Units.map (fromBlocksOneHom (α := α) (β := β) K) A,
    fromBlocksOneHom_mem_levi A⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Units.map (fromBlocksOneHom (α := α) (β := β) K))
  map_mul' A B := by
    apply Subtype.ext
    exact map_mul (Units.map (fromBlocksOneHom (α := α) (β := β) K)) A B

private theorem fromBlocks_toBlocks_of_mem_levi {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {K : Type} [Field K] {g : GL (α ⊕ β) K}
    (hg : g ∈ levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K))) :
    (g : Matrix (α ⊕ β) (α ⊕ β) K) =
      Matrix.fromBlocks (Matrix.toBlocks₁₁ (g : Matrix (α ⊕ β) (α ⊕ β) K)) 0 0 1 := by
  have h1 := hg.1
  have h2 := hg.2
  rw [one_sub_fromBlocks_one_zero] at h1 h2
  ext x y
  rcases x with i | i <;> rcases y with j | j
  · rfl
  · have h := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.fromBlocks_apply₁₂, Matrix.mul_apply, Matrix.one_apply] using h
  · have h := congrFun (congrFun h2 (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.fromBlocks_apply₂₁, Matrix.mul_apply, Matrix.one_apply] using h
  · have h := congrFun (congrFun h1 (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.fromBlocks_apply₂₂, Matrix.mul_apply, Matrix.one_apply] using h

private noncomputable def leviBlockUnit {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (K : Type) [Field K]
    (g : ↥(levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K)))) :
    GL α K :=
  let ginv : GL (α ⊕ β) K := (g : GL (α ⊕ β) K)⁻¹
  { val := Matrix.toBlocks₁₁ (((g : GL (α ⊕ β) K)) : Matrix (α ⊕ β) (α ⊕ β) K)
    inv := Matrix.toBlocks₁₁ ((ginv : GL (α ⊕ β) K) : Matrix (α ⊕ β) (α ⊕ β) K)
    val_inv := by
      have hmem : ginv ∈
          levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K)) := by
        change ((g⁻¹ : ↥(levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0
          (0 : Matrix β β K)))) : GL (α ⊕ β) K) ∈
          levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K))
        exact (levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0
          (0 : Matrix β β K))).inv_mem g.2
      have hgblk := fromBlocks_toBlocks_of_mem_levi (α := α) (β := β) (K := K) g.2
      have hinvblk := fromBlocks_toBlocks_of_mem_levi (α := α) (β := β) (K := K) hmem
      have hmul : (((g : GL (α ⊕ β) K)) : Matrix (α ⊕ β) (α ⊕ β) K) *
          ((ginv : GL (α ⊕ β) K) : Matrix (α ⊕ β) (α ⊕ β) K) = 1 := by
        have h := congrArg (fun u : GL (α ⊕ β) K => (u : Matrix (α ⊕ β) (α ⊕ β) K))
          (mul_inv_cancel (g : GL (α ⊕ β) K))
        rw [Units.val_mul, Units.val_one] at h
        exact h
      rw [hgblk, hinvblk, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hmul
      simp only [zero_add, add_zero, mul_one, Matrix.mul_zero,
        Matrix.zero_mul, Matrix.mul_one] at hmul
      exact (Matrix.fromBlocks_inj.mp hmul).1
    inv_val := by
      have hmem : ginv ∈
          levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K)) := by
        change ((g⁻¹ : ↥(levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0
          (0 : Matrix β β K)))) : GL (α ⊕ β) K) ∈
          levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K))
        exact (levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0
          (0 : Matrix β β K))).inv_mem g.2
      have hgblk := fromBlocks_toBlocks_of_mem_levi (α := α) (β := β) (K := K) g.2
      have hinvblk := fromBlocks_toBlocks_of_mem_levi (α := α) (β := β) (K := K) hmem
      have hmul : ((ginv : GL (α ⊕ β) K) : Matrix (α ⊕ β) (α ⊕ β) K) *
          (((g : GL (α ⊕ β) K)) : Matrix (α ⊕ β) (α ⊕ β) K) = 1 := by
        have h := congrArg (fun u : GL (α ⊕ β) K => (u : Matrix (α ⊕ β) (α ⊕ β) K))
          (inv_mul_cancel (g : GL (α ⊕ β) K))
        rw [Units.val_mul, Units.val_one] at h
        exact h
      rw [hgblk, hinvblk, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hmul
      simp only [zero_add, add_zero, mul_one, Matrix.mul_zero,
        Matrix.zero_mul, Matrix.mul_one] at hmul
      exact (Matrix.fromBlocks_inj.mp hmul).1 }

private theorem fromBlocksOneHomUnits_bijective {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (K : Type) [Field K] :
    Function.Bijective (fromBlocksOneHomUnits (α := α) (β := β) K) := by
  constructor
  · intro A B h
    apply Units.ext
    have h' := congrArg (fun x : ↥(levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0
      (0 : Matrix β β K))) => (((x : GL (α ⊕ β) K)) : Matrix (α ⊕ β) (α ⊕ β) K)) h
    change Matrix.fromBlocks (A : Matrix α α K) 0 0 1 =
      Matrix.fromBlocks (B : Matrix α α K) 0 0 1 at h'
    exact (Matrix.fromBlocks_inj.mp h').1
  · intro g
    refine ⟨leviBlockUnit K g, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change Matrix.fromBlocks
        (Matrix.toBlocks₁₁ (((g : GL (α ⊕ β) K)) : Matrix (α ⊕ β) (α ⊕ β) K)) 0 0 1 =
      (((g : GL (α ⊕ β) K)) : Matrix (α ⊕ β) (α ⊕ β) K)
    exact (fromBlocks_toBlocks_of_mem_levi (α := α) (β := β) (K := K) g.2).symm

private noncomputable def leviFromBlocksEquiv {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (K : Type) [Field K] :
    ↥(levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K))) ≃* GL α K :=
  (MulEquiv.ofBijective (fromBlocksOneHomUnits (α := α) (β := β) K)
    (fromBlocksOneHomUnits_bijective (α := α) (β := β) K)).symm

private theorem leviFromBlocksEquiv_apply_coe {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (K : Type) [Field K]
    (g : ↥(levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0 (0 : Matrix β β K)))) :
    ((leviFromBlocksEquiv (α := α) (β := β) K g : GL α K) : Matrix α α K) =
      Matrix.toBlocks₁₁ (((g : GL (α ⊕ β) K)) : Matrix (α ⊕ β) (α ⊕ β) K) := by
  have h : fromBlocksOneHomUnits (α := α) (β := β) K
      ((leviFromBlocksEquiv (α := α) (β := β) K) g) = g := by
    change (leviFromBlocksEquiv (α := α) (β := β) K).symm
      ((leviFromBlocksEquiv (α := α) (β := β) K) g) = g
    exact (leviFromBlocksEquiv (α := α) (β := β) K).symm_apply_apply g
  have hm := congrArg (fun x : ↥(levi (Matrix.fromBlocks (1 : Matrix α α K) 0 0
    (0 : Matrix β β K))) => (((x : GL (α ⊕ β) K)) : Matrix (α ⊕ β) (α ⊕ β) K)) h
  change Matrix.fromBlocks (((leviFromBlocksEquiv (α := α) (β := β) K) g :
      GL α K) : Matrix α α K) 0 0 1 =
    (((g : GL (α ⊕ β) K)) : Matrix (α ⊕ β) (α ⊕ β) K) at hm
  have := congrArg Matrix.toBlocks₁₁ hm
  simpa [Matrix.toBlocks_fromBlocks₁₁] using this

private noncomputable abbrev diagSupportEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → K) [DecidablePred fun i => f i = 1] :
    {i // f i = 1} ⊕ {i // ¬ f i = 1} ≃ ι :=
  Equiv.sumCompl (fun i => f i = 1)

private theorem reindex_diagonal_eq_fromBlocks {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → K) [DecidablePred fun i => f i = 1] (hf : ∀ i, f i = 0 ∨ f i = 1) :
    Matrix.reindex (diagSupportEquiv (K := K) f).symm (diagSupportEquiv (K := K) f).symm
        (Matrix.diagonal f) =
      Matrix.fromBlocks (1 : Matrix {i // f i = 1} {i // f i = 1} K) 0 0
        (0 : Matrix {i // ¬ f i = 1} {i // ¬ f i = 1} K) := by
  classical
  let e := diagSupportEquiv (K := K) f
  ext x y
  rcases x with a | a <;> rcases y with b | b
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inl, Matrix.diagonal_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp [a.2]
    · have hne : (a.1 : ι) ≠ b.1 := fun h => hab (Subtype.ext h)
      simp [Subtype.ext_iff, hne]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, Matrix.diagonal_apply, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply]
    have hne : (a.1 : ι) ≠ b.1 := by
      intro h
      have ha : f a.1 = 1 := a.2
      have hb : ¬ f b.1 = 1 := b.2
      exact hb (h ▸ ha)
    simp [hne]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inr,
      Equiv.sumCompl_apply_inl, Matrix.diagonal_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
    have hne : (a.1 : ι) ≠ b.1 := by
      intro h
      have ha : ¬ f a.1 = 1 := a.2
      have hb : f b.1 = 1 := b.2
      exact ha (h ▸ hb)
    simp [hne]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inr,
      Equiv.sumCompl_apply_inr, Matrix.diagonal_apply, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply]
    have hfa : f a.1 = 0 := by
      rcases hf a.1 with h | h
      · exact h
      · exact absurd h a.2
    by_cases hab : a = b
    · subst hab; simp [hfa]
    · have hne : (a.1 : ι) ≠ b.1 := fun h => hab (Subtype.ext h)
      simp [hne]

private noncomputable def leviDiagonalEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → K) [DecidablePred fun i => f i = 1] (hf : ∀ i, f i = 0 ∨ f i = 1) :
    ↥(levi (Matrix.diagonal f)) ≃* GL {i // f i = 1} K := by
  classical
  let e := diagSupportEquiv (K := K) f
  let Φ : Matrix ({i // f i = 1} ⊕ {i // ¬ f i = 1})
      ({i // f i = 1} ⊕ {i // ¬ f i = 1}) K ≃+*
      Matrix ι ι K := Matrix.reindexAlgEquiv K K e
  let F : Matrix ({i // f i = 1} ⊕ {i // ¬ f i = 1})
      ({i // f i = 1} ⊕ {i // ¬ f i = 1}) K :=
    Matrix.fromBlocks (1 : Matrix {i // f i = 1} {i // f i = 1} K) 0 0
      (0 : Matrix {i // ¬ f i = 1} {i // ¬ f i = 1} K)
  have hF : Φ.symm (Matrix.diagonal f) = F := reindex_diagonal_eq_fromBlocks f hf
  have hF' : Φ F = Matrix.diagonal f := by
    rw [← hF]
    exact Φ.apply_symm_apply (Matrix.diagonal f)
  let φ : GL ({i // f i = 1} ⊕ {i // ¬ f i = 1}) K ≃* GL ι K :=
    Units.mapEquiv Φ.toMulEquiv
  have hφg (g : GL ({i // f i = 1} ⊕ {i // ¬ f i = 1}) K) :
      (((φ g : GL ι K)) : Matrix ι ι K) = Φ (g : Matrix _ _ K) := by
    change ((Units.mapEquiv Φ.toMulEquiv g : GL ι K) : Matrix ι ι K) = Φ (g : Matrix _ _ K)
    rw [Units.coe_mapEquiv]
    rfl
  have hmap : (levi (Matrix.diagonal f)).map φ.symm.toMonoidHom =
      levi (Matrix.fromBlocks (1 : Matrix {i // f i = 1} {i // f i = 1} K) 0 0
        (0 : Matrix {i // ¬ f i = 1} {i // ¬ f i = 1} K)) := by
    ext g
    rw [Subgroup.mem_map_equiv]
    simp only [MulEquiv.symm_symm]
    constructor
    · intro h
      have hsym : Φ.symm (((φ g : GL ι K)) : Matrix ι ι K) = (g : Matrix _ _ K) := by
        rw [hφg]
        exact Φ.symm_apply_apply (g : Matrix _ _ K)
      constructor
      · have hh := congrArg Φ.symm h.1
        simp only [map_mul, map_sub, map_one] at hh
        rw [hsym] at hh
        rw [hF] at hh
        exact hh
      · have hh := congrArg Φ.symm h.2
        simp only [map_mul, map_sub, map_one] at hh
        rw [hsym] at hh
        rw [hF] at hh
        exact hh
    · intro h
      constructor
      · have hh := congrArg Φ h.1
        simp only [map_mul, map_sub, map_one] at hh
        rw [hF'] at hh
        rw [hφg]
        exact hh
      · have hh := congrArg Φ h.2
        simp only [map_mul, map_sub, map_one] at hh
        rw [hF'] at hh
        rw [hφg]
        exact hh
  let mid := ↥(Subgroup.map φ.symm.toMonoidHom (levi (Matrix.diagonal f)))
  have e₂ : ↥(levi (Matrix.diagonal f)) ≃* mid :=
    Subgroup.equivMapOfInjective (levi (Matrix.diagonal f)) φ.symm.toMonoidHom
      φ.symm.injective
  have e₃ : mid ≃* ↥(levi (Matrix.fromBlocks
      (1 : Matrix {i // f i = 1} {i // f i = 1} K) 0 0
      (0 : Matrix {i // ¬ f i = 1} {i // ¬ f i = 1} K))) :=
    MulEquiv.subgroupCongr hmap
  have hlast : ↥(levi (Matrix.fromBlocks
      (1 : Matrix {i // f i = 1} {i // f i = 1} K) 0 0
      (0 : Matrix {i // ¬ f i = 1} {i // ¬ f i = 1} K))) ≃* GL {i // f i = 1} K :=
    leviFromBlocksEquiv (α := {i // f i = 1}) (β := {i // ¬ f i = 1}) K
  exact (e₂.trans e₃).trans hlast

private theorem leviDiagonalEquiv_coe {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → K) [DecidablePred fun i => f i = 1] (hf : ∀ i, f i = 0 ∨ f i = 1)
    (g : ↥(levi (Matrix.diagonal f))) :
    ((leviDiagonalEquiv f hf g : GL {i // f i = 1} K) :
      Matrix {i // f i = 1} {i // f i = 1} K) =
      Matrix.toBlocks₁₁ (Matrix.reindex (diagSupportEquiv f).symm (diagSupportEquiv f).symm
        ((g : GL ι K) : Matrix ι ι K)) := by
  let e := diagSupportEquiv (K := K) f
  let φ : GL ({i // f i = 1} ⊕ {i // ¬ f i = 1}) K ≃* GL ι K :=
    Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv
  simp only [leviDiagonalEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    leviFromBlocksEquiv_apply_coe]
  change Matrix.toBlocks₁₁ (((φ.symm (g : GL ι K) : GL ({i // f i = 1} ⊕
      {i // ¬ f i = 1}) K)) : Matrix ({i // f i = 1} ⊕ {i // ¬ f i = 1})
        ({i // f i = 1} ⊕ {i // ¬ f i = 1}) K) =
    Matrix.toBlocks₁₁ (Matrix.reindex e.symm e.symm ((g : GL ι K) : Matrix ι ι K))
  change (Matrix.reindex e.symm e.symm ((g : GL ι K) : Matrix ι ι K)).toBlocks₁₁ =
    (Matrix.reindex e.symm e.symm ((g : GL ι K) : Matrix ι ι K)).toBlocks₁₁
  rfl

private theorem levi_diagonal_mulEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → K) [DecidablePred fun i => f i = 1] (hf : ∀ i, f i = 0 ∨ f i = 1) :
    Nonempty (↥(levi (Matrix.diagonal f)) ≃* GL {i // f i = 1} K) :=
  ⟨leviDiagonalEquiv f hf⟩

private theorem mem_of_planeIdem_plane_eq_one {t : ℕ} (ε : Fin 2) (S : Finset (Fin t))
    {i : Fin t}
    (h : planeIdem (K := K) t ε S true (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl i)) = 1) :
    i ∈ S := by
  by_contra hS
  simp [planeIdem, hS] at h

private theorem mem_of_planeIdem_plane_eq_one' {t : ℕ} (ε : Fin 2) (S : Finset (Fin t))
    {i : Fin t}
    (h : planeIdem (K := K) t ε S true (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inr i)) = 1) :
    i ∈ S := by
  by_contra hS
  simp [planeIdem, hS] at h

private noncomputable def planeSupportToFun (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    {x : LinIdx t ε // planeIdem (K := K) t ε S true x x = 1} → (S ⊕ S) ⊕ Fin ε.val
  | ⟨Sum.inl (Sum.inl i), hx⟩ =>
      Sum.inl (Sum.inl ⟨i, mem_of_planeIdem_plane_eq_one (K := K) ε S hx⟩)
  | ⟨Sum.inl (Sum.inr i), hx⟩ =>
      Sum.inl (Sum.inr ⟨i, mem_of_planeIdem_plane_eq_one' (K := K) ε S hx⟩)
  | ⟨Sum.inr j, _⟩ => Sum.inr j

private noncomputable def planeSupportInvFun (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    (S ⊕ S) ⊕ Fin ε.val → {x : LinIdx t ε // planeIdem (K := K) t ε S true x x = 1}
  | Sum.inl (Sum.inl i) => ⟨Sum.inl (Sum.inl i.1), by simp [planeIdem, i.2]⟩
  | Sum.inl (Sum.inr i) => ⟨Sum.inl (Sum.inr i.1), by simp [planeIdem, i.2]⟩
  | Sum.inr j => ⟨Sum.inr j, by simp [planeIdem]⟩

private noncomputable def planeSupportEquiv (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    {x : LinIdx t ε // planeIdem (K := K) t ε S true x x = 1} ≃ (S ⊕ S) ⊕ Fin ε.val where
  toFun := planeSupportToFun (K := K) t ε S
  invFun := planeSupportInvFun (K := K) t ε S
  left_inv := by
    rintro ⟨(i | i) | j, hx⟩ <;> rfl
  right_inv := by
    rintro ((i | i) | j) <;> rfl

private theorem card_planeIdem_support (t : ℕ) (ε : Fin 2) (S : Finset (Fin t))
    [DecidablePred fun x : LinIdx t ε => planeIdem (K := K) t ε S true x x = 1] :
    Fintype.card {x : LinIdx t ε // planeIdem (K := K) t ε S true x x = 1} =
      2 * S.card + ε.val := by
  rw [Fintype.card_congr (planeSupportEquiv (K := K) t ε S)]
  simp [Fintype.card_sum, two_mul, Nat.add_assoc]

variable (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)

private theorem planeIdem_false_eq_fromBlocks (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    (planeIdem (K := K) t ε S false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem (K := K) t S) 0 0 0 := by
  classical
  ext x y
  rcases x with (i | i) | j <;> rcases y with (k | k) | l <;>
    simp [planeIdem, CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.diagonal_apply]

theorem nonempty_blockGroup_zero_mulEquiv (S : Finset (Fin t)) :
    Nonempty (↥(blockGroup ζ t ε (PlaneRaw.Code.zero S)) ≃* GL (Fin (2 * S.card + ε.val)) K) := by
  classical
  have hf : ∀ x : LinIdx t ε,
      (planeIdem (K := K) t ε S true x x) = 0 ∨ (planeIdem (K := K) t ε S true x x) = 1 := by
    intro x
    rcases x with (i | i) | j
    · by_cases h : i ∈ S <;> simp [planeIdem, h]
    · by_cases h : i ∈ S <;> simp [planeIdem, h]
    · simp [planeIdem]
  have hdiag : Matrix.diagonal (fun x : LinIdx t ε => planeIdem (K := K) t ε S true x x) =
      planeIdem (K := K) t ε S true := by
    ext x y
    by_cases hxy : x = y <;> simp [planeIdem, hxy]
  obtain ⟨e₁⟩ := levi_diagonal_mulEquiv (K := K)
    (fun x : LinIdx t ε => planeIdem (K := K) t ε S true x x) hf
  rw [hdiag] at e₁
  let eT : {x : LinIdx t ε // planeIdem (K := K) t ε S true x x = 1} ≃
      Fin (2 * S.card + ε.val) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_planeIdem_support t ε S])
  let φ : GL {x : LinIdx t ε // planeIdem (K := K) t ε S true x x = 1} K ≃*
      GL (Fin (2 * S.card + ε.val)) K :=
    Units.mapEquiv (Matrix.reindexAlgEquiv K K eT).toMulEquiv
  exact ⟨e₁.trans φ⟩

private theorem reindex_diagonal_fixes_complement {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → K) [DecidablePred fun i => f i = 1] (hf : ∀ i, f i = 0 ∨ f i = 1)
    {Tau : Matrix ι ι K}
    (h1 : Tau * (1 - Matrix.diagonal f) = 1 - Matrix.diagonal f)
    (h2 : (1 - Matrix.diagonal f) * Tau = 1 - Matrix.diagonal f) :
    Matrix.reindex (diagSupportEquiv f).symm (diagSupportEquiv f).symm Tau =
      Matrix.fromBlocks (Matrix.toBlocks₁₁ (Matrix.reindex (diagSupportEquiv f).symm
        (diagSupportEquiv f).symm Tau)) 0 0
        (1 : Matrix {i // ¬ f i = 1} {i // ¬ f i = 1} K) := by
  classical
  let e := diagSupportEquiv (K := K) f
  let g : ι → K := fun i => 1 - f i
  have hdiag : (1 : Matrix ι ι K) - Matrix.diagonal f = Matrix.diagonal g := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
  have hgT (a : {i // f i = 1}) : g (e (Sum.inl a)) = 0 := by
    rw [Equiv.sumCompl_apply_inl, show g a.1 = 0 from by simp [g, a.2]]
  have hgU (b : {i // ¬ f i = 1}) : g (e (Sum.inr b)) = 1 := by
    have hfb : f b.1 = 0 := by
      rcases hf b.1 with h | h
      · exact h
      · exact absurd h b.2
    rw [Equiv.sumCompl_apply_inr]
    simp [g, hfb]
  have hgT' (a : {i // f i = 1}) : g a.1 = 0 := by
    have h := hgT a
    rw [Equiv.sumCompl_apply_inl] at h
    exact h
  have hgU' (b : {i // ¬ f i = 1}) : g b.1 = 1 := by
    have h := hgU b
    rw [Equiv.sumCompl_apply_inr] at h
    exact h
  have hne (a : {i // f i = 1}) (b : {i // ¬ f i = 1}) :
      e (Sum.inl a) ≠ e (Sum.inr b) := by
    intro h
    have := congrArg e.symm h
    simp at this
  have hTU (a : {i // f i = 1}) (b : {i // ¬ f i = 1}) : a.1 ≠ b.1 := by
    intro h
    exact b.2 (h ▸ a.2)
  ext x y
  rcases x with a | a <;> rcases y with b | b
  · rfl
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply]
    have h1' := h1
    rw [hdiag] at h1'
    have h := congrFun (congrFun h1' (e (Sum.inl a))) (e (Sum.inr b))
    rw [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, Matrix.mul_diagonal,
      hgU' b, mul_one, Matrix.diagonal_apply, if_neg (hTU a b)] at h
    exact h
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
    have h2' := h2
    rw [hdiag] at h2'
    have h := congrFun (congrFun h2' (e (Sum.inr a))) (e (Sum.inl b))
    rw [Equiv.sumCompl_apply_inr, Equiv.sumCompl_apply_inl, Matrix.diagonal_mul,
      hgU' a, one_mul, Matrix.diagonal_apply, if_neg] at h
    · exact h
    · intro hEq
      exact hTU b a hEq.symm
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.fromBlocks_apply₂₂,
      Matrix.one_apply]
    have h1' := h1
    rw [hdiag] at h1'
    have h := congrFun (congrFun h1' (e (Sum.inr a))) (e (Sum.inr b))
    rw [Equiv.sumCompl_apply_inr, Equiv.sumCompl_apply_inr, Matrix.mul_diagonal,
      hgU' b, mul_one] at h
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply, if_pos rfl, hgU' a] at h
      simpa using h
    · have hne' : a.1 ≠ b.1 := fun hh => hab (Subtype.ext hh)
      rw [Matrix.diagonal_apply, if_neg hne'] at h
      simpa [hab] using h

private theorem mem_of_planeIdem_false_plane_eq_one {t : ℕ} (ε : Fin 2)
    (S : Finset (Fin t)) {i : Fin t}
    (h : planeIdem (K := K) t ε S false (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl i)) = 1) :
    i ∈ S := by
  by_contra hS
  simp [planeIdem, hS] at h

private theorem mem_of_planeIdem_false_plane_eq_one' {t : ℕ} (ε : Fin 2)
    (S : Finset (Fin t)) {i : Fin t}
    (h : planeIdem (K := K) t ε S false (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inr i)) = 1) :
    i ∈ S := by
  by_contra hS
  simp [planeIdem, hS] at h

private noncomputable def planeSupportEquivFalse (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    {x : LinIdx t ε // planeIdem (K := K) t ε S false x x = 1} ≃ S ⊕ S where
  toFun x := by
    rcases x with ⟨(i | i) | j, hx⟩
    · exact Sum.inl ⟨i, mem_of_planeIdem_false_plane_eq_one ε S hx⟩
    · exact Sum.inr ⟨i, mem_of_planeIdem_false_plane_eq_one' ε S hx⟩
    · exfalso
      simp [planeIdem] at hx
  invFun x := by
    rcases x with i | i
    · exact ⟨Sum.inl (Sum.inl i.1), by simp [planeIdem, i.2]⟩
    · exact ⟨Sum.inl (Sum.inr i.1), by simp [planeIdem, i.2]⟩
  left_inv x := by
    rcases x with ⟨(i | i) | j, hx⟩
    · rfl
    · rfl
    · exfalso
      simp [planeIdem] at hx
  right_inv x := by
    rcases x with i | i <;> rfl

private theorem card_planeIdem_support_false (t : ℕ) (ε : Fin 2) (S : Finset (Fin t))
    [DecidablePred fun x : LinIdx t ε => planeIdem (K := K) t ε S false x x = 1] :
    Fintype.card {x : LinIdx t ε // planeIdem (K := K) t ε S false x x = 1} =
      2 * S.card := by
  rw [Fintype.card_congr (planeSupportEquivFalse t ε S)]
  simp [Fintype.card_sum, two_mul]

private theorem one_sub_planeIdem_false (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    (1 : Matrix (LinIdx t ε) (LinIdx t ε) K) - planeIdem (K := K) t ε S false =
      Matrix.fromBlocks (1 - CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem (K := K) t S)
        0 0 1 := by
  rw [planeIdem_false_eq_fromBlocks]
  ext x y
  rcases x with (i | i) | j <;> rcases y with (k | k) | l <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.one_apply]

private theorem one_sub_planeIdem_planes (t : ℕ) (S : Finset (Fin t)) :
    (1 : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) -
        CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem (K := K) t S =
      WitSpNs.planeMat (fun j => if j ∈ S then (0 : Matrix (Fin 2) (Fin 2) K) else 1) := by
  rw [CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem_eq_planeMat]
  ext a b
  rw [Matrix.sub_apply, Matrix.one_apply, WitSpNs.planeMat_apply]
  rcases a with i | i <;> rcases b with j | j <;>
    by_cases hij : i = j <;> by_cases hj : j ∈ S <;>
    simp [hij, hj, Matrix.one_apply, WitSpNs.planeMat_apply]

private theorem tau_mem_levi_ext (t : ℕ) (ε : Fin 2) (S : Finset (Fin t))
    (e : PlaneRaw.V t) (hS : S = PlaneRaw.Code.extSupport e) :
    tau ζ t ε e ∈ levi (planeIdem (K := K) t ε S false) := by
  classical
  let M : Fin t → Matrix (Fin 2) (Fin 2) K := fun j =>
    ((ζ (Multiplicative.ofAdd (e j)) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)
  have hM : ∀ j, j ∉ S → M j = 1 := by
    intro j hj
    have hej : e j = 0 := by
      by_contra hne
      exact hj (by rw [hS]; exact (PlaneRaw.mem_extSupport e j).mpr hne)
    simp [M, hej]
  have hmul : WitSpNs.planeMat M * (1 - CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem
      (K := K) t S) = 1 - CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem (K := K) t S := by
    rw [one_sub_planeIdem_planes, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · simp [hj]
    · rw [hM j hj]
      simp [hj]
  have hmul' : (1 - CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem (K := K) t S) *
      WitSpNs.planeMat M = 1 - CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem (K := K) t S := by
    rw [one_sub_planeIdem_planes, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · simp [hj]
    · rw [hM j hj]
      simp [hj]
  constructor
  · rw [coe_tau_eq_fromBlocks_planeMat, one_sub_planeIdem_false, Matrix.fromBlocks_multiply,
      hmul]
    simp
  · rw [coe_tau_eq_fromBlocks_planeMat, one_sub_planeIdem_false, Matrix.fromBlocks_multiply,
      hmul']
    simp

private theorem tau_sq_add_ext [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (t : ℕ) (ε : Fin 2) {e : PlaneRaw.V t} (_he : e ≠ 0) :
    ((tau ζ t ε e : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        ((tau ζ t ε e : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) +
      ((tau ζ t ε e : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      planeIdem (K := K) t ε (PlaneRaw.Code.extSupport e) false := by
  classical
  let S := PlaneRaw.Code.extSupport e
  let M : Fin t → Matrix (Fin 2) (Fin 2) K := fun j =>
    ((ζ (Multiplicative.ofAdd (e j)) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)
  let N0 : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K := WitSpNs.planeMat M
  have hM : ∀ j, M j * M j + M j =
      if j ∈ S then (1 : Matrix (Fin 2) (Fin 2) K) else 0 := by
    intro j
    have := CFSG.StandardType.GGQ2Frame.SpBlocks.zeta_mul_self_add (K := K) hK hζ (e j)
    simpa [M, S, PlaneRaw.mem_extSupport] using this
  have hblocks : N0 * N0 + N0 =
      CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem (K := K) t S := by
    rw [show N0 * N0 + N0 = WitSpNs.planeMat (fun j => M j * M j + M j) from by
      rw [show N0 = WitSpNs.planeMat M from rfl, WitSpNs.planeMat_mul,
        CFSG.StandardType.GGQ2Frame.SpBlocks.planeMat_add]
      rfl]
    rw [CFSG.StandardType.GGQ2Frame.SpBlocks.planeIdem_eq_planeMat]
    congr 1
    funext j
    exact hM j
  have htau : ((tau ζ t ε e : GL (LinIdx t ε) K) :
      Matrix (LinIdx t ε) (LinIdx t ε) K) = Matrix.fromBlocks N0 0 0 1 :=
    coe_tau_eq_fromBlocks_planeMat ζ t ε e
  rw [htau, planeIdem_false_eq_fromBlocks, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_add, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [mul_zero, zero_mul, add_assoc] using hblocks
  · simp
  · simp
  · simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]
    ext i j
    exact CharTwo.add_self_eq_zero ((1 : Matrix (Fin ε) (Fin ε) K) i j)

private noncomputable def f2LinearEquivOfF4 {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module (CFSG.Fischer.F4) W] [Algebra (ZMod 2) CFSG.Fischer.F4]
    [IsScalarTower (ZMod 2) CFSG.Fischer.F4 W]
    (e : W ≃ₗ[CFSG.Fischer.F4] W) : W ≃ₗ[ZMod 2] W :=
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := fun r v => by
      rw [← algebraMap_smul CFSG.Fischer.F4 r v, e.map_smul, algebraMap_smul]
      rfl }

private theorem centralizer_orderThree_mulEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : Fintype.card ι = 2 * k) (U : GL ι (ZMod 2))
    (hU : (U : Matrix ι ι (ZMod 2)) * (U : Matrix ι ι (ZMod 2)) +
      (U : Matrix ι ι (ZMod 2)) = 1) :
    Nonempty (↥(Subgroup.centralizer ({U} : Set (GL ι (ZMod 2)))) ≃*
      GL (Fin k) CFSG.Fischer.F4) := by
  classical
  let W := ι → ZMod 2
  let C : W →ₗ[ZMod 2] W := Matrix.toLin' (U : Matrix ι ι (ZMod 2))
  have hC : C * C + C + 1 = 0 := by
    have h : C * C + C = 1 := by
      have := congrArg (Matrix.toLin' (R := ZMod 2)) hU
      rw [map_add, Matrix.toLin'_mul, Matrix.toLin'_one] at this
      change toLin' (U : Matrix ι ι (ZMod 2)) ∘ₗ
        toLin' (U : Matrix ι ι (ZMod 2)) + toLin' (U : Matrix ι ι (ZMod 2)) = LinearMap.id
      exact this
    rw [h]
    apply LinearMap.ext
    intro v
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  let : Algebra (ZMod 2) CFSG.Fischer.F4 := ZMod.algebra CFSG.Fischer.F4 2
  let : Module CFSG.Fischer.F4 W :=
    CFSG.GroupTheory.F4ModuleFromOperator.Operator.f4Module C hC
  let : IsScalarTower (ZMod 2) CFSG.Fischer.F4 W :=
    CFSG.GroupTheory.F4ModuleFromOperator.Operator.isScalarTower_f4Module C hC
  have hfin2 : Module.finrank (ZMod 2) W = 2 * k := by
    rw [Module.finrank_fintype_fun_eq_card, hk]
  have hfin4 : Module.finrank CFSG.Fischer.F4 W = k := by
    have h := Module.finrank_mul_finrank (ZMod 2) CFSG.Fischer.F4 W
    have hF2 : Module.finrank (ZMod 2) CFSG.Fischer.F4 = 2 :=
      CFSG.GroupTheory.HeisenbergF4.finrank_f2_eq_two
    rw [hF2, hfin2] at h
    omega
  let b : Module.Basis (Fin k) CFSG.Fischer.F4 W :=
    (Module.finBasis CFSG.Fischer.F4 W).reindex (finCongr hfin4)
  let eB : (W ≃ₗ[CFSG.Fischer.F4] W) ≃* GL (Fin k) CFSG.Fischer.F4 :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv CFSG.Fischer.F4 W).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)
  let φGL : GL ι (ZMod 2) ≃* (W ≃ₗ[ZMod 2] W) :=
    (Matrix.GeneralLinearGroup.toLin).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
  let uC : W ≃ₗ[ZMod 2] W := φGL U
  have huC : (uC : W →ₗ[ZMod 2] W) = C := by
    apply LinearMap.ext
    intro v
    change (Matrix.mulVecLin (U : Matrix ι ι (ZMod 2))) v =
      (Matrix.toLin' (U : Matrix ι ι (ZMod 2))) v
    rw [Matrix.toLin'_apply, Matrix.mulVecLin_apply]
  have huCfun : (uC : W → W) = C := congrArg (fun f : W →ₗ[ZMod 2] W => (f : W → W)) huC
  have hmapU : (Subgroup.centralizer ({U} : Set (GL ι (ZMod 2)))).map φGL.toMonoidHom =
      Subgroup.centralizer ({uC} : Set (W ≃ₗ[ZMod 2] W)) :=
    CFSG.centralizer_singleton_map φGL U
  let toC : (W ≃ₗ[CFSG.Fischer.F4] W) →*
      ↥(Subgroup.centralizer ({uC} : Set (W ≃ₗ[ZMod 2] W))) :=
    { toFun := fun e =>
        ⟨f2LinearEquivOfF4 e, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          ext v w
          have he : (f2LinearEquivOfF4 e).toLinearMap.comp C =
              C.comp (f2LinearEquivOfF4 e).toLinearMap := by
            apply LinearMap.ext
            intro w
            change e (C w) = C (e w)
            rw [show C w = CFSG.Fischer.F4.ω • w from
              (CFSG.GroupTheory.F4ModuleFromOperator.Operator.f4Module_omega_smul C hC w).symm]
            rw [e.map_smul]
            exact CFSG.GroupTheory.F4ModuleFromOperator.Operator.f4Module_omega_smul C hC (e w)
          have hpoint := congrArg (fun f : W →ₗ[ZMod 2] W => f v) he
          have hw := congrArg (fun x : W => x w) hpoint
          simpa [LinearEquiv.mul_apply, LinearMap.comp_apply, huCfun] using hw⟩
      map_one' := by
        ext v
        rfl
      map_mul' := fun e e' => by
        ext v
        rfl }
  have toC_inj : Function.Injective toC := by
    intro e e' h
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : ↥(Subgroup.centralizer ({uC} : Set (W ≃ₗ[ZMod 2] W))) =>
      (f : W ≃ₗ[ZMod 2] W) v) h
  have toC_surj : Function.Surjective toC := by
    intro g
    refine ⟨CFSG.GroupTheory.F4ModuleFromOperator.Operator.f4LinearEquiv C hC
      (g : W ≃ₗ[ZMod 2] W) ?_, ?_⟩
    · apply LinearMap.ext
      intro v
      have hg := (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      have hpoint := congrArg (fun f : W ≃ₗ[ZMod 2] W => f v) hg
      simpa [LinearEquiv.mul_apply, huCfun] using hpoint
    · apply Subtype.ext
      ext v
      rfl
  let eC : (W ≃ₗ[CFSG.Fischer.F4] W) ≃*
      ↥(Subgroup.centralizer ({uC} : Set (W ≃ₗ[ZMod 2] W))) :=
    MulEquiv.ofBijective toC ⟨toC_inj, toC_surj⟩
  have hcenter : ↥(Subgroup.centralizer ({U} : Set (GL ι (ZMod 2)))) ≃*
      ↥(Subgroup.centralizer ({uC} : Set (W ≃ₗ[ZMod 2] W))) :=
    (Subgroup.equivMapOfInjective (Subgroup.centralizer ({U} : Set (GL ι (ZMod 2))))
      φGL.toMonoidHom φGL.injective).trans (MulEquiv.subgroupCongr hmapU)
  exact ⟨hcenter.trans (eC.symm.trans eB)⟩

private theorem extension_zmod2 (ζ : Multiplicative (ZMod 3) →*
    SpecialLinearGroup (Fin 2) (ZMod 2)) (hζ : Function.Injective ζ) (t : ℕ) (ε : Fin 2)
    {e : PlaneRaw.V t} (he : e ≠ 0) :
    Nonempty (↥(blockGroup ζ t ε (PlaneRaw.Code.extension e)) ≃*
      GL (Fin (PlaneRaw.Code.extSupport e).card) CFSG.Fischer.F4) := by
  classical
  let S := PlaneRaw.Code.extSupport e
  let P : Matrix (LinIdx t ε) (LinIdx t ε) (ZMod 2) := planeIdem t ε S false
  let f : LinIdx t ε → ZMod 2 := fun x => P x x
  have hf : ∀ x, f x = 0 ∨ f x = 1 := by
    intro x
    rcases x with (i | i) | j
    · by_cases h : i ∈ S <;> simp [f, P, planeIdem, h]
    · by_cases h : i ∈ S <;> simp [f, P, planeIdem, h]
    · simp [f, P, planeIdem]
  have hdiag : Matrix.diagonal f = P := by
    ext x y
    by_cases hxy : x = y <;> simp [f, P, planeIdem, hxy]
  have htau : tau ζ t ε e ∈ levi P := tau_mem_levi_ext ζ t ε S e rfl
  let T := {x : LinIdx t ε // P x x = 1}
  let e0 := diagSupportEquiv (K := ZMod 2) f
  let Φ : ↥(levi P) ≃* GL T (ZMod 2) :=
    (MulEquiv.subgroupCongr (congrArg levi hdiag.symm)).trans (leviDiagonalEquiv f hf)
  let tauL : ↥(levi P) := ⟨tau ζ t ε e, htau⟩
  let U : GL T (ZMod 2) := Φ tauL
  have hUcoe : ((U : GL T (ZMod 2)) : Matrix T T (ZMod 2)) =
      Matrix.toBlocks₁₁ (Matrix.reindex e0.symm e0.symm
        (((tau ζ t ε e : GL (LinIdx t ε) (ZMod 2))) :
          Matrix (LinIdx t ε) (LinIdx t ε) (ZMod 2))) := by
    change ((leviDiagonalEquiv f hf (MulEquiv.subgroupCongr (congrArg levi hdiag.symm) tauL) :
      GL T (ZMod 2)) : Matrix T T (ZMod 2)) = _
    rw [leviDiagonalEquiv_coe]
    rfl
  have h1 : (((tau ζ t ε e : GL (LinIdx t ε) (ZMod 2))) :
      Matrix (LinIdx t ε) (LinIdx t ε) (ZMod 2)) * (1 - Matrix.diagonal f) =
        1 - Matrix.diagonal f := by
    simpa [hdiag] using htau.1
  have h2 : (1 - Matrix.diagonal f) * (((tau ζ t ε e :
      GL (LinIdx t ε) (ZMod 2))) : Matrix (LinIdx t ε) (LinIdx t ε) (ZMod 2)) =
        1 - Matrix.diagonal f := by
    simpa [hdiag] using htau.2
  have hblock : Matrix.reindex e0.symm e0.symm
      (((tau ζ t ε e : GL (LinIdx t ε) (ZMod 2))) :
        Matrix (LinIdx t ε) (LinIdx t ε) (ZMod 2)) =
      Matrix.fromBlocks (U : Matrix T T (ZMod 2)) 0 0 1 := by
    rw [reindex_diagonal_fixes_complement f hf h1 h2, hUcoe]
  have hU : (U : Matrix T T (ZMod 2)) * (U : Matrix T T (ZMod 2)) +
      (U : Matrix T T (ZMod 2)) = 1 := by
    have hsq := tau_sq_add_ext (ζ := ζ) (K := ZMod 2)
      (by rw [Nat.card_eq_fintype_card, ZMod.card]) hζ t ε he
    have hsq' := congrArg (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e0.symm) hsq
    rw [map_add, map_mul] at hsq'
    have hTau' : (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e0.symm)
        ((((tau ζ t ε e : GL (LinIdx t ε) (ZMod 2))) :
          Matrix (LinIdx t ε) (LinIdx t ε) (ZMod 2))) =
        Matrix.fromBlocks (U : Matrix T T (ZMod 2)) 0 0 1 := by
      change Matrix.reindex e0.symm e0.symm
        ((((tau ζ t ε e : GL (LinIdx t ε) (ZMod 2))) :
          Matrix (LinIdx t ε) (LinIdx t ε) (ZMod 2))) =
        Matrix.fromBlocks (U : Matrix T T (ZMod 2)) 0 0 1
      exact hblock
    have hright : (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e0.symm)
        (planeIdem (K := ZMod 2) t ε S false) =
        Matrix.fromBlocks (1 : Matrix T T (ZMod 2)) 0 0
          (0 : Matrix {x : LinIdx t ε // ¬ P x x = 1}
            {x : LinIdx t ε // ¬ P x x = 1} (ZMod 2)) := by
      change Matrix.reindex e0.symm e0.symm
        (planeIdem (K := ZMod 2) t ε S false) = _
      rw [show planeIdem (K := ZMod 2) t ε S false = Matrix.diagonal f from hdiag.symm]
      exact reindex_diagonal_eq_fromBlocks (K := ZMod 2) f hf
    rw [hTau', hright] at hsq'
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.fromBlocks_inj] at hsq'
    simpa [mul_zero, zero_mul, add_assoc] using hsq'.1
  have hk : Fintype.card T = 2 * S.card :=
    card_planeIdem_support_false (K := ZMod 2) t ε S
  obtain ⟨eC⟩ := centralizer_orderThree_mulEquiv S.card hk U hU
  let Clevi : Subgroup ↥(levi P) := Subgroup.centralizer ({tauL} : Set ↥(levi P))
  have hsub : (blockGroup ζ t ε (PlaneRaw.Code.extension e)).subgroupOf (levi P) = Clevi := by
    ext x
    change ↑x ∈ levi P ⊓ Subgroup.centralizer ({tau ζ t ε e} : Set
      (GL (LinIdx t ε) (ZMod 2))) ↔
      x ∈ Subgroup.centralizer ({tauL} : Set ↥(levi P))
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      exact Subtype.ext hx
    · intro hx
      exact ⟨x.2, congrArg (fun y : ↥(levi P) => (y : GL (LinIdx t ε) (ZMod 2))) hx⟩
  have hBiso : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e)) ≃* ↥Clevi :=
    (Subgroup.subgroupOfEquivOfLe (show blockGroup ζ t ε (PlaneRaw.Code.extension e) ≤ levi P
      from inf_le_left)).symm.trans
      (MulEquiv.subgroupCongr hsub)
  have hClevi : ↥Clevi ≃* ↥(Subgroup.centralizer ({U} : Set (GL T (ZMod 2)))) :=
    (Subgroup.equivMapOfInjective Clevi Φ.toMonoidHom Φ.injective).trans
      (MulEquiv.subgroupCongr (CFSG.centralizer_singleton_map Φ tauL))
  exact ⟨hBiso.trans (hClevi.trans eC)⟩

private noncomputable def mapGL {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    (ι : Type) [Fintype ι] [DecidableEq ι] : GL ι K ≃* GL ι L :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := ι) φ).toMulEquiv

private theorem mapGL_coe {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K) :
    ((mapGL φ ι g : GL ι L) : Matrix ι ι L) = RingEquiv.mapMatrix φ (g : Matrix ι ι K) := rfl

private theorem planeIdem_map {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) (fix : Bool) :
    ((planeIdem (K := K) t ε S fix : Matrix (LinIdx t ε) (LinIdx t ε) K).map φ) =
      (planeIdem (K := L) t ε S fix : Matrix (LinIdx t ε) (LinIdx t ε) L) := by
  classical
  rw [planeIdem, planeIdem, Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext x
  rcases x with (i | i) | j
  · by_cases h : i ∈ S <;> simp [h]
  · by_cases h : i ∈ S <;> simp [h]
  · by_cases h : fix = true <;> simp [h]

private theorem planeMat_map {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    {t : ℕ} (M : Fin t → Matrix (Fin 2) (Fin 2) K) :
    ((WitSpNs.planeMat M).map φ) = WitSpNs.planeMat (fun j => (M j).map φ) := by
  ext a b
  simp only [WitSpNs.planeMat_apply, Matrix.map_apply]
  by_cases h : WitSpNs.plane a = WitSpNs.plane b <;> simp [h]

private theorem tau_map {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    (u : PlaneRaw.V t) :
    ((mapGL φ (LinIdx t ε)) (tau ζ t ε u)) =
      tau ((SpecialLinearGroup.map (n := Fin 2) φ.toRingHom).comp ζ) t ε u := by
  apply Units.ext
  rw [mapGL_coe]
  rw [coe_tau_eq_fromBlocks_planeMat, coe_tau_eq_fromBlocks_planeMat]
  change ((Matrix.fromBlocks (WitSpNs.planeMat fun j =>
      (((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K)) 0 0 1).map (fun x => φ x)) = _
  rw [Matrix.fromBlocks_map]
  congr 1
  · rw [planeMat_map]
    rw [show (fun j => (((ζ (Multiplicative.ofAdd (u j)) :
          SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map φ)) =
        (fun j => ((SpecialLinearGroup.map φ.toRingHom
          (ζ (Multiplicative.ofAdd (u j))) : SpecialLinearGroup (Fin 2) L) :
            Matrix (Fin 2) (Fin 2) L)) from by
      funext j
      exact (SpecialLinearGroup.map_apply_coe φ.toRingHom
        (ζ (Multiplicative.ofAdd (u j)))).symm]
    rfl
  · simp [Matrix.map_zero]
  · simp [Matrix.map_zero]
  · simp [Matrix.map_one]

private theorem levi_map {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι K) :
    (levi P).map (mapGL φ ι).toMonoidHom = levi (P.map φ) := by
  classical
  have hsymm_coe (g : GL ι L) :
      ((((mapGL φ ι).symm g : GL ι K)) : Matrix ι ι K) =
        RingEquiv.mapMatrix φ.symm (g : Matrix ι ι L) := rfl
  ext g
  rw [Subgroup.mem_map_equiv, levi, levi]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have h := congrArg (RingEquiv.mapMatrix φ) h1
      rw [map_mul, map_sub, map_one] at h
      rw [← mapGL_coe (φ := φ) ((mapGL φ ι).symm g)] at h
      rw [MulEquiv.apply_symm_apply] at h
      exact h
    · have h := congrArg (RingEquiv.mapMatrix φ) h2
      rw [map_mul, map_sub, map_one] at h
      rw [← mapGL_coe (φ := φ) ((mapGL φ ι).symm g)] at h
      rw [MulEquiv.apply_symm_apply] at h
      exact h
  · rintro ⟨h1, h2⟩
    have hPP : RingEquiv.mapMatrix φ.symm (P.map (fun x => φ x)) = P := by
      ext i j
      simp
    constructor
    · have h := congrArg (RingEquiv.mapMatrix φ.symm) h1
      rw [map_mul, map_sub, map_one, hPP] at h
      rw [← hsymm_coe g] at h
      exact h
    · have h := congrArg (RingEquiv.mapMatrix φ.symm) h2
      rw [map_mul, map_sub, map_one, hPP] at h
      rw [← hsymm_coe g] at h
      exact h

private theorem blockGroup_extension_map {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    (e : PlaneRaw.V t) :
    (blockGroup ζ t ε (PlaneRaw.Code.extension e)).map (mapGL φ (LinIdx t ε)).toMonoidHom =
      blockGroup ((SpecialLinearGroup.map (n := Fin 2) φ.toRingHom).comp ζ) t ε
        (PlaneRaw.Code.extension e) := by
  classical
  let S := PlaneRaw.Code.extSupport e
  have hP : (planeIdem (K := K) t ε S false).map φ =
      planeIdem (K := L) t ε S false := planeIdem_map φ t ε S false
  have htau : mapGL φ (LinIdx t ε) (tau ζ t ε e) =
      tau ((SpecialLinearGroup.map (n := Fin 2) φ.toRingHom).comp ζ) t ε e := tau_map φ ζ t ε e
  change (levi (planeIdem (K := K) t ε S false) ⊓
      Subgroup.centralizer ({tau ζ t ε e} : Set (GL (LinIdx t ε) K))).map
        (Units.mapEquiv (RingEquiv.mapMatrix (m := LinIdx t ε) φ).toMulEquiv).toMonoidHom = _
  rw [Subgroup.map_inf (H := levi (planeIdem (K := K) t ε S false))
    (K := Subgroup.centralizer ({tau ζ t ε e} : Set (GL (LinIdx t ε) K)))
    (f := (Units.mapEquiv (RingEquiv.mapMatrix (m := LinIdx t ε) φ).toMulEquiv).toMonoidHom)
    (Units.mapEquiv (RingEquiv.mapMatrix (m := LinIdx t ε) φ).toMulEquiv).injective]
  change (levi (planeIdem (K := K) t ε S false)).map (mapGL φ (LinIdx t ε)).toMonoidHom ⊓
      (Subgroup.centralizer ({tau ζ t ε e} : Set (GL (LinIdx t ε) K))).map
        (mapGL φ (LinIdx t ε)).toMonoidHom = _
  rw [levi_map φ, hP, CFSG.centralizer_singleton_map, htau]
  rfl

theorem exists_blockGroup_extension_mulEquiv [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t} (he : e ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (_ : CharP L 2), Nat.card L = 2 ^ 2 ∧
      Nonempty (↥(blockGroup ζ t ε (PlaneRaw.Code.extension e)) ≃*
        GL (Fin (PlaneRaw.Code.extSupport e).card) L) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hZ2]
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
  let ζ' : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) (ZMod 2) :=
    (SpecialLinearGroup.map (n := Fin 2) φ.toRingHom).comp ζ
  have hφSL : Function.Injective (SpecialLinearGroup.map (n := Fin 2) φ.toRingHom) := by
    intro A B hAB
    apply Subtype.ext
    ext i j
    have h := congrArg (fun M : SpecialLinearGroup (Fin 2) (ZMod 2) =>
      (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j) hAB
    simp only [SpecialLinearGroup.map_apply_coe] at h
    exact φ.injective h
  have hζ' : Function.Injective ζ' := hφSL.comp hζ
  have hmap := blockGroup_extension_map φ ζ t ε e
  obtain ⟨eZ⟩ := extension_zmod2 ζ' hζ' t ε he
  let eTrans : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e)) ≃*
      ↥(blockGroup ζ' t ε (PlaneRaw.Code.extension e)) :=
    (Subgroup.equivMapOfInjective (blockGroup ζ t ε (PlaneRaw.Code.extension e))
      (mapGL φ (LinIdx t ε)).toMonoidHom (mapGL φ (LinIdx t ε)).injective).trans
      (MulEquiv.subgroupCongr hmap)
  refine ⟨CFSG.Fischer.F4, ?_, ?_, ?_, ?_, ?_⟩
  · exact inferInstance
  · exact inferInstance
  · exact inferInstance
  · rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card]
    norm_num
  · exact ⟨eTrans.trans eZ⟩

end

end CFSG.StandardType.GGQ2Frame.LinBlocks
