module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksDefs
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCent
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksBasic

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin Matrix
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ} {ε : Fin 2}

private def reindexGL {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) : GL ι K ≃* GL κ K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv

omit [Finite K] [CharP K 2] in
private theorem coe_reindexGL {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (g : GL ι K) :
    ((reindexGL e g : GL κ K) : Matrix κ κ K) =
      Matrix.reindexAlgEquiv K K e (g : Matrix ι ι K) := by
  simp [reindexGL]

omit [Finite K] [CharP K 2] in
private theorem mem_levi_reindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (P : Matrix ι ι K) (g : GL ι K) :
    g ∈ levi P ↔ reindexGL e g ∈ levi (Matrix.reindexAlgEquiv K K e P) := by
  change ((g : Matrix ι ι K) * (1 - P) = 1 - P ∧
      (1 - P) * (g : Matrix ι ι K) = 1 - P) ↔
    (((reindexGL e g : GL κ K) : Matrix κ κ K) *
        (1 - Matrix.reindexAlgEquiv K K e P) = 1 - Matrix.reindexAlgEquiv K K e P ∧
      (1 - Matrix.reindexAlgEquiv K K e P) *
        ((reindexGL e g : GL κ K) : Matrix κ κ K) =
          1 - Matrix.reindexAlgEquiv K K e P)
  rw [coe_reindexGL]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := congrArg (Matrix.reindexAlgEquiv K K e) h1
      simpa only [map_mul, map_sub, map_one, AlgEquiv.symm_apply_apply] using this
    · have := congrArg (Matrix.reindexAlgEquiv K K e) h2
      simpa only [map_mul, map_sub, map_one, AlgEquiv.symm_apply_apply] using this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := congrArg (Matrix.reindexAlgEquiv K K e).symm h1
      simpa only [map_mul, map_sub, map_one, AlgEquiv.symm_apply_apply] using this
    · have := congrArg (Matrix.reindexAlgEquiv K K e).symm h2
      simpa only [map_mul, map_sub, map_one, AlgEquiv.symm_apply_apply] using this

omit [Finite K] [CharP K 2] in
private theorem map_levi_reindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (P : Matrix ι ι K) :
    (levi P).map (reindexGL e).toMonoidHom = levi (Matrix.reindexAlgEquiv K K e P) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (mem_levi_reindex e P h).mp hh
  · intro hg
    refine ⟨(reindexGL e).symm g, ?_, ?_⟩
    · exact (mem_levi_reindex e P _).mpr (by simpa using hg)
    · simp

private def zeroBlock (K : Type) [Field K] (μ ν : Type) [Fintype μ] [DecidableEq μ]
    [Fintype ν] [DecidableEq ν] : Matrix (μ ⊕ ν) (μ ⊕ ν) K :=
  Matrix.fromBlocks (1 : Matrix μ μ K) 0 0 (0 : Matrix ν ν K)

private def diagGL {μ ν : Type} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (A : GL μ K) : GL (μ ⊕ ν) K where
  val := Matrix.fromBlocks (A : Matrix μ μ K) 0 0 (1 : Matrix ν ν K)
  inv := Matrix.fromBlocks ((A⁻¹ : GL μ K) : Matrix μ μ K) 0 0 (1 : Matrix ν ν K)
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp

private def diagGLHom {μ ν : Type} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν] :
    GL μ K →* GL (μ ⊕ ν) K where
  toFun := diagGL
  map_one' := by
    apply Units.ext
    simp [diagGL, Matrix.fromBlocks_one]
  map_mul' A B := by
    apply Units.ext
    ext i j
    simp [diagGL, Matrix.fromBlocks_multiply]

omit [Finite K] [CharP K 2] in
private lemma one_sub_zeroBlock {μ ν : Type} [Fintype μ] [DecidableEq μ] [Fintype ν]
    [DecidableEq ν] :
    (1 : Matrix (μ ⊕ ν) (μ ⊕ ν) K) - zeroBlock K μ ν =
      Matrix.fromBlocks (0 : Matrix μ μ K) 0 0 (1 : Matrix ν ν K) := by
  rw [zeroBlock, ← Matrix.fromBlocks_one (l := μ) (m := ν), sub_eq_add_neg,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp

omit [Finite K] [CharP K 2] in
private lemma diagGL_mem_levi {μ ν : Type} [Fintype μ] [DecidableEq μ] [Fintype ν]
    [DecidableEq ν] (A : GL μ K) : diagGL A ∈ levi (zeroBlock K μ ν) := by
  change ((diagGL A : GL (μ ⊕ ν) K) : Matrix (μ ⊕ ν) (μ ⊕ ν) K) * (1 - zeroBlock K μ ν) =
      1 - zeroBlock K μ ν ∧
    (1 - zeroBlock K μ ν) * ((diagGL A : GL (μ ⊕ ν) K) : Matrix (μ ⊕ ν) (μ ⊕ ν) K) =
      1 - zeroBlock K μ ν
  rw [one_sub_zeroBlock]
  constructor
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [diagGL, Matrix.fromBlocks_multiply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [diagGL, Matrix.fromBlocks_multiply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

omit [Finite K] [CharP K 2] in
private lemma levi_zeroBlock_eq_range {μ ν : Type} [Fintype μ] [DecidableEq μ] [Fintype ν]
    [DecidableEq ν] :
    levi (zeroBlock K μ ν) = diagGLHom.range := by
  ext g
  constructor
  · intro hg
    set M : Matrix (μ ⊕ ν) (μ ⊕ ν) K := (g : Matrix (μ ⊕ ν) (μ ⊕ ν) K) with hM
    have hMblocks : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
      (Matrix.fromBlocks_toBlocks M).symm
    have hg1 : M * (1 - zeroBlock K μ ν) = 1 - zeroBlock K μ ν := by
      simpa [hM] using hg.1
    rw [one_sub_zeroBlock, hMblocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hg1
    obtain ⟨-, hB, -, hD⟩ := hg1
    simp only [Matrix.mul_zero, zero_add, Matrix.mul_one] at hB hD
    have hg2 : (1 - zeroBlock K μ ν) * M = 1 - zeroBlock K μ ν := by
      simpa [hM] using hg.2
    rw [one_sub_zeroBlock, hMblocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hg2
    obtain ⟨-, -, hC, -⟩ := hg2
    simp only [Matrix.zero_mul, zero_add, Matrix.one_mul] at hC
    have hMeq : M = Matrix.fromBlocks M.toBlocks₁₁ 0 0 (1 : Matrix ν ν K) := by
      calc M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ := hMblocks
        _ = Matrix.fromBlocks M.toBlocks₁₁ 0 0 (1 : Matrix ν ν K) := by rw [hB, hC, hD]
    have hginv : g⁻¹ ∈ levi (zeroBlock K μ ν) := (levi (zeroBlock K μ ν)).inv_mem hg
    set M' : Matrix (μ ⊕ ν) (μ ⊕ ν) K := (g⁻¹ : Matrix (μ ⊕ ν) (μ ⊕ ν) K) with hM'
    have hM'blocks : M' =
        Matrix.fromBlocks M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂ :=
      (Matrix.fromBlocks_toBlocks M').symm
    have hg1' : M' * (1 - zeroBlock K μ ν) = 1 - zeroBlock K μ ν := by
      simpa [hM'] using hginv.1
    rw [one_sub_zeroBlock, hM'blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hg1'
    obtain ⟨-, hB', -, hD'⟩ := hg1'
    simp only [Matrix.mul_zero, zero_add, Matrix.mul_one] at hB' hD'
    have hg2' : (1 - zeroBlock K μ ν) * M' = 1 - zeroBlock K μ ν := by
      simpa [hM'] using hginv.2
    rw [one_sub_zeroBlock, hM'blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hg2'
    obtain ⟨-, -, hC', -⟩ := hg2'
    simp only [Matrix.zero_mul, zero_add, Matrix.one_mul] at hC'
    have hM'eq : M' = Matrix.fromBlocks M'.toBlocks₁₁ 0 0 (1 : Matrix ν ν K) := by
      calc M' = Matrix.fromBlocks M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂ :=
          hM'blocks
        _ = Matrix.fromBlocks M'.toBlocks₁₁ 0 0 (1 : Matrix ν ν K) := by rw [hB', hC', hD']
    have hmul : g * g⁻¹ = 1 := mul_inv_cancel g
    have hmulM : M * M' = 1 := by
      have := congrArg (fun u : GL (μ ⊕ ν) K => (u : Matrix (μ ⊕ ν) (μ ⊕ ν) K)) hmul
      simp [hM, hM']
    rw [hMeq, hM'eq, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one (l := μ) (m := ν),
      Matrix.fromBlocks_inj] at hmulM
    obtain ⟨hAA', -, -, -⟩ := hmulM
    simp only [Matrix.mul_zero, add_zero] at hAA'
    have hmul2 : g⁻¹ * g = 1 := inv_mul_cancel g
    have hmulM2 : M' * M = 1 := by
      have := congrArg (fun u : GL (μ ⊕ ν) K => (u : Matrix (μ ⊕ ν) (μ ⊕ ν) K)) hmul2
      simp [hM, hM']
    rw [hM'eq, hMeq, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one (l := μ) (m := ν),
      Matrix.fromBlocks_inj] at hmulM2
    obtain ⟨hA'A, -, -, -⟩ := hmulM2
    simp only [Matrix.mul_zero, add_zero] at hA'A
    refine ⟨⟨M.toBlocks₁₁, M'.toBlocks₁₁, hAA', hA'A⟩, ?_⟩
    apply Units.ext
    simpa [diagGLHom, diagGL, hM] using hMeq.symm
  · rintro ⟨A, rfl⟩
    exact diagGL_mem_levi A

omit [Finite K] [CharP K 2] in
private theorem levi_zeroBlock_perfect {μ ν : Type} [Fintype μ] [DecidableEq μ]
    [Fintype ν] [DecidableEq ν] (hK : Nat.card K = 2) (hμ : 3 ≤ Fintype.card μ) :
    Group.IsPerfect ↥(levi (zeroBlock K μ ν)) := by
  have hsurj : Function.Surjective
      (diagGLHom.codRestrict (levi (zeroBlock K μ ν)) fun A => diagGL_mem_levi A) := by
    intro g
    have hg : (g : GL (μ ⊕ ν) K) ∈ diagGLHom.range := by
      rw [← levi_zeroBlock_eq_range]
      exact g.2
    obtain ⟨A, hA⟩ := hg
    exact ⟨A, Subtype.ext hA⟩
  have hSLperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (Fintype.card μ)) K) :=
    CFSG.LinearGroups.special_linear_isPerfect (n := Fintype.card μ) (by omega)
      (Or.inl (by omega))
  have hdet : Function.Surjective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (Fintype.card μ)) K →*
        GL (Fin (Fintype.card μ)) K) := by
    intro A
    have hcardK : Nat.card Kˣ = 1 := by
      simp [Nat.card_units, hK]
    have hsub : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hcardK).1
    have h1 : Matrix.GeneralLinearGroup.det A = 1 := @Subsingleton.elim Kˣ hsub _ _
    have hdetA : (A : Matrix (Fin (Fintype.card μ)) (Fin (Fintype.card μ)) K).det = 1 := by
      have h2 := congrArg (fun u : Kˣ => (u : K)) h1
      simpa using h2
    exact ⟨⟨(A : Matrix (Fin (Fintype.card μ)) (Fin (Fintype.card μ)) K), hdetA⟩,
      Units.ext rfl⟩
  have hGLfin : Group.IsPerfect (GL (Fin (Fintype.card μ)) K) :=
    @Group.IsPerfect.ofSurjective (Matrix.SpecialLinearGroup (Fin (Fintype.card μ)) K)
      (GL (Fin (Fintype.card μ)) K) _ _ Matrix.SpecialLinearGroup.toGL hSLperf hdet
  let e : μ ≃ Fin (Fintype.card μ) := Fintype.equivFin μ
  have hGLμ : Group.IsPerfect (GL μ K) :=
    @Group.IsPerfect.ofSurjective (GL (Fin (Fintype.card μ)) K) (GL μ K) _ _
      (reindexGL e).symm.toMonoidHom hGLfin (reindexGL e).symm.surjective
  exact @Group.IsPerfect.ofSurjective (GL μ K)
    ↥(levi (zeroBlock K μ ν)) _ _
    (diagGLHom.codRestrict (levi (zeroBlock K μ ν)) fun A => diagGL_mem_levi A) hGLμ hsurj

private def zeroW (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) : Finset (LinIdx t ε) :=
  (S.image fun i => (Sum.inl (Sum.inl i) : LinIdx t ε)) ∪
    ((S.image fun i => (Sum.inl (Sum.inr i) : LinIdx t ε)) ∪
      (Finset.univ.image fun f : Fin ε.val => (Sum.inr f : LinIdx t ε)))

omit [Finite K] [CharP K 2] in
private lemma planeIdem_diag (S : Finset (Fin t)) (x : LinIdx t ε) :
    (planeIdem (K := K) t ε S true) x x =
      if x ∈ zeroW t ε S then 1 else 0 := by
  rcases x with ((i | i) | f)
  · by_cases hi : i ∈ S <;> simp [zeroW, planeIdem, hi]
  · by_cases hi : i ∈ S <;> simp [zeroW, planeIdem, hi]
  · simp [zeroW, planeIdem]

private lemma card_zeroW (S : Finset (Fin t)) :
    (zeroW t ε S).card = 2 * S.card + ε.val := by
  let A : Finset (LinIdx t ε) := S.image fun i => (Sum.inl (Sum.inl i) : LinIdx t ε)
  let B : Finset (LinIdx t ε) := S.image fun i => (Sum.inl (Sum.inr i) : LinIdx t ε)
  let C : Finset (LinIdx t ε) := Finset.univ.image fun f : Fin ε.val => (Sum.inr f : LinIdx t ε)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    simp only [A, B, Finset.mem_image] at hx hx'
    obtain ⟨a, -, rfl⟩ := hx
    simp at hx'
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    simp only [B, C, Finset.mem_image] at hx hx'
    obtain ⟨a, -, rfl⟩ := hx
    simp at hx'
  have hABC : Disjoint A (B ∪ C) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    simp only [A, B, C, Finset.mem_image, Finset.mem_univ, Finset.mem_union, true_and] at hx hx'
    obtain ⟨a, -, rfl⟩ := hx
    simp at hx'
  have hA : A.card = S.card :=
    Finset.card_image_of_injective _ (fun a b h => by
      injection h with h1
      exact Sum.inl.inj h1)
  have hB : B.card = S.card :=
    Finset.card_image_of_injective _ (fun a b h => by
      injection h with h1
      exact Sum.inr.inj h1)
  have hC : C.card = ε.val := by
    dsimp only [C]
    rw [Finset.card_image_of_injective _ (fun a b h => Sum.inr.inj h), Finset.card_univ,
      Fintype.card_fin]
  have hW : zeroW t ε S = A ∪ (B ∪ C) := rfl
  rw [hW, Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hBC, hA, hB, hC]
  omega

omit [Finite K] [CharP K 2] in
private lemma planeIdem_apply_eq {S : Finset (Fin t)} {x y : LinIdx t ε} :
    (planeIdem (K := K) t ε S true) x y =
      if x = y then (if x ∈ zeroW t ε S then 1 else 0) else 0 := by
  rw [planeIdem, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    simpa [planeIdem, Matrix.diagonal_apply] using planeIdem_diag S x
  · rw [if_neg hxy]
    simp [hxy]

omit [Finite K] [CharP K 2] in
private lemma reindex_planeIdem_zeroW (S : Finset (Fin t)) :
    let W : Finset (LinIdx t ε) := zeroW t ε S
    let Wc := {x : LinIdx t ε // x ∉ W}
    let e : LinIdx t ε ≃ W ⊕ Wc := (Equiv.sumCompl (fun x => x ∈ W)).symm
    Matrix.reindexAlgEquiv K K e (planeIdem (K := K) t ε S true) = zeroBlock K W Wc := by
  intro W Wc e
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.fromBlocks_apply₁₁, zeroBlock]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inl i, Equiv.sumCompl_apply_inl j, planeIdem_apply_eq]
    by_cases hij : i.1 = j.1
    · rw [if_pos hij]
      have hi : i.1 ∈ zeroW t ε S := by simpa only [W] using i.2
      have hij' : i = j := Subtype.ext hij
      subst hij'
      simp [hi]
    · rw [if_neg hij]
      have hij' : i ≠ j := fun h => hij (congrArg Subtype.val h)
      simp [hij']
  · simp only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.fromBlocks_apply₁₂, zeroBlock]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inl i, Equiv.sumCompl_apply_inr j, planeIdem_apply_eq]
    have hne : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
    simp [hne]
  · simp only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.fromBlocks_apply₂₁, zeroBlock]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inr i, Equiv.sumCompl_apply_inl j, planeIdem_apply_eq]
    have hne : i.1 ≠ j.1 := fun h => i.2 (h ▸ j.2)
    simp [hne]
  · simp only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.fromBlocks_apply₂₂, zeroBlock]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inr i, Equiv.sumCompl_apply_inr j, planeIdem_apply_eq]
    by_cases hij : i.1 = j.1
    · rw [if_pos hij]
      have hi : i.1 ∉ zeroW t ε S := by simpa only [W] using i.2
      simp [hi]
    · rw [if_neg hij]
      rfl

omit [Finite K] [CharP K 2] in
private theorem levi_zero_perfect (hK : Nat.card K = 2) {S : Finset (Fin t)}
    (hS : 3 ≤ 2 * S.card + ε.val) :
    ⁅levi (planeIdem (K := K) t ε S true), levi (planeIdem (K := K) t ε S true)⁆ =
      levi (planeIdem (K := K) t ε S true) := by
  let W : Finset (LinIdx t ε) := zeroW t ε S
  let Wc := {x : LinIdx t ε // x ∉ W}
  let e : LinIdx t ε ≃ W ⊕ Wc := (Equiv.sumCompl (fun x => x ∈ W)).symm
  have hP : Matrix.reindexAlgEquiv K K e (planeIdem (K := K) t ε S true) =
      zeroBlock K W Wc := reindex_planeIdem_zeroW S
  have hcard : 3 ≤ Fintype.card W := by
    rw [Fintype.card_coe]
    dsimp only [W]
    rw [card_zeroW]
    exact hS
  have hperf : Group.IsPerfect ↥(levi (zeroBlock K W Wc)) := levi_zeroBlock_perfect hK hcard
  have hmap : (levi (planeIdem (K := K) t ε S true)).map (reindexGL e).toMonoidHom =
      levi (zeroBlock K W Wc) := by
    rw [map_levi_reindex, hP]
  let iso : ↥(levi (planeIdem (K := K) t ε S true)) ≃* ↥(levi (zeroBlock K W Wc)) :=
    (Subgroup.equivMapOfInjective _ (reindexGL e).toMonoidHom (reindexGL e).injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact Subgroup.isPerfect_iff.mp
    (@Group.IsPerfect.ofSurjective ↥(levi (zeroBlock K W Wc))
      ↥(levi (planeIdem (K := K) t ε S true)) _ _ iso.symm.toMonoidHom hperf
      iso.symm.surjective)

omit [Finite K] [CharP K 2] in
private lemma one_sub_planeIdem_apply_of_not_mem {S : Finset (Fin t)} {x y : LinIdx t ε}
    (hy : y ∉ zeroW t ε S) :
    (1 - planeIdem (K := K) t ε S true) x y = if x = y then 1 else 0 := by
  rw [Matrix.sub_apply, Matrix.one_apply, planeIdem_apply_eq]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, if_pos rfl, if_neg hy]
    simp
  · rw [if_neg hxy, if_neg hxy]
    simp

omit [Finite K] [CharP K 2] in
private lemma one_sub_planeIdem_apply_of_mem {S : Finset (Fin t)} {x y : LinIdx t ε}
    (hy : y ∈ zeroW t ε S) :
    (1 - planeIdem (K := K) t ε S true) x y = 0 := by
  rw [Matrix.sub_apply, Matrix.one_apply, planeIdem_apply_eq]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, if_pos rfl, if_pos hy]
    simp
  · rw [if_neg hxy, if_neg hxy]
    simp

omit [Finite K] [CharP K 2] in
private lemma one_sub_planeIdem_apply_of_not_mem_left {S : Finset (Fin t)} {x y : LinIdx t ε}
    (hx : x ∉ zeroW t ε S) :
    (1 - planeIdem (K := K) t ε S true) x y = if x = y then 1 else 0 := by
  rw [Matrix.sub_apply, Matrix.one_apply, planeIdem_apply_eq]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, if_pos rfl, if_neg hx]
    simp
  · rw [if_neg hxy, if_neg hxy]
    simp

omit [Finite K] [CharP K 2] in
private lemma mul_one_sub_apply_of_mem {S : Finset (Fin t)}
    {T : Matrix (LinIdx t ε) (LinIdx t ε) K} {y : LinIdx t ε}
    (hy : y ∈ zeroW t ε S) (x : LinIdx t ε) :
    (T * (1 - planeIdem (K := K) t ε S true)) x y = 0 := by
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun z _ => by
    rw [one_sub_planeIdem_apply_of_mem hy, mul_zero]

omit [Finite K] [CharP K 2] in
private lemma mul_one_sub_apply_of_not_mem {S : Finset (Fin t)}
    {T : Matrix (LinIdx t ε) (LinIdx t ε) K} {y : LinIdx t ε}
    (hy : y ∉ zeroW t ε S) (x : LinIdx t ε) :
    (T * (1 - planeIdem (K := K) t ε S true)) x y = T x y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single y]
  · rw [one_sub_planeIdem_apply_of_not_mem hy]
    simp
  · intro z _ hzy
    rw [one_sub_planeIdem_apply_of_not_mem hy, if_neg hzy, mul_zero]
  · intro hy'
    exact absurd (Finset.mem_univ y) hy'

omit [Finite K] [CharP K 2] in
omit [Finite K] [CharP K 2] in
private lemma apply_of_mem_levi {S : Finset (Fin t)} {g : GL (LinIdx t ε) K}
    (h : g ∈ levi (planeIdem (K := K) t ε S true)) {y : LinIdx t ε}
    (hy : y ∉ zeroW t ε S) (x : LinIdx t ε) :
    (g : Matrix (LinIdx t ε) (LinIdx t ε) K) x y =
      (1 - planeIdem (K := K) t ε S true) x y := by
  have h1 : ((g : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
      (1 - planeIdem (K := K) t ε S true) = 1 - planeIdem (K := K) t ε S true := h.1
  have := congrFun (congrFun h1 x) y
  rwa [mul_one_sub_apply_of_not_mem hy] at this

omit [Finite K] [CharP K 2] in
private lemma tau_apply_of_not_mem {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i, i ∉ S → u i = 0) {y : LinIdx t ε} (hy : y ∉ zeroW t ε S)
    (x : LinIdx t ε) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) x y =
      if x = y then 1 else 0 := by
  rcases y with ((i | i) | f)
  · have hi : i ∉ S := by
      intro hi
      exact hy (by simp [zeroW, hi])
    have hui : u i = 0 := hu i hi
    rcases x with ((j | j) | g)
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      simp [WitSpNs.plane_inl, WitSpNs.side_inl, hui, Matrix.SpecialLinearGroup.coe_one]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      simp [WitSpNs.plane_inl, WitSpNs.side_inr, hui, Matrix.SpecialLinearGroup.coe_one,
        Sum.inr_ne_inl]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₂₁]
      simp [Sum.inr_ne_inl]
  · have hi : i ∉ S := by
      intro hi
      exact hy (by simp [zeroW, hi])
    have hui : u i = 0 := hu i hi
    rcases x with ((j | j) | g)
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      simp [WitSpNs.plane_inr, WitSpNs.side_inl, hui, Matrix.SpecialLinearGroup.coe_one,
        Sum.inl_ne_inr]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      simp [WitSpNs.plane_inr, WitSpNs.side_inr, hui, Matrix.SpecialLinearGroup.coe_one]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₂₁]
      simp [Sum.inr_ne_inl]
  · exact absurd (by simp [zeroW] : (Sum.inr f : LinIdx t ε) ∈ zeroW t ε S) hy

omit [Finite K] [CharP K 2] in
private lemma one_sub_planeIdem_apply_of_mem_left {S : Finset (Fin t)} {x y : LinIdx t ε}
    (hx : x ∈ zeroW t ε S) :
    (1 - planeIdem (K := K) t ε S true) x y = 0 := by
  rw [Matrix.sub_apply, Matrix.one_apply, planeIdem_apply_eq]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, if_pos rfl, if_pos hx]
    simp
  · rw [if_neg hxy, if_neg hxy]
    simp

omit [Finite K] [CharP K 2] in
private lemma mul_one_sub_apply_of_mem_left {S : Finset (Fin t)}
    {T : Matrix (LinIdx t ε) (LinIdx t ε) K} {x : LinIdx t ε}
    (hx : x ∈ zeroW t ε S) (y : LinIdx t ε) :
    ((1 - planeIdem (K := K) t ε S true) * T) x y = 0 := by
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun z _ => by
    rw [one_sub_planeIdem_apply_of_mem_left hx, zero_mul]

omit [Finite K] [CharP K 2] in
private lemma tau_apply_of_not_mem_left {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i, i ∉ S → u i = 0) {x : LinIdx t ε} (hx : x ∉ zeroW t ε S)
    (y : LinIdx t ε) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) x y =
      if x = y then 1 else 0 := by
  rcases x with ((i | i) | f)
  · have hi : i ∉ S := by
      intro hi
      exact hx (by simp [zeroW, hi])
    have hui : u i = 0 := hu i hi
    rcases y with ((j | j) | g)
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inl, hui]
      · simp [WitSpNs.plane_inl, hij]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inl, hui]
      · simp [WitSpNs.plane_inl, hij]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₂]
      simp [Sum.inl_ne_inr]
  · have hi : i ∉ S := by
      intro hi
      exact hx (by simp [zeroW, hi])
    have hui : u i = 0 := hu i hi
    rcases y with ((j | j) | g)
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inr, hui]
      · simp [WitSpNs.plane_inr, hij]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inr, hui]
      · simp [WitSpNs.plane_inr, hij]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₂]
      simp [Sum.inl_ne_inr]
  · exact absurd (by simp [zeroW] : (Sum.inr f : LinIdx t ε) ∈ zeroW t ε S) hx

omit [Finite K] [CharP K 2] in
omit [Finite K] [CharP K 2] in
private lemma tau_mem_levi_of_support {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i, i ∉ S → u i = 0) :
    tau ζ t ε u ∈ levi (planeIdem (K := K) t ε S true) := by
  constructor
  · ext x y
    by_cases hy : y ∈ zeroW t ε S
    · rw [mul_one_sub_apply_of_mem hy, one_sub_planeIdem_apply_of_mem hy]
    · rw [mul_one_sub_apply_of_not_mem hy, tau_apply_of_not_mem hu hy,
        one_sub_planeIdem_apply_of_not_mem hy]
  · ext x y
    by_cases hx : x ∈ zeroW t ε S
    · rw [mul_one_sub_apply_of_mem_left hx, one_sub_planeIdem_apply_of_mem_left hx]
    · rw [Matrix.mul_apply, Finset.sum_eq_single x]
      · rw [one_sub_planeIdem_apply_of_not_mem_left hx, if_pos rfl, one_mul,
          tau_apply_of_not_mem_left hu hx y, one_sub_planeIdem_apply_of_not_mem_left hx]
      · intro z _ hzx
        rw [one_sub_planeIdem_apply_of_not_mem_left hx, if_neg (Ne.symm hzx), zero_mul]
      · intro hx'
        exact absurd (Finset.mem_univ x) hx'

omit [Finite K] [CharP K 2] in
private lemma eq_zero_of_tau_mem_levi_lin {S : Finset (Fin t)}
    (hζ : Function.Injective ζ) {u : PlaneRaw.V t}
    (h : tau ζ t ε u ∈ levi (planeIdem (K := K) t ε S true)) :
    ∀ i, i ∉ S → u i = 0 := by
  intro i hi
  have hy0 : (Sum.inl (WitSpNs.coord 0 i) : LinIdx t ε) ∉ zeroW t ε S := by
    simp [zeroW, WitSpNs.coord, hi]
  have hy1 : (Sum.inl (WitSpNs.coord 1 i) : LinIdx t ε) ∉ zeroW t ε S := by
    simp [zeroW, WitSpNs.coord, hi]
  have h00 : ((ζ (Multiplicative.ofAdd (u i)) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h' := apply_of_mem_levi h hy0 (Sum.inl (WitSpNs.coord 0 i))
    rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_coord,
      one_sub_planeIdem_apply_of_not_mem hy0] at h'
    simpa using h'
  have h10 : ((ζ (Multiplicative.ofAdd (u i)) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have h' := apply_of_mem_levi h hy0 (Sum.inl (WitSpNs.coord 1 i))
    rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_coord,
      one_sub_planeIdem_apply_of_not_mem hy0] at h'
    simpa [WitSpNs.coord] using h'
  have h01 : ((ζ (Multiplicative.ofAdd (u i)) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have h' := apply_of_mem_levi h hy1 (Sum.inl (WitSpNs.coord 0 i))
    rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_coord,
      one_sub_planeIdem_apply_of_not_mem hy1] at h'
    simpa [WitSpNs.coord] using h'
  have h11 : ((ζ (Multiplicative.ofAdd (u i)) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have h' := apply_of_mem_levi h hy1 (Sum.inl (WitSpNs.coord 1 i))
    rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_coord,
      one_sub_planeIdem_apply_of_not_mem hy1] at h'
    simpa using h'
  have hB : ((ζ (Multiplicative.ofAdd (u i)) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [h00, h10, h01, h11]
  have hzeta : ζ (Multiplicative.ofAdd (u i)) = 1 := Subtype.ext hB
  have h1 : Multiplicative.ofAdd (u i) = 1 := hζ (by rw [hzeta, map_one])
  simpa using congrArg Multiplicative.toAdd h1

omit [Finite K] [CharP K 2] in
theorem ycode_zero_eq_blockGroup [Finite K] [CharP K 2] (hK : Nat.card K = 2) {S : Finset (Fin t)}
    (hS : 3 ≤ 2 * S.card + ε.val) :
    Ycode ζ t ε (PlaneRaw.Code.zero S) = blockGroup ζ t ε (PlaneRaw.Code.zero S) := by
  change ⁅levi (planeIdem (K := K) t ε S true), levi (planeIdem (K := K) t ε S true)⁆ =
    levi (planeIdem (K := K) t ε S true)
  exact levi_zero_perfect hK hS

omit [Finite K] [CharP K 2] in
theorem tau_mem_ycode_zero_iff [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ)
    {S : Finset (Fin t)} (hS : 3 ≤ 2 * S.card + ε.val) (u : PlaneRaw.V t) :
    tau ζ t ε u ∈ Ycode ζ t ε (PlaneRaw.Code.zero S) ↔ u ∈ PlaneRaw.insideZero S := by
  rw [ycode_zero_eq_blockGroup hK hS]
  change tau ζ t ε u ∈ levi (planeIdem (K := K) t ε S true) ↔ u ∈ PlaneRaw.insideZero S
  rw [PlaneRaw.mem_insideZero']
  exact ⟨eq_zero_of_tau_mem_levi_lin hζ, tau_mem_levi_of_support⟩

omit [Finite K] in
private lemma sl2W_mul_self : (sl2W * sl2W : SpecialLinearGroup (Fin 2) K) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2W]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private def swapGL (i : Fin t) : GL (LinIdx t ε) K where
  val := Matrix.fromBlocks
    (WitSpNs.planeMat fun j => if j = i then
      ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)
      else (1 : Matrix (Fin 2) (Fin 2) K))
    (0 : Matrix (Fin t ⊕ Fin t) (Fin ε.val) K) (0 : Matrix (Fin ε.val) (Fin t ⊕ Fin t) K)
    (1 : Matrix (Fin ε.val) (Fin ε.val) K)
  inv := Matrix.fromBlocks
    (WitSpNs.planeMat fun j => if j = i then
      ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)
      else (1 : Matrix (Fin 2) (Fin 2) K))
    (0 : Matrix (Fin t ⊕ Fin t) (Fin ε.val) K) (0 : Matrix (Fin ε.val) (Fin t ⊕ Fin t) K)
    (1 : Matrix (Fin ε.val) (Fin ε.val) K)
  val_inv := by
    rw [Matrix.fromBlocks_multiply, WitSpNs.planeMat_mul]
    have h : (fun j : Fin t =>
        (if j = i then ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) else 1) *
        (if j = i then ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) else 1)) = fun _ => 1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [if_pos rfl, ← Matrix.SpecialLinearGroup.coe_mul, sl2W_mul_self,
          Matrix.SpecialLinearGroup.coe_one]
      · simp [hj]
    rw [h]
    simp [WitSpNs.planeMat_one, Matrix.fromBlocks_one]
  inv_val := by
    rw [Matrix.fromBlocks_multiply, WitSpNs.planeMat_mul]
    have h : (fun j : Fin t =>
        (if j = i then ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) else 1) *
        (if j = i then ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) else 1)) = fun _ => 1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [if_pos rfl, ← Matrix.SpecialLinearGroup.coe_mul, sl2W_mul_self,
          Matrix.SpecialLinearGroup.coe_one]
      · simp [hj]
    rw [h]
    simp [WitSpNs.planeMat_one, Matrix.fromBlocks_one]

omit [Finite K] in
private lemma coe_swapGL (i : Fin t) :
    ((swapGL (K := K) (ε := ε) i : GL (LinIdx t ε) K) :
      Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks
        (WitSpNs.planeMat fun j => if j = i then
          ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K)
          else (1 : Matrix (Fin 2) (Fin 2) K))
        (0 : Matrix (Fin t ⊕ Fin t) (Fin ε.val) K) (0 : Matrix (Fin ε.val) (Fin t ⊕ Fin t) K)
        (1 : Matrix (Fin ε.val) (Fin ε.val) K) := rfl

omit [Finite K] [CharP K 2] in
private lemma planeMat_apply_of_not_mem {S : Finset (Fin t)}
    {B : Fin t → Matrix (Fin 2) (Fin 2) K} (hB : ∀ j, j ∉ S → B j = 1)
    {y : LinIdx t ε} (hy : y ∉ zeroW t ε S) (x : LinIdx t ε) :
    (Matrix.fromBlocks (WitSpNs.planeMat B) 0 0 1) x y = if x = y then 1 else 0 := by
  rcases y with ((i | i) | f)
  · have hi : i ∉ S := by
      intro hi
      exact hy (by simp [zeroW, hi])
    have hBi : B i = 1 := hB i hi
    rcases x with ((j | j) | g)
    · rw [Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      simp [WitSpNs.plane_inl, hBi]
    · rw [Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      simp [WitSpNs.plane_inl, hBi, Sum.inr_ne_inl]
    · rw [Matrix.fromBlocks_apply₂₁]
      simp [Sum.inr_ne_inl]
  · have hi : i ∉ S := by
      intro hi
      exact hy (by simp [zeroW, hi])
    have hBi : B i = 1 := hB i hi
    rcases x with ((j | j) | g)
    · rw [Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      simp [WitSpNs.plane_inr, hBi, Sum.inl_ne_inr]
    · rw [Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      simp [WitSpNs.plane_inr, hBi]
    · rw [Matrix.fromBlocks_apply₂₁]
      simp [Sum.inr_ne_inl]
  · exact absurd (by simp [zeroW] : (Sum.inr f : LinIdx t ε) ∈ zeroW t ε S) hy

omit [Finite K] [CharP K 2] in
private lemma planeMat_apply_of_not_mem_left {S : Finset (Fin t)}
    {B : Fin t → Matrix (Fin 2) (Fin 2) K} (hB : ∀ j, j ∉ S → B j = 1)
    {x : LinIdx t ε} (hx : x ∉ zeroW t ε S) (y : LinIdx t ε) :
    (Matrix.fromBlocks (WitSpNs.planeMat B) 0 0 1) x y = if x = y then 1 else 0 := by
  rcases x with ((i | i) | f)
  · have hi : i ∉ S := by
      intro hi
      exact hx (by simp [zeroW, hi])
    have hBi : B i = 1 := hB i hi
    rcases y with ((j | j) | g)
    · rw [Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inl, hBi]
      · simp [WitSpNs.plane_inl, hij]
    · rw [Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inl, WitSpNs.side_inr, hBi]
      · simp [WitSpNs.plane_inl, hij]
    · rw [Matrix.fromBlocks_apply₁₂]
      simp [Sum.inl_ne_inr]
  · have hi : i ∉ S := by
      intro hi
      exact hx (by simp [zeroW, hi])
    have hBi : B i = 1 := hB i hi
    rcases y with ((j | j) | g)
    · rw [Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inr, WitSpNs.side_inl, hBi]
      · simp [WitSpNs.plane_inr, hij]
    · rw [Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inr, hBi]
      · simp [WitSpNs.plane_inr, hij]
    · rw [Matrix.fromBlocks_apply₁₂]
      simp [Sum.inl_ne_inr]
  · exact absurd (by simp [zeroW] : (Sum.inr f : LinIdx t ε) ∈ zeroW t ε S) hx

omit [Finite K] [CharP K 2] in
private lemma mem_levi_of_fromBlocks_planeMat {S : Finset (Fin t)}
    {B : Fin t → Matrix (Fin 2) (Fin 2) K} (hB : ∀ j, j ∉ S → B j = 1)
    {g : GL (LinIdx t ε) K}
    (hg : (g : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (WitSpNs.planeMat B) 0 0 1) :
    g ∈ levi (planeIdem (K := K) t ε S true) := by
  constructor
  · ext x y
    rw [hg]
    by_cases hy : y ∈ zeroW t ε S
    · rw [mul_one_sub_apply_of_mem hy, one_sub_planeIdem_apply_of_mem hy]
    · rw [mul_one_sub_apply_of_not_mem hy, planeMat_apply_of_not_mem hB hy,
        one_sub_planeIdem_apply_of_not_mem hy]
  · ext x y
    rw [hg]
    by_cases hx : x ∈ zeroW t ε S
    · rw [mul_one_sub_apply_of_mem_left hx, one_sub_planeIdem_apply_of_mem_left hx]
    · rw [Matrix.mul_apply, Finset.sum_eq_single x]
      · rw [one_sub_planeIdem_apply_of_not_mem_left hx, if_pos rfl, one_mul,
          planeMat_apply_of_not_mem_left hB hx y, one_sub_planeIdem_apply_of_not_mem_left hx]
      · intro z _ hzx
        rw [one_sub_planeIdem_apply_of_not_mem_left hx, if_neg (Ne.symm hzx), zero_mul]
      · intro hx'
        exact absurd (Finset.mem_univ x) hx'

omit [Finite K] [CharP K 2] in
private lemma swapGL_mem_levi [CharP K 2] {S : Finset (Fin t)} {i : Fin t} (hi : i ∈ S) :
    swapGL (K := K) i ∈ levi (planeIdem (K := K) t ε S true) := by
  have hB : ∀ j : Fin t, j ∉ S →
      (if j = i then
        ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        else (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    intro j hj
    rw [if_neg]
    exact fun h => hj (h ▸ hi)
  exact mem_levi_of_fromBlocks_planeMat hB (coe_swapGL (K := K) (ε := ε) i)

private lemma tau_mul_swap_ne (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    {S : Finset (Fin t)} {u : PlaneRaw.V t} {i : Fin t} (_hi : i ∈ S) (hui : u i ≠ 0) :
    tau ζ t ε u * swapGL (K := K) i ≠ swapGL (K := K) i * tau ζ t ε u := by
  intro hcomm
  have hmat := congrArg (fun x : GL (LinIdx t ε) K =>
    (x : Matrix (LinIdx t ε) (LinIdx t ε) K)) hcomm
  rw [Units.val_mul, Units.val_mul, coe_tau_eq_fromBlocks_planeMat, coe_swapGL,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hmat
  rw [Matrix.fromBlocks_inj] at hmat
  obtain ⟨hleft, -, -, -⟩ := hmat
  rw [WitSpNs.planeMat_mul, WitSpNs.planeMat_mul] at hleft
  have hleft' : WitSpNs.planeMat (fun j =>
      ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) *
      (if j = i then ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) else 1)) =
      WitSpNs.planeMat (fun j =>
        (if j = i then ((sl2W (k := K) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) else 1) *
        ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) := by
    simpa using hleft
  have hfuneq := WitSpNs.planeMat_injective hleft'
  have hi' := congrFun hfuneq i
  have hcommSL : ζ (Multiplicative.ofAdd (u i)) * sl2W =
      sl2W * ζ (Multiplicative.ofAdd (u i)) := Subtype.ext (by simpa [if_true] using hi')
  have hcomm' : sl2W * ζ (Multiplicative.ofAdd (u i)) * sl2W⁻¹ =
      ζ (Multiplicative.ofAdd (u i)) := by
    rw [← hcommSL, mul_assoc, mul_inv_cancel, mul_one]
  rw [SpBlocks.sl2W_conj_eq_inv hK (SpBlocks.zeta_pow_three (u i))
    (SpBlocks.zeta_ne_one hζ hui)] at hcomm'
  have hBinv : (ζ (Multiplicative.ofAdd (u i)))⁻¹ = ζ (Multiplicative.ofAdd (u i)) := by
    simpa using hcomm'
  have h2 : ζ (Multiplicative.ofAdd (u i + u i)) = 1 := by
    rw [ofAdd_add, map_mul]
    nth_rewrite 2 [← hBinv]
    exact mul_inv_cancel (ζ (Multiplicative.ofAdd (u i)))
  have hne : u i + u i ≠ 0 := by
    revert hui
    generalize u i = a
    revert a
    decide
  exact SpBlocks.zeta_ne_one hζ hne h2

omit [Finite K] [CharP K 2] in
private lemma apply_of_mem_levi_left {S : Finset (Fin t)} {g : GL (LinIdx t ε) K}
    (h : g ∈ levi (planeIdem (K := K) t ε S true)) {x : LinIdx t ε}
    (hx : x ∉ zeroW t ε S) (y : LinIdx t ε) :
    (g : Matrix (LinIdx t ε) (LinIdx t ε) K) x y =
      (1 - planeIdem (K := K) t ε S true) x y := by
  have h2 : (1 - planeIdem (K := K) t ε S true) *
      ((g : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      1 - planeIdem (K := K) t ε S true := h.2
  have h' := congrFun (congrFun h2 x) y
  rw [Matrix.mul_apply, Finset.sum_eq_single x] at h'
  · rw [one_sub_planeIdem_apply_of_not_mem_left hx, if_pos rfl, one_mul] at h'
    exact h'
  · intro z _ hzx
    rw [one_sub_planeIdem_apply_of_not_mem_left hx, if_neg (Ne.symm hzx), zero_mul]
  · intro hx'
    exact absurd (Finset.mem_univ x) hx'

omit [Finite K] [CharP K 2] in
private lemma tau_apply_of_mem {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i, i ∈ S → u i = 0) {x y : LinIdx t ε}
    (hx : x ∈ zeroW t ε S) (hy : y ∈ zeroW t ε S) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) x y =
      if x = y then 1 else 0 := by
  rcases x with ((i | i) | f)
  · have hi : i ∈ S := by simpa [zeroW] using hx
    have hui : u i = 0 := hu i hi
    rcases y with ((j | j) | g)
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inl, hui]
      · simp [WitSpNs.plane_inl, hij]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inl, hui]
      · simp [WitSpNs.plane_inl, hij]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₂]
      simp [Sum.inl_ne_inr]
  · have hi : i ∈ S := by simpa [zeroW] using hx
    have hui : u i = 0 := hu i hi
    rcases y with ((j | j) | g)
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inr, hui]
      · simp [WitSpNs.plane_inr, hij]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply]
      by_cases hij : i = j
      · subst hij
        simp [WitSpNs.plane_inr, hui]
      · simp [WitSpNs.plane_inr, hij]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₂]
      simp [Sum.inl_ne_inr]
  · rcases y with ((j | j) | g)
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₂₁]
      simp [Sum.inr_ne_inl]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₂₁]
      simp [Sum.inr_ne_inl]
    · rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₂₂]
      simp [Matrix.one_apply]

private lemma mem_zeroW_inl {S : Finset (Fin t)} {a : Fin t ⊕ Fin t} :
    (Sum.inl a : LinIdx t ε) ∈ zeroW t ε S ↔ WitSpNs.plane a ∈ S := by
  rcases a with i | i <;> simp [zeroW, WitSpNs.plane]

private lemma not_mem_zeroW_inl {S : Finset (Fin t)} {a : Fin t ⊕ Fin t} :
    (Sum.inl a : LinIdx t ε) ∉ zeroW t ε S ↔ WitSpNs.plane a ∉ S := by
  rw [mem_zeroW_inl]

private lemma mem_zeroW_inr {S : Finset (Fin t)} (f : Fin ε.val) :
    (Sum.inr f : LinIdx t ε) ∈ zeroW t ε S := by
  simp [zeroW]

omit [Finite K] [CharP K 2] in
private lemma tau_apply_offplane {u : PlaneRaw.V t}
    {a b : Fin t ⊕ Fin t} (h : WitSpNs.plane a ≠ WitSpNs.plane b) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K)
      (Sum.inl a) (Sum.inl b) = 0 := by
  rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₁, WitSpNs.planeMat_apply, if_neg h]

omit [Finite K] [CharP K 2] in
private lemma tau_apply_inr_inl {u : PlaneRaw.V t}
    (f : Fin ε.val) (a : Fin t ⊕ Fin t) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K)
      (Sum.inr f) (Sum.inl a) = 0 := by
  rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₂₁]
  simp

omit [Finite K] [CharP K 2] in
private lemma tau_apply_inl_inr {u : PlaneRaw.V t}
    (a : Fin t ⊕ Fin t) (f : Fin ε.val) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K)
      (Sum.inl a) (Sum.inr f) = 0 := by
  rw [coe_tau_eq_fromBlocks_planeMat, Matrix.fromBlocks_apply₁₂]
  simp

omit [Finite K] [CharP K 2] in
private lemma reindex_levi_eq_blocks {S : Finset (Fin t)} {g : GL (LinIdx t ε) K}
    (hg : g ∈ levi (planeIdem (K := K) t ε S true)) :
    let W : Finset (LinIdx t ε) := zeroW t ε S
    let Wc := {x : LinIdx t ε // x ∉ W}
    let e : LinIdx t ε ≃ W ⊕ Wc := (Equiv.sumCompl (fun x => x ∈ W)).symm
    (reindexGL e g : Matrix (W ⊕ Wc) (W ⊕ Wc) K) =
      Matrix.fromBlocks ((reindexGL e g : Matrix (W ⊕ Wc) (W ⊕ Wc) K).toBlocks₁₁) 0 0 1 := by
  intro W Wc e
  rw [← Matrix.fromBlocks_toBlocks (reindexGL e g : Matrix (W ⊕ Wc) (W ⊕ Wc) K),
    Matrix.fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · ext i j
    change (reindexGL e g : Matrix (W ⊕ Wc) (W ⊕ Wc) K) (Sum.inl i) (Sum.inr j) = 0
    rw [coe_reindexGL, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inl i, Equiv.sumCompl_apply_inr j]
    have hj : j.1 ∉ zeroW t ε S := by simpa only [W] using j.2
    rw [apply_of_mem_levi hg hj, one_sub_planeIdem_apply_of_not_mem hj]
    have hne : i.1 ≠ j.1 := fun h => hj (h ▸ by simpa only [W] using i.2)
    simp [hne]
  · ext i j
    change (reindexGL e g : Matrix (W ⊕ Wc) (W ⊕ Wc) K) (Sum.inr i) (Sum.inl j) = 0
    rw [coe_reindexGL, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inr i, Equiv.sumCompl_apply_inl j]
    have hi : i.1 ∉ zeroW t ε S := by simpa only [W] using i.2
    rw [apply_of_mem_levi_left hg hi, one_sub_planeIdem_apply_of_not_mem_left hi]
    have hne : i.1 ≠ j.1 := fun h => hi (h ▸ by simpa only [W] using j.2)
    simp [hne]
  · ext i j
    change (reindexGL e g : Matrix (W ⊕ Wc) (W ⊕ Wc) K) (Sum.inr i) (Sum.inr j) =
      (1 : Matrix Wc Wc K) i j
    rw [coe_reindexGL, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inr i, Equiv.sumCompl_apply_inr j, Matrix.one_apply]
    have hj : j.1 ∉ zeroW t ε S := by simpa only [W] using j.2
    rw [apply_of_mem_levi hg hj, one_sub_planeIdem_apply_of_not_mem hj]
    by_cases hij : i = j
    · subst hij
      simp
    · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [hij, hij']

omit [Finite K] [CharP K 2] in
private lemma reindex_tau_eq_blocks_of_cent {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i, i ∈ S → u i = 0) :
    let W : Finset (LinIdx t ε) := zeroW t ε S
    let Wc := {x : LinIdx t ε // x ∉ W}
    let e : LinIdx t ε ≃ W ⊕ Wc := (Equiv.sumCompl (fun x => x ∈ W)).symm
    (reindexGL e (tau ζ t ε u) : Matrix (W ⊕ Wc) (W ⊕ Wc) K) =
      Matrix.fromBlocks 1 0 0
        ((reindexGL e (tau ζ t ε u) : Matrix (W ⊕ Wc) (W ⊕ Wc) K).toBlocks₂₂) := by
  intro W Wc e
  rw [← Matrix.fromBlocks_toBlocks (reindexGL e (tau ζ t ε u) : Matrix (W ⊕ Wc) (W ⊕ Wc) K),
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, rfl⟩
  · ext i j
    change (reindexGL e (tau ζ t ε u) : Matrix (W ⊕ Wc) (W ⊕ Wc) K) (Sum.inl i) (Sum.inl j) =
      (1 : Matrix W W K) i j
    rw [coe_reindexGL, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inl i, Equiv.sumCompl_apply_inl j, Matrix.one_apply]
    rw [tau_apply_of_mem hu (by simpa only [W] using i.2) (by simpa only [W] using j.2)]
    by_cases hij : i = j
    · subst hij
      simp
    · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [hij, hij']
  · ext i j
    change (reindexGL e (tau ζ t ε u) : Matrix (W ⊕ Wc) (W ⊕ Wc) K)
      (Sum.inl i) (Sum.inr j) = 0
    rw [coe_reindexGL, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inl i, Equiv.sumCompl_apply_inr j]
    have hi : i.1 ∈ zeroW t ε S := by simpa only [W] using i.2
    have hj : j.1 ∉ zeroW t ε S := by simpa only [W] using j.2
    rcases h : i.1 with a | f
    · rcases h2 : j.1 with b | g
      · have hS : WitSpNs.plane a ∈ S := by
          rw [← mem_zeroW_inl]
          rwa [h] at hi
        have hS' : WitSpNs.plane b ∉ S := by
          rw [← not_mem_zeroW_inl]
          rwa [h2] at hj
        rw [tau_apply_offplane (u := u) (a := a) (b := b) (h := by
          intro hEq
          exact hS' (hEq ▸ hS))]
      · exact absurd (by rw [h2]; exact mem_zeroW_inr g) hj
    · rcases h2 : j.1 with b | g
      · rw [tau_apply_inr_inl]
      · exact absurd (by rw [h2]; exact mem_zeroW_inr g) hj
  · ext i j
    change (reindexGL e (tau ζ t ε u) : Matrix (W ⊕ Wc) (W ⊕ Wc) K)
      (Sum.inr i) (Sum.inl j) = 0
    rw [coe_reindexGL, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    simp only [e, Equiv.symm_symm]
    rw [Equiv.sumCompl_apply_inr i, Equiv.sumCompl_apply_inl j]
    have hi : i.1 ∉ zeroW t ε S := by simpa only [W] using i.2
    have hj : j.1 ∈ zeroW t ε S := by simpa only [W] using j.2
    rcases h : i.1 with a | f
    · rcases h2 : j.1 with b | g
      · have hS : WitSpNs.plane a ∉ S := by
          rw [← not_mem_zeroW_inl]
          rwa [h] at hi
        have hS' : WitSpNs.plane b ∈ S := by
          rw [← mem_zeroW_inl]
          rwa [h2] at hj
        rw [tau_apply_offplane (u := u) (a := a) (b := b) (h := by
          intro hEq
          exact hS (hEq ▸ hS'))]
      · rw [tau_apply_inl_inr]
    · exact absurd (by rw [h]; exact mem_zeroW_inr f) hi

omit [Finite K] [CharP K 2] in
private lemma commute_tau_of_cent [CharP K 2] {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i, i ∈ S → u i = 0) {g : GL (LinIdx t ε) K}
    (hg : g ∈ levi (planeIdem (K := K) t ε S true)) :
    tau ζ t ε u * g = g * tau ζ t ε u := by
  let W : Finset (LinIdx t ε) := zeroW t ε S
  let Wc := {x : LinIdx t ε // x ∉ W}
  let e : LinIdx t ε ≃ W ⊕ Wc := (Equiv.sumCompl (fun x => x ∈ W)).symm
  have hgblocks := reindex_levi_eq_blocks hg
  have hublocks := reindex_tau_eq_blocks_of_cent (ζ := ζ) (t := t) (ε := ε) (S := S) hu
  apply (reindexGL e).injective
  rw [map_mul, map_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hgblocks, hublocks, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add]

theorem tau_commute_ycode_zero_iff (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    {S : Finset (Fin t)} (hS : 3 ≤ 2 * S.card + ε.val) (u : PlaneRaw.V t) :
    (∀ g ∈ Ycode ζ t ε (PlaneRaw.Code.zero S), tau ζ t ε u * g = g * tau ζ t ε u) ↔
      u ∈ PlaneRaw.centZero S := by
  rw [ycode_zero_eq_blockGroup hK hS]
  change (∀ g ∈ levi (planeIdem (K := K) t ε S true),
    tau ζ t ε u * g = g * tau ζ t ε u) ↔ u ∈ PlaneRaw.centZero S
  rw [PlaneRaw.mem_centZero]
  constructor
  · intro h i hi
    by_contra hui
    exact tau_mul_swap_ne hK hζ hi hui (h (swapGL (K := K) i) (swapGL_mem_levi hi))
  · intro hu g hg
    exact commute_tau_of_cent hu hg

end

end CFSG.StandardType.GGQ2Frame.LinBlocks

end
