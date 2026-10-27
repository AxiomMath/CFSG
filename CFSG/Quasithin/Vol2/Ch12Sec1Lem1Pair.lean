module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Par
public import CFSG.Quasithin.Vol2.KGFactH91

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open scoped Matrix

namespace PairStab

variable {n m : ℕ}

@[expose] def pairStab (x₀ y₀ : Fin n → ZMod 2) : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  VecStab.vecStab x₀ ⊓ (VecStab.vecStab y₀).comap (slGraphAut n (ZMod 2)).toMonoidHom

theorem mem_pairStab {x₀ y₀ : Fin n → ZMod 2} {g : SpecialLinearGroup (Fin n) (ZMod 2)} :
    g ∈ pairStab x₀ y₀ ↔ (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x₀ = x₀ ∧
      (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y₀ = y₀ :=
  Iff.rfl

theorem graph_mulVec_eq_iff {g : SpecialLinearGroup (Fin n) (ZMod 2)} {y : Fin n → ZMod 2} :
    (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y = y ↔
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ y = y := by
  rw [slGraphAut_matrix]
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [mulVec_mulVec, ← transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, transpose_one, one_mulVec]
  · exact VecStab.inv_transpose_mulVec_of

theorem graph_inv_mulVec_mulVec (s : SpecialLinearGroup (Fin n) (ZMod 2)) (y : Fin n → ZMod 2) :
    (slGraphAut n (ZMod 2) s⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      ((slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) = y := by
  rw [map_inv]
  exact VecStab.inv_mulVec_mulVec _ y

theorem map_conj (s : SpecialLinearGroup (Fin n) (ZMod 2)) (x y : Fin n → ZMod 2) :
    (pairStab x y).map (MulAut.conj s).toMonoidHom =
      pairStab ((s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)
        ((slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) := by
  ext g
  constructor
  · rintro ⟨a, ⟨ha₁, ha₂⟩, rfl⟩
    have ha₁' : (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x := ha₁
    have ha₂' : (slGraphAut n (ZMod 2) a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y = y := ha₂
    refine ⟨?_, ?_⟩
    · change ((s * a * s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ((s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = _
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← mulVec_mulVec, VecStab.inv_mulVec_mulVec, ← mulVec_mulVec, ha₁']
    · change (slGraphAut n (ZMod 2) (s * a * s⁻¹) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) = _
      rw [map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← mulVec_mulVec, graph_inv_mulVec_mulVec, ← mulVec_mulVec, ha₂']
  · rintro ⟨hg₁, hg₂⟩
    have hg₁' : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) =
        (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x := hg₁
    have hg₂' : (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) =
        (slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y := hg₂
    refine ⟨s⁻¹ * g * s, ⟨?_, ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    · change ((s⁻¹ * g * s : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← mulVec_mulVec, ← mulVec_mulVec, hg₁', VecStab.inv_mulVec_mulVec]
    · change (slGraphAut n (ZMod 2) (s⁻¹ * g * s) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y = y
      rw [map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← mulVec_mulVec, ← mulVec_mulVec, hg₂', graph_inv_mulVec_mulVec]

@[expose] noncomputable def levE (h : 1 + m = n) :
    SpecialLinearGroup (Fin m) (ZMod 2) →* SpecialLinearGroup (Fin n) (ZMod 2) :=
  (reindexSL (ZMod 2) h).toMonoidHom.comp (levR (ZMod 2) (Fin 1))

@[expose] def emb (h : 1 + m = n) (ξ : Fin m → ZMod 2) : Fin n → ZMod 2 :=
  (Sum.elim (0 : Fin 1 → ZMod 2) ξ) ∘ (sumEquiv h).symm

theorem levE_val (h : 1 + m = n) (D : SpecialLinearGroup (Fin m) (ZMod 2)) :
    (levE h D : Matrix (Fin n) (Fin n) (ZMod 2)) =
      reindex (sumEquiv h) (sumEquiv h) (fromBlocks 1 0 0 (D : Matrix (Fin m) (Fin m) (ZMod 2))) :=
  rfl

theorem levE_mulVec_comp (h : 1 + m = n) (D : SpecialLinearGroup (Fin m) (ZMod 2))
    (u : Fin 1 ⊕ Fin m → ZMod 2) :
    (levE h D : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ (u ∘ (sumEquiv h).symm) =
      ((fromBlocks 1 0 0 (D : Matrix (Fin m) (Fin m) (ZMod 2))) *ᵥ u) ∘ (sumEquiv h).symm := by
  rw [levE_val, reindex_apply, submatrix_mulVec_equiv]
  congr 2
  funext k
  simp

theorem levE_transpose_mulVec_comp (h : 1 + m = n) (D : SpecialLinearGroup (Fin m) (ZMod 2))
    (u : Fin 1 ⊕ Fin m → ZMod 2) :
    (levE h D : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ (u ∘ (sumEquiv h).symm) =
      ((fromBlocks 1 0 0 (D : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ) *ᵥ u) ∘ (sumEquiv h).symm := by
  rw [levE_val, transpose_reindex, fromBlocks_transpose, transpose_one, transpose_zero,
    transpose_zero, reindex_apply, submatrix_mulVec_equiv]
  congr 2
  funext k
  simp

theorem fromBlocks_mulVec_single (X : Matrix (Fin m) (Fin m) (ZMod 2)) :
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0 X) *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin m → ZMod 2) = Pi.single (Sum.inl 0) 1 := by
  rw [mulVec_single_one]
  funext k
  rcases k with i | j
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp [Matrix.col_apply]
  · simp [Matrix.col_apply]

theorem fromBlocks_mulVec_elim (X : Matrix (Fin m) (Fin m) (ZMod 2)) (ξ : Fin m → ZMod 2) :
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0 X) *ᵥ
      Sum.elim (0 : Fin 1 → ZMod 2) ξ = Sum.elim (0 : Fin 1 → ZMod 2) (X *ᵥ ξ) := by
  rw [fromBlocks_mulVec]
  congr 1
  · funext i
    simp
  · funext j
    simp

theorem levE_mulVec_e0 (h : 1 + m = n) (D : SpecialLinearGroup (Fin m) (ZMod 2)) :
    (levE h D : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = VecStab.e0 h := by
  rw [VecStab.e0_eq, levE_mulVec_comp, fromBlocks_mulVec_single]

theorem levE_transpose_mulVec_e0 (h : 1 + m = n) (D : SpecialLinearGroup (Fin m) (ZMod 2)) :
    (levE h D : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ VecStab.e0 h = VecStab.e0 h := by
  rw [VecStab.e0_eq, levE_transpose_mulVec_comp, fromBlocks_mulVec_single]

theorem levE_mulVec_emb (h : 1 + m = n) (D : SpecialLinearGroup (Fin m) (ZMod 2))
    (ξ : Fin m → ZMod 2) :
    (levE h D : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ emb h ξ =
      emb h ((D : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ ξ) := by
  rw [emb, levE_mulVec_comp, fromBlocks_mulVec_elim, emb]

theorem slGraphAut_levE (h : 1 + m = n) (D : SpecialLinearGroup (Fin m) (ZMod 2)) :
    slGraphAut n (ZMod 2) (levE h D) = levE h (slGraphAut m (ZMod 2) D) := by
  apply Subtype.ext
  have e1 : ((levE h D)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) = levE h D⁻¹ :=
    (map_inv _ _).symm
  rw [slGraphAut_matrix, e1, levE_val, levE_val, slGraphAut_matrix, transpose_reindex,
    fromBlocks_transpose, transpose_one, transpose_zero, transpose_zero]

theorem graph_levE_mulVec_emb (h : 1 + m = n) (D : SpecialLinearGroup (Fin m) (ZMod 2))
    (η : Fin m → ZMod 2) :
    (slGraphAut n (ZMod 2) (levE h D) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ emb h η =
      emb h ((slGraphAut m (ZMod 2) D : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ η) := by
  rw [slGraphAut_levE, levE_mulVec_emb]

theorem range_levE (h : 1 + m = n) : (levE h).range = pairStab (VecStab.e0 h) (VecStab.e0 h) := by
  ext g
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨levE_mulVec_e0 h D, graph_mulVec_eq_iff.mpr (levE_transpose_mulVec_e0 h D)⟩
  · rintro ⟨hg₁, hg₂⟩
    have hg₁' : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = VecStab.e0 h := hg₁
    have hg₂' := graph_mulVec_eq_iff.mp hg₂
    set M : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) (ZMod 2) :=
      ((reindexSL (ZMod 2) h).symm g : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) (ZMod 2)) with hM
    have hMg : reindex (sumEquiv h) (sumEquiv h) M = (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      have := congrArg Subtype.val ((reindexSL (ZMod 2) h).apply_symm_apply g)
      rwa [reindexSL_val] at this
    have hcol : ∀ k, M k (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin m → ZMod 2) k := by
      intro k
      have h1 := congrFun hg₁' (sumEquiv h k)
      rw [← hMg, reindex_apply, submatrix_mulVec_equiv, VecStab.e0_eq] at h1
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm] at h1
      have h2 : ((Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin m → ZMod 2) ∘ ⇑(sumEquiv h).symm) ∘
          ⇑(sumEquiv h) = Pi.single (Sum.inl 0) 1 := by
        funext j
        simp
      rw [h2, mulVec_single_one] at h1
      exact h1
    have hrow : ∀ k, M (Sum.inl 0) k = (Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin m → ZMod 2) k := by
      intro k
      have h1 := congrFun hg₂' (sumEquiv h k)
      rw [← hMg, transpose_reindex, reindex_apply, submatrix_mulVec_equiv, VecStab.e0_eq] at h1
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm] at h1
      have h2 : ((Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin m → ZMod 2) ∘ ⇑(sumEquiv h).symm) ∘
          ⇑(sumEquiv h) = Pi.single (Sum.inl 0) 1 := by
        funext j
        simp
      rw [h2, mulVec_single_one] at h1
      exact h1
    have hblocks : M = fromBlocks 1 0 0 M.toBlocks₂₂ := by
      conv_lhs => rw [← fromBlocks_toBlocks M]
      congr 1
      · funext i j
        have hi : i = 0 := Subsingleton.elim i 0
        have hj : j = 0 := Subsingleton.elim j 0
        subst hi hj
        simpa [toBlocks₁₁] using hcol (Sum.inl 0)
      · funext i j
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        simpa [toBlocks₁₂] using hrow (Sum.inr j)
      · funext i j
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        simpa [toBlocks₂₁] using hcol (Sum.inr i)
    have hdet : M.toBlocks₂₂.det = 1 := by
      have h1 : M.det = 1 := ((reindexSL (ZMod 2) h).symm g).prop
      rwa [hblocks, det_fromBlocks_zero₂₁, det_one, one_mul] at h1
    refine ⟨(⟨M.toBlocks₂₂, hdet⟩ : SpecialLinearGroup (Fin m) (ZMod 2)), Subtype.ext ?_⟩
    change reindex (sumEquiv h) (sumEquiv h) (fromBlocks 1 0 0 M.toBlocks₂₂) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2))
    rw [← hblocks, hMg]

theorem e0_eq_single (h : 1 + m = n) :
    VecStab.e0 h = Pi.single (⟨0, by omega⟩ : Fin n) 1 := by
  rw [VecStab.e0]
  congr 1

theorem exists_emb_of_dot (h : 1 + m = n) {x : Fin n → ZMod 2} (hx : x ⬝ᵥ VecStab.e0 h = 0) :
    ∃ ξ, x = emb h ξ := by
  refine ⟨x ∘ sumEquiv h ∘ Sum.inr, ?_⟩
  funext k
  obtain ⟨k', rfl⟩ := (sumEquiv h).surjective k
  rcases k' with i | j
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have h1 : x ⬝ᵥ VecStab.e0 h = x (sumEquiv h (Sum.inl 0)) := by
      rw [VecStab.e0, dotProduct_single, mul_one]
    rw [h1] at hx
    simp [emb, hx]
  · simp [emb]

theorem ne_zero_of_emb (h : 1 + m = n) {ξ : Fin m → ZMod 2} (hξ : emb h ξ ≠ 0) : ξ ≠ 0 := by
  rintro rfl
  apply hξ
  funext k
  obtain ⟨k', rfl⟩ := (sumEquiv h).surjective k
  rcases k' with i | j <;> simp [emb]

theorem exists_normal (h : 1 + m = n) (hm : 1 ≤ m) {x₀ y₀ : Fin n → ZMod 2}
    (hxy : y₀ ⬝ᵥ x₀ = 1) :
    ∃ s : SpecialLinearGroup (Fin n) (ZMod 2),
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = x₀ ∧
        (slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = y₀ := by
  have hx₀ : x₀ ≠ 0 := by
    rintro rfl
    rw [dotProduct_zero] at hxy
    exact zero_ne_one hxy
  have hy₀ : y₀ ≠ 0 := by
    rintro rfl
    rw [zero_dotProduct] at hxy
    exact zero_ne_one hxy
  obtain ⟨s, hs₁, hs₂⟩ := KGH91.exists_normal_form (by omega : 2 ≤ n) hx₀ hy₀
  rw [ite_eq_left hxy] at hs₂
  refine ⟨s, ?_, ?_⟩
  · rw [e0_eq_single h]
    exact hs₁
  · rw [e0_eq_single h]
    exact hs₂

theorem eq_map_levE (h : 1 + m = n) {x₀ y₀ : Fin n → ZMod 2}
    {s : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hs₁ : (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = x₀)
    (hs₂ : (slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = y₀) :
    pairStab x₀ y₀ = (levE h).range.map (MulAut.conj s).toMonoidHom := by
  rw [range_levE, map_conj, hs₁, hs₂]

theorem commutator_eq (h : 1 + m = n) (hm : 3 ≤ m) {x₀ y₀ : Fin n → ZMod 2}
    (hxy : y₀ ⬝ᵥ x₀ = 1) : ⁅pairStab x₀ y₀, pairStab x₀ y₀⁆ = pairStab x₀ y₀ := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_normal h (by omega) hxy
  rw [eq_map_levE h hs₁ hs₂, ← Subgroup.map_commutator]
  congr 1
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    VecStab.commutator_sl_eq_top hm]

theorem inv_mulVec_dot (h : 1 + m = n) {y₀ x : Fin n → ZMod 2}
    {s : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hs₂ : (slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = y₀) :
    ((s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x ⬝ᵥ
      VecStab.e0 h = x ⬝ᵥ y₀ := by
  rw [← hs₂, ← KGH91.dot_graph s, VecStab.mulVec_inv_mulVec]

theorem graph_inv_mulVec_dot (h : 1 + m = n) {x₀ y : Fin n → ZMod 2}
    {s : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hs₁ : (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ VecStab.e0 h = x₀) :
    (slGraphAut n (ZMod 2) s⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y ⬝ᵥ VecStab.e0 h =
      y ⬝ᵥ x₀ := by
  rw [← hs₁, dotProduct_comm, ← KGH91.dot_graph s, dotProduct_comm, map_inv,
    VecStab.mulVec_inv_mulVec]

theorem exists_mulVec (h : 1 + m = n) (hm : 1 ≤ m) {x₀ y₀ x x' : Fin n → ZMod 2}
    (hxy : y₀ ⬝ᵥ x₀ = 1) (hx : x ⬝ᵥ y₀ = 0) (hx' : x' ⬝ᵥ y₀ = 0) (hx0 : x ≠ 0) (hx'0 : x' ≠ 0) :
    ∃ g ∈ pairStab x₀ y₀, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x' := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_normal h hm hxy
  set si := ((s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
  obtain ⟨ξ, hξ⟩ := exists_emb_of_dot h (x := si *ᵥ x) (by rw [inv_mulVec_dot h hs₂, hx])
  obtain ⟨ξ', hξ'⟩ := exists_emb_of_dot h (x := si *ᵥ x') (by rw [inv_mulVec_dot h hs₂, hx'])
  have hne : ∀ {z : Fin n → ZMod 2}, z ≠ 0 → si *ᵥ z ≠ 0 := by
    intro z hz h0
    apply hz
    rw [← VecStab.mulVec_inv_mulVec s z, h0, mulVec_zero]
  obtain ⟨D, hD⟩ := Sec121Q.exists_sl_mulVec_eq (ne_zero_of_emb h (hξ ▸ hne hx0))
    (ne_zero_of_emb h (hξ' ▸ hne hx'0))
  refine ⟨s * levE h D * s⁻¹, ?_, ?_⟩
  · rw [eq_map_levE h hs₁ hs₂]
    exact ⟨levE h D, ⟨D, rfl⟩, rfl⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
      ← mulVec_mulVec, hξ, levE_mulVec_emb, hD, ← hξ', VecStab.mulVec_inv_mulVec]

theorem exists_dual (h : 1 + m = n) (hm : 1 ≤ m) {x₀ y₀ y y' : Fin n → ZMod 2}
    (hxy : y₀ ⬝ᵥ x₀ = 1) (hy : y ⬝ᵥ x₀ = 0) (hy' : y' ⬝ᵥ x₀ = 0) (hy0 : y ≠ 0) (hy'0 : y' ≠ 0) :
    ∃ g ∈ pairStab x₀ y₀,
      (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y = y' := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_normal h hm hxy
  have hback : ∀ z : Fin n → ZMod 2,
      (slGraphAut n (ZMod 2) s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((slGraphAut n (ZMod 2) s⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) = z := by
    intro z
    rw [map_inv]
    exact VecStab.mulVec_inv_mulVec _ z
  set si := (slGraphAut n (ZMod 2) s⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2)) with hsi
  obtain ⟨η, hη⟩ := exists_emb_of_dot h (x := si *ᵥ y) (by rw [graph_inv_mulVec_dot h hs₁, hy])
  obtain ⟨η', hη'⟩ := exists_emb_of_dot h (x := si *ᵥ y') (by
    rw [graph_inv_mulVec_dot h hs₁, hy'])
  have hne : ∀ {z : Fin n → ZMod 2}, z ≠ 0 → si *ᵥ z ≠ 0 := by
    intro z hz h0
    apply hz
    rw [← hback z, h0, mulVec_zero]
  obtain ⟨D, hD⟩ := Sec121Q.exists_sl_mulVec_eq (ne_zero_of_emb h (hη ▸ hne hy0))
    (ne_zero_of_emb h (hη' ▸ hne hy'0))
  obtain ⟨E, rfl⟩ : ∃ E, slGraphAut m (ZMod 2) E = D :=
    ⟨slGraphAut m (ZMod 2) D, VecStab.slGraphAut_slGraphAut D⟩
  refine ⟨s * levE h E * s⁻¹, ?_, ?_⟩
  · rw [eq_map_levE h hs₁ hs₂]
    exact ⟨levE h E, ⟨E, rfl⟩, rfl⟩
  · rw [map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← mulVec_mulVec, ← mulVec_mulVec, hη, graph_levE_mulVec_emb, hD, ← hη', hback]

theorem eq_of_mulVec_eq {g h : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hgh : ∀ ξ, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ξ =
      (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ξ) : g = h := by
  apply Subtype.ext
  ext i j
  have := congrFun (hgh (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem levE_injective (h : 1 + m = n) : Function.Injective (levE h) := by
  intro D D' hD
  have hr : ∀ X : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) (ZMod 2),
      reindex (sumEquiv h).symm (sumEquiv h).symm (reindex (sumEquiv h) (sumEquiv h) X) = X :=
    fun X => by rw [← reindex_symm, Equiv.symm_apply_apply]
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) (ZMod 2) =>
    reindex (sumEquiv h).symm (sumEquiv h).symm (g : Matrix (Fin n) (Fin n) (ZMod 2))) hD
  simp only [levE_val] at h1
  rw [hr, hr, fromBlocks_inj] at h1
  exact Subtype.ext h1.2.2.2

theorem emb_injective (h : 1 + m = n) : Function.Injective (emb h) := by
  intro ξ ξ' he
  funext j
  have := congrFun he (sumEquiv h (Sum.inr j))
  simpa [emb] using this

theorem emb_dot_e0 (h : 1 + m = n) (ξ : Fin m → ZMod 2) : emb h ξ ⬝ᵥ VecStab.e0 h = 0 := by
  rw [VecStab.e0, dotProduct_single, mul_one]
  simp [emb]

end PairStab

end CFSG.Quasithin.H13
