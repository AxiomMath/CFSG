module

public import CFSG.Monster.B.Rep4371.Span

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B Matrix

variable (hoct : Model.octDataOK = true)

include hoct in
theorem Rraw_mem_V4 {k : ℕ} (hk : k < 4371) : Rraw k ∈ V4 Short.rStar := by
  rcases Nat.lt_or_ge k 23 with h | h
  · exact Across_le_V4 Short.isShortCoord_rStar (Rraw_mem_Across (by omega))
  rcases Nat.lt_or_ge k 2323 with h' | h'
  · have hm : Rraw k ∈ Xdiff Short.isShortCoord_rStar := by
      rw [← (xdiff_Rraw hoct).2.1]
      refine Submodule.subset_span ⟨⟨k - 23, by omega⟩, ?_⟩
      show Rraw (23 + (k - 23)) = Rraw k
      rw [show 23 + (k - 23) = k by omega]
    exact Xdiff_le_V4 Short.isShortCoord_rStar hm
  · exact Tplus_le_V4 Short.isShortCoord_rStar (Rraw_mem_Tplus h')

include hoct in
theorem span_Rraw :
    Submodule.span ℚ (Set.range fun k : Fin 4371 => Rraw k) = V4 Short.rStar := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Rraw_mem_V4 hoct k.2
  · rw [V4_eq_sup Short.isShortCoord_rStar]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Across_le_span.trans
        (Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨⟨k, by omega⟩, rfl⟩))
    · rw [← (xdiff_Rraw hoct).2.1]
      exact Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨⟨23 + t, by omega⟩, rfl⟩)
    · exact Tplus_le_span.trans
        (Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨⟨2323 + t, by omega⟩, rfl⟩))

@[expose] def gR (k : ℕ) : ℚ := if k = 0 then 2 else if k ≤ 22 then 4 else 2

theorem gR_ne_zero (k : ℕ) : gR k ≠ 0 := by
  unfold gR
  split_ifs <;> norm_num

theorem bform_tbasis_sub (x₁ x₂ y₁ y₂ : TIdx) :
    bform (tbasis x₁ - tbasis x₂) (tbasis y₁ - tbasis y₂) =
      ((if x₁ = y₁ then tnorm x₁ else 0) - if x₁ = y₂ then tnorm x₁ else 0) -
        ((if x₂ = y₁ then tnorm x₂ else 0) - if x₂ = y₂ then tnorm x₂ else 0) := by
  simp only [map_sub, LinearMap.sub_apply, bform_tbasis]
  ring

theorem fin24_succ_pos {k : ℕ} (h1 : 1 ≤ k) (h22 : k ≤ 22) : (0 : Fin 24) < fin24 (k + 1) := by
  rw [Fin.lt_def, val_fin24 (by omega), Fin.val_zero]
  omega

theorem fin24_succ_gt_one {k : ℕ} (h1 : 1 ≤ k) (h22 : k ≤ 22) :
    (1 : Fin 24) < fin24 (k + 1) := by
  rw [Fin.lt_def, val_fin24 (by omega), Fin.val_one]
  omega

theorem Rraw_A_tbasis {k : ℕ} (h1 : 1 ≤ k) (h22 : k ≤ 22) :
    Rraw k = tbasis (.inr (.inl (ltPair 0 (fin24 (k + 1)) (fin24_succ_pos h1 h22), 0))) -
      tbasis (.inr (.inl (ltPair 1 (fin24 (k + 1)) (fin24_succ_gt_one h1 h22), 0))) := by
  rw [Rraw_A_eq h1 h22]
  exact rawA_eq_tbasis _ _

theorem ltPair_inj {i i' j j' : Fin 24} {h : i < j} {h' : i' < j'}
    (e : ltPair i j h = ltPair i' j' h') : i = i' ∧ j = j' := by
  have := congrArg Subtype.val e
  simp only [ltPair, Prod.mk.injEq] at this
  exact this

theorem bform_Rraw_A {k l : ℕ} (hk : k ≤ 22) (hl : l ≤ 22) :
    bform (Rraw k) (Rraw l) = if k = l then gR k else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0 <;> rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rw [Rraw, ite_eq_left rfl, rawDiag_eq_tbasis, bform_tbasis_sub]
    simp [gR, tnorm]
    norm_num
  · rw [show Rraw 0 = rawDiag from rfl, rawDiag_eq_tbasis, Rraw_A_tbasis hl0 hl, bform_tbasis_sub]
    simp only [reduceCtorEq, ↓reduceIte, sub_self]
    rw [ite_eq_right (by omega)]
  · rw [show Rraw 0 = rawDiag from rfl, rawDiag_eq_tbasis, Rraw_A_tbasis hk0 hk, bform_tbasis_sub]
    simp only [reduceCtorEq, ↓reduceIte, sub_self]
    rw [ite_eq_right (by omega)]
  · rw [Rraw_A_tbasis hk0 hk, Rraw_A_tbasis hl0 hl, bform_tbasis_sub]
    by_cases hkl : k = l
    · subst hkl
      have hne : ltPair 1 (fin24 (k + 1)) (fin24_succ_gt_one hk0 hk) ≠
          ltPair 0 (fin24 (k + 1)) (fin24_succ_pos hk0 hk) :=
        fun h => absurd (ltPair_inj h).1 (by decide)
      simp [tnorm, hne, Ne.symm hne]
      rw [gR, ite_eq_right (by omega), ite_eq_left hk]
      norm_num
    · have hj : fin24 (k + 1) ≠ fin24 (l + 1) := fun h => by
        have := congrArg Fin.val h
        rw [val_fin24 (by omega), val_fin24 (by omega)] at this
        omega
      rw [ite_eq_right hkl]
      have e1 : ∀ (a b : Fin 24) (ha : a < fin24 (k + 1)) (hb : b < fin24 (l + 1)),
          (Sum.inr (Sum.inl (ltPair a (fin24 (k + 1)) ha, 0)) : TIdx) ≠
            Sum.inr (Sum.inl (ltPair b (fin24 (l + 1)) hb, 0)) := fun a b ha hb h => by
        have h' := congrArg (fun x : TIdx => match x with
          | .inr (.inl (p, _)) => (p : Fin 24 × Fin 24).2 | _ => 0) h
        exact hj h'
      rw [ite_eq_right (e1 _ _ _ _), ite_eq_right (e1 _ _ _ _), ite_eq_right (e1 _ _ _ _),
        ite_eq_right (e1 _ _ _ _)]
      ring

theorem dotProduct_single_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι} (h : a ≠ b) :
    ((Pi.single a (1 : ℚ) - Pi.single b (1 : ℚ) : ι → ℚ) ⬝ᵥ
      (Pi.single a (1 : ℚ) - Pi.single b (1 : ℚ) : ι → ℚ)) = 2 := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, single_dotProduct, single_dotProduct,
    single_dotProduct, single_dotProduct, Pi.single_apply, Pi.single_apply, Pi.single_apply,
    Pi.single_apply, ite_eq_left rfl, ite_eq_left rfl, ite_eq_right h, ite_eq_right (Ne.symm h)]
  norm_num

include hoct in
theorem bform_Rraw_X {k l : ℕ} (h1 : 23 ≤ k) (h2 : k ≤ 2322) (h1' : 23 ≤ l) (h2' : l ≤ 2322) :
    bform (Rraw k) (Rraw l) = if k = l then gR k else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl, gR, ite_eq_right (by omega), ite_eq_right (by omega),
      Rraw_xLab hoct h1 h2, Xlift_labelElt, Xlift_labelElt, bform_inX_inX']
    refine dotProduct_single_sub fun h => ?_
    have := (xLab_injective hoct h1 h2 h1 h2 (labelIdx_injective h)).2
    exact Bool.false_ne_true this
  · rw [ite_eq_right hkl]
    have h := (xdiff_Rraw hoct).2.2 (i := ⟨k - 23, by omega⟩) (j := ⟨l - 23, by omega⟩)
      (fun h => hkl (by have := congrArg Fin.val h; simp at this; omega))
    simp only at h
    rwa [show 23 + (k - 23) = k by omega, show 23 + (l - 23) = l by omega] at h

theorem bform_rawSpin (η η' : ZMod 2) (c c' : C₀) :
    bform (rawSpin η c) (rawSpin η' c') = if (η, c) = (η', c') then 2 else 0 := by
  rw [rawSpin, rawSpin, inW, inW, bform_tensor, E_dotProduct_E]
  have hw : wvec ⬝ᵥ wvec = 2 := by
    rw [wvec, dotProduct_single_sub (by decide : (0 : Fin 24) ≠ 1)]
  rw [hw]
  split_ifs <;> norm_num

theorem bform_Rraw_W {k l : ℕ} (h1 : 2323 ≤ k) (hk : k < 4371) (h1' : 2323 ≤ l) (hl : l < 4371) :
    bform (Rraw k) (Rraw l) = if k = l then gR k else 0 := by
  rw [Rraw_spin_eq h1, Rraw_spin_eq h1', bform_rawSpin]
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl, ite_eq_left rfl, gR, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right hkl, ite_eq_right]
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := oddC_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      (congrArg Prod.snd h)
    simp only at h1
    split_ifs at h1 with ha hb hb <;> first | exact absurd h1 (by decide) | omega

theorem Rraw_A_blocks {k : ℕ} (hk : k ≤ 22) : xs (Rraw k) = 0 ∧ Nm (Rraw k) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact ⟨rfl, rfl⟩
  · rw [Rraw_A_eq hk0 hk]
    exact ⟨rfl, rfl⟩

include hoct in
theorem Rraw_X_blocks {k : ℕ} (h1 : 23 ≤ k) (h2 : k ≤ 2322) : Am (Rraw k) = 0 ∧ Nm (Rraw k) = 0 := by
  rw [Rraw_xLab hoct h1 h2]
  exact ⟨rfl, rfl⟩

theorem Rraw_W_blocks {k : ℕ} (h1 : 2323 ≤ k) : Am (Rraw k) = 0 ∧ xs (Rraw k) = 0 := by
  rw [Rraw_spin_eq h1]
  exact ⟨rfl, rfl⟩

include hoct in
theorem bform_Rraw {k l : ℕ} (hk : k < 4371) (hl : l < 4371) :
    bform (Rraw k) (Rraw l) = if k = l then gR k else 0 := by
  rcases Nat.lt_or_ge k 23 with ka | ka <;> rcases Nat.lt_or_ge l 23 with la | la
  · exact bform_Rraw_A (by omega) (by omega)
  · rw [ite_eq_right (by omega)]
    rcases Nat.lt_or_ge l 2323 with lb | lb
    · exact bform_eq_zero_of_blocks (.inr (Rraw_X_blocks hoct la (by omega)).1)
        (.inl (Rraw_A_blocks (by omega)).1) (.inl (Rraw_A_blocks (by omega)).2)
    · exact bform_eq_zero_of_blocks (.inr (Rraw_W_blocks lb).1)
        (.inl (Rraw_A_blocks (by omega)).1) (.inl (Rraw_A_blocks (by omega)).2)
  · rw [ite_eq_right (by omega)]
    rcases Nat.lt_or_ge k 2323 with kb | kb
    · exact bform_eq_zero_of_blocks (.inl (Rraw_X_blocks hoct ka (by omega)).1)
        (.inr (Rraw_A_blocks (by omega)).1) (.inr (Rraw_A_blocks (by omega)).2)
    · exact bform_eq_zero_of_blocks (.inl (Rraw_W_blocks kb).1)
        (.inr (Rraw_A_blocks (by omega)).1) (.inr (Rraw_A_blocks (by omega)).2)
  · rcases Nat.lt_or_ge k 2323 with kb | kb <;> rcases Nat.lt_or_ge l 2323 with lb | lb
    · exact bform_Rraw_X hoct ka (by omega) la (by omega)
    · rw [ite_eq_right (by omega)]
      exact bform_eq_zero_of_blocks (.inl (Rraw_X_blocks hoct ka (by omega)).1)
        (.inr (Rraw_W_blocks lb).2) (.inl (Rraw_X_blocks hoct ka (by omega)).2)
    · rw [ite_eq_right (by omega)]
      exact bform_eq_zero_of_blocks (.inr (Rraw_X_blocks hoct la (by omega)).1)
        (.inl (Rraw_W_blocks kb).2) (.inr (Rraw_X_blocks hoct la (by omega)).2)
    · exact bform_Rraw_W kb hk lb hl

include hoct in
theorem linearIndependent_Rraw : LinearIndependent ℚ (fun k : Fin 4371 => Rraw k) :=
  LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := bform)
    (fun k l hkl => by
      change bform (Rraw k) (Rraw l) = 0
      rw [bform_Rraw hoct k.2 l.2, ite_eq_right (fun h => hkl (Fin.ext h))])
    (fun k => by
      rw [bform_Rraw hoct k.2 k.2, ite_eq_left rfl]
      exact gR_ne_zero k)

@[expose] noncomputable def RbasisOf : Module.Basis (Fin 4371) ℚ (V4 Short.rStar) :=
  (Module.Basis.span (linearIndependent_Rraw hoct)).map (LinearEquiv.ofEq _ _ (span_Rraw hoct))

theorem coe_RbasisOf (t : Fin 4371) : (RbasisOf hoct t : SpaceB) = Rraw t := by
  rw [RbasisOf, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]

include hoct in
theorem finrank_V4_rStar : Module.finrank ℚ (V4 Short.rStar) = 4371 := by
  rw [Module.finrank_eq_card_basis (RbasisOf hoct), Fintype.card_fin]

theorem toMatrix_eq_transpose {n : ℕ} {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (b : Module.Basis (Fin n) ℚ V) (f : V →ₗ[ℚ] V) (N : Matrix (Fin n) (Fin n) ℚ)
    (hN : ∀ t, f (b t) = ∑ u, N t u • b u) : LinearMap.toMatrix b b f = Nᵀ := by
  ext u t
  rw [LinearMap.toMatrix_apply, hN, Module.Basis.repr_sum_self, Matrix.transpose_apply]

theorem mul_gram_transpose {n : ℕ} (R : Fin n → SpaceB) (G : Matrix (Fin n) (Fin n) ℚ)
    (hG : ∀ t u, bform (R t) (R u) = G t u) (g : SpaceB →ₗ[ℚ] SpaceB)
    (hg : ∀ v w, bform (g v) (g w) = bform v w) (N : Matrix (Fin n) (Fin n) ℚ)
    (hN : ∀ t, g (R t) = ∑ u, N t u • R u) : N * G * Nᵀ = G := by
  ext t t'
  have h := hg (R t) (R t')
  rw [hN, hN, hG] at h
  rw [← h]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hG, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  ring

end CFSG.Monster.B.Rep4371
