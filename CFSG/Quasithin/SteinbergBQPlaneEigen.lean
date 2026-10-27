module

public import CFSG.Quasithin.SteinbergBQPlaneRoots
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.SteinbergBQ

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

@[expose] def eigVec (A : Matrix (Fin 3) (Fin 3) F) (μ : F) : Submodule F (Fin 3 → F) where
  carrier := {v | A *ᵥ v = μ • v}
  add_mem' {v w} hv hw := by
    have h1 : A *ᵥ v = μ • v := hv
    have h2 : A *ᵥ w = μ • w := hw
    change A *ᵥ (v + w) = μ • (v + w)
    rw [mulVec_add, h1, h2, smul_add]
  zero_mem' := by
    change A *ᵥ 0 = μ • 0
    rw [mulVec_zero, smul_zero]
  smul_mem' c v hv := by
    have h1 : A *ᵥ v = μ • v := hv
    change A *ᵥ (c • v) = μ • (c • v)
    rw [mulVec_smul, h1, smul_comm]

theorem mem_eigVec {A : Matrix (Fin 3) (Fin 3) F} {μ : F} {v : Fin 3 → F} :
    v ∈ eigVec A μ ↔ A *ᵥ v = μ • v :=
  Iff.rfl

@[expose] def eigProj [NeZero p] (ζ : F) (T : Matrix (Fin 3) (Fin 3) F) (i : ZMod p) :
    Matrix (Fin 3) (Fin 3) F :=
  ∑ j : ZMod p, ζ⁻¹ ^ (i * j).val • T ^ j.val

theorem mul_eigProj [NeZero p] {ζ : F} (hζ0 : ζ ≠ 0) (hζ : ζ ^ p = 1)
    {T : Matrix (Fin 3) (Fin 3) F} (hT : T ^ p = 1) (i : ZMod p) :
    T * eigProj ζ T i = ζ ^ i.val • eigProj ζ T i := by
  have hζ' : ζ⁻¹ ^ p = 1 := by rw [inv_pow, hζ, inv_one]
  rw [eigProj, Finset.mul_sum, Finset.smul_sum]
  have hT1 : ∀ j : ZMod p, T * T ^ j.val = T ^ (j + 1).val := fun j => by
    rw [pow_val_add hT, ← Nat.cast_one, pow_val_natCast hT, pow_one, ← pow_succ', ← pow_succ]
  refine Fintype.sum_equiv (Equiv.addRight 1) _ _ fun j => ?_
  rw [Matrix.mul_smul, hT1, Equiv.coe_addRight, smul_smul]
  congr 1
  rw [mul_add, mul_one, pow_val_add hζ', ← mul_assoc, mul_comm (ζ ^ i.val), mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hζ0, one_pow, mul_one]

theorem sum_pow_val_eq_zero [NeZero p] (hp1 : 1 < p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    ∑ k : ZMod p, ζ ^ k.val = 0 := by
  rw [← hζ.geom_sum_eq_zero hp1]
  exact Finset.sum_nbij' ZMod.val Nat.cast (fun a _ => Finset.mem_range.2 (ZMod.val_lt a))
    (fun _ _ => Finset.mem_univ _) (fun a _ => ZMod.natCast_zmod_val a)
    (fun _ hn => ZMod.val_cast_of_lt (Finset.mem_range.1 hn)) fun _ _ => rfl

theorem sum_eigProj [NeZero p] [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (T : Matrix (Fin 3) (Fin 3) F) : ∑ i : ZMod p, eigProj ζ T i = (p : F) • 1 := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  simp only [eigProj]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (0 : ZMod p) (fun j _ hj0 => by
      have hs : ∑ i : ZMod p, ζ⁻¹ ^ (i * j).val = ∑ k : ZMod p, ζ⁻¹ ^ k.val :=
        Fintype.sum_equiv (Equiv.mulRight₀ j hj0) _ _ fun _ => rfl
      rw [hs, sum_pow_val_eq_zero hp1 hζ.inv, zero_smul])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [mul_zero, ZMod.val_zero, pow_zero, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mul_one]

theorem mem_iSup_eigVec [NeZero p] [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hpF : (p : F) ≠ 0) {T : Matrix (Fin 3) (Fin 3) F} (hT : T ^ p = 1)
    (W : Submodule F (Fin 3 → F)) (hW : ∀ w ∈ W, T *ᵥ w ∈ W) {v : Fin 3 → F} (hv : v ∈ W) :
    v ∈ ⨆ i : ZMod p, W ⊓ eigVec T (ζ ^ i.val) := by
  have hpow : ∀ (k : ℕ), ∀ w ∈ W, T ^ k *ᵥ w ∈ W := by
    intro k
    induction k with
    | zero => intro w hw; rwa [pow_zero, one_mulVec]
    | succ k ih => intro w hw; rw [pow_succ', ← mulVec_mulVec]; exact hW _ (ih w hw)
  have hv' : v = ∑ i : ZMod p, (p : F)⁻¹ • (eigProj ζ T i *ᵥ v) := by
    rw [← Finset.smul_sum, ← sum_mulVec, sum_eigProj hζ, smul_mulVec, one_mulVec, smul_smul,
      inv_mul_cancel₀ hpF, one_smul]
  rw [hv']
  refine Submodule.sum_mem _ fun i _ =>
    Submodule.mem_iSup_of_mem i (Submodule.mem_inf.2 ⟨W.smul_mem _ ?_, ?_⟩)
  · rw [eigProj, sum_mulVec]
    exact W.sum_mem fun j _ => by
      rw [smul_mulVec]
      exact W.smul_mem _ (hpow _ v hv)
  · rw [mem_eigVec, mulVec_smul, mulVec_mulVec, mul_eigProj (hζ.ne_zero (NeZero.ne p))
      hζ.pow_eq_one hT, smul_mulVec, smul_comm]

theorem mem_iSup_jointEig [NeZero p] [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hpF : (p : F) ≠ 0) {A B : Matrix (Fin 3) (Fin 3) F} (hA : A ^ p = 1) (hB : B ^ p = 1)
    (hAB : A * B = B * A) (v : Fin 3 → F) :
    v ∈ ⨆ i : ZMod p, ⨆ k : ZMod p, eigVec A (ζ ^ i.val) ⊓ eigVec B (ζ ^ k.val) := by
  have h1 := mem_iSup_eigVec hζ hpF hA ⊤ (fun _ _ => Submodule.mem_top) (Submodule.mem_top (x := v))
  refine (iSup_le fun i => ?_ : ⨆ i : ZMod p, (⊤ : Submodule F (Fin 3 → F)) ⊓
    eigVec A (ζ ^ i.val) ≤ _) h1
  intro w hw
  have hBinv : ∀ u ∈ eigVec A (ζ ^ i.val), B *ᵥ u ∈ eigVec A (ζ ^ i.val) := fun u hu => by
    rw [mem_eigVec, mulVec_mulVec, hAB, ← mulVec_mulVec, mem_eigVec.1 hu, mulVec_smul]
  have h2 := mem_iSup_eigVec hζ hpF hB (eigVec A (ζ ^ i.val)) hBinv hw.2
  exact le_iSup (fun i : ZMod p => ⨆ k : ZMod p, eigVec A (ζ ^ i.val) ⊓ eigVec B (ζ ^ k.val)) i h2

theorem diagonal_mulVec_single_one (e : Fin 3 → F) (m : Fin 3) :
    diagonal e *ᵥ Pi.single m 1 = e m • Pi.single m 1 := by
  funext j
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = m
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

theorem exists_joint_eigenbasis [Finite F] [NeZero p] [Fact p.Prime] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (hpF : (p : F) ≠ 0) {A B : Matrix (Fin 3) (Fin 3) F}
    (hA : A ^ p = 1) (hB : B ^ p = 1) (hAB : A * B = B * A) :
    ∃ (M M' : Matrix (Fin 3) (Fin 3) F) (α β : Fin 3 → ZMod p), M' * M = 1 ∧ M * M' = 1 ∧
      M' * A * M = diagPow ζ α ∧ M' * B * M = diagPow ζ β := by
  classical
  set S : Set (Fin 3 → F) := ⋃ i : ZMod p, ⋃ k : ZMod p,
    ((eigVec A (ζ ^ i.val) ⊓ eigVec B (ζ ^ k.val) : Submodule F (Fin 3 → F)) :
      Set (Fin 3 → F)) with hS
  have hspanS : Submodule.span F S = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h := mem_iSup_jointEig hζ hpF hA hB hAB v
    refine (iSup_le fun i => iSup_le fun k => ?_ : _ ≤ Submodule.span F S) h
    intro w hw
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨k, hw⟩⟩)
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent F S
  have : Fintype b := Fintype.ofFinite b
  let bb := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hspanS])
  have h3 : Fintype.card b = 3 := by
    rw [← Module.finrank_eq_card_basis bb, Module.finrank_fin_fun]
  let bb' := bb.reindex (Fintype.equivFinOfCardEq h3)
  have hmem : ∀ m, ∃ ik : ZMod p × ZMod p, A *ᵥ bb' m = ζ ^ ik.1.val • bb' m ∧
      B *ᵥ bb' m = ζ ^ ik.2.val • bb' m := fun m => by
    have h1 : bb' m ∈ S := by
      rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact hbS (Subtype.mem _)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h1
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hi
    exact ⟨(i, k), hk.1, hk.2⟩
  choose ik hik using hmem
  have hsymm : ∀ m, bb'.equivFun.symm (Pi.single m 1) = bb' m := fun m => by
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : j = m
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hfun : ∀ m, bb'.equivFun (bb' m) = Pi.single m 1 := fun m => by
    rw [← hsymm m, LinearEquiv.apply_symm_apply]
  set M := LinearMap.toMatrix' bb'.equivFun.symm.toLinearMap with hM
  set M' := LinearMap.toMatrix' bb'.equivFun.toLinearMap with hM'
  have hMe : ∀ m, M *ᵥ Pi.single m 1 = bb' m := fun m => by
    rw [hM, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe, hsymm]
  have hM'e : ∀ m, M' *ᵥ bb' m = Pi.single m 1 := fun m => by
    rw [hM', LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe, hfun]
  have hdiag : ∀ (T : Matrix (Fin 3) (Fin 3) F) (γ : Fin 3 → ZMod p),
      (∀ m, T *ᵥ bb' m = ζ ^ (γ m).val • bb' m) → M' * T * M = diagPow ζ γ := by
    intro T γ hT
    refine ext_of_mulVec_single fun m => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, hMe, hT, mulVec_smul, hM'e, diagPow,
      diagonal_mulVec_single_one]
  refine ⟨M, M', fun m => (ik m).1, fun m => (ik m).2, ?_, ?_, hdiag A _ fun m => (hik m).1,
    hdiag B _ fun m => (hik m).2⟩
  · rw [hM, hM', ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext fun v => bb'.equivFun.apply_symm_apply v
  · rw [hM, hM', ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext fun v => bb'.equivFun.symm_apply_apply v

theorem pairMat_nsmul (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F)
    (n : ℕ) (y : ZMod p × ZMod p) : pairMat φ (n • y) = pairMat φ y ^ n := by
  rw [pairMat, pairMat, ofAdd_nsmul, map_pow]
  rfl

theorem diagPow_nsmul [NeZero p] {ζ : F} (hζ : ζ ^ p = 1) (n : ℕ) (v : Fin 3 → ZMod p) :
    diagPow ζ (n • v) = diagPow ζ v ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, diagPow_zero]
  | succ n ih => rw [succ_nsmul, diagPow_add hζ, ih, pow_succ]

theorem mem_sumZeroPlane_of_det [NeZero p] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {v : Fin 3 → ZMod p} (h : (diagPow ζ v).det = 1) : v ∈ sumZeroPlane p := by
  rw [diagPow, det_diagonal, Fin.prod_univ_three, ← pow_add, ← pow_add,
    hζ.pow_eq_one_iff_dvd] at h
  have h1 := (ZMod.natCast_eq_zero_iff _ _).2 h
  push_cast at h1
  rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1

theorem conj_mul_conj {M M' : Matrix (Fin 3) (Fin 3) F} (hMM' : M * M' = 1)
    (X Y : Matrix (Fin 3) (Fin 3) F) : M' * X * M * (M' * Y * M) = M' * (X * Y) * M := by
  calc M' * X * M * (M' * Y * M) = M' * X * (M * M') * Y * M := by
        simp only [Matrix.mul_assoc]
    _ = M' * (X * Y) * M := by
        rw [hMM', Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem conj_pow_eq {M M' : Matrix (Fin 3) (Fin 3) F} (hM'M : M' * M = 1) (hMM' : M * M' = 1)
    (X : Matrix (Fin 3) (Fin 3) F) (n : ℕ) : (M' * X * M) ^ n = M' * X ^ n * M := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hM'M]
  | succ n ih => rw [pow_succ, ih, conj_mul_conj hMM', ← pow_succ]

theorem det_conj {M M' : Matrix (Fin 3) (Fin 3) F} (hM'M : M' * M = 1)
    (X : Matrix (Fin 3) (Fin 3) F) : (M' * X * M).det = X.det := by
  rw [det_mul, det_mul, mul_right_comm, ← det_mul, hM'M, det_one, one_mul]

theorem exists_conj_eq_diagPlane [Finite F] [NeZero p] [Fact p.Prime] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (hpF : (p : F) ≠ 0)
    (φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F)
    (hφ : Function.Injective φ) :
    ∃ M M' : Matrix (Fin 3) (Fin 3) F, M' * M = 1 ∧ M * M' = 1 ∧
      (∀ y, ∃ v : sumZeroPlane p, M' * pairMat φ y * M = diagPow ζ (v : Fin 3 → ZMod p)) ∧
      ∀ v : sumZeroPlane p, ∃ y, M' * pairMat φ y * M = diagPow ζ (v : Fin 3 → ZMod p) := by
  classical
  have hpz : ∀ y : ZMod p × ZMod p, p • y = 0 := fun y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  have hA : pairMat φ (1, 0) ^ p = 1 := by rw [← pairMat_nsmul, hpz, pairMat_zero]
  have hB : pairMat φ (0, 1) ^ p = 1 := by rw [← pairMat_nsmul, hpz, pairMat_zero]
  have hAB : pairMat φ (1, 0) * pairMat φ (0, 1) = pairMat φ (0, 1) * pairMat φ (1, 0) := by
    rw [← pairMat_add, ← pairMat_add, add_comm]
  obtain ⟨M, M', α, β, hM'M, hMM', hAα, hBβ⟩ := exists_joint_eigenbasis hζ hpF hA hB hAB
  have hαV : α ∈ sumZeroPlane p :=
    mem_sumZeroPlane_of_det hζ (by rw [← hAα, det_conj hM'M]; exact (φ _).2)
  have hβV : β ∈ sumZeroPlane p :=
    mem_sumZeroPlane_of_det hζ (by rw [← hBβ, det_conj hM'M]; exact (φ _).2)
  set α' : sumZeroPlane p := ⟨α, hαV⟩
  set β' : sumZeroPlane p := ⟨β, hβV⟩
  have hconj : ∀ y : ZMod p × ZMod p, M' * pairMat φ y * M =
      diagPow ζ ((y.1 • α' + y.2 • β' : sumZeroPlane p) : Fin 3 → ZMod p) := by
    intro y
    have hy : pairMat φ y = pairMat φ (1, 0) ^ y.1.val * pairMat φ (0, 1) ^ y.2.val := by
      rw [← pairMat_nsmul, ← pairMat_nsmul, ← pairMat_add]
      congr 1
      ext <;> simp
    rw [hy, ← conj_mul_conj hMM', ← conj_pow_eq hM'M hMM', ← conj_pow_eq hM'M hMM', hAα, hBβ,
      ← diagPow_nsmul hζ.pow_eq_one, ← diagPow_nsmul hζ.pow_eq_one, ← diagPow_add hζ.pow_eq_one]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ← Nat.cast_smul_eq_nsmul (ZMod p),
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rfl
  refine ⟨M, M', hM'M, hMM', fun y => ⟨_, hconj y⟩, fun v => ?_⟩
  let L : ZMod p × ZMod p → sumZeroPlane p := fun y => y.1 • α' + y.2 • β'
  have hcancel : ∀ X : Matrix (Fin 3) (Fin 3) F, X = M * (M' * X * M) * M' := fun X => by
    simp only [← Matrix.mul_assoc, hMM', Matrix.one_mul]
    rw [Matrix.mul_assoc, hMM', Matrix.mul_one]
  have hLinj : Function.Injective L := by
    intro y y' h
    have h1 : M' * pairMat φ y * M = M' * pairMat φ y' * M := by
      rw [hconj, hconj]
      exact congrArg (fun u : sumZeroPlane p => diagPow ζ (u : Fin 3 → ZMod p)) h
    have h2 : pairMat φ y = pairMat φ y' := by rw [hcancel (pairMat φ y), h1, ← hcancel]
    have h3 : φ (Multiplicative.ofAdd y) = φ (Multiplicative.ofAdd y') := Subtype.ext h2
    exact congrArg Multiplicative.toAdd (hφ h3)
  have hLbij : Function.Bijective L := hLinj.bijective_of_nat_card_le (by
    rw [card_sumZeroPlane, Nat.card_prod, Nat.card_zmod, sq])
  obtain ⟨y, hy⟩ := hLbij.2 v
  exact ⟨y, by
    rw [hconj]
    exact congrArg (fun u : sumZeroPlane p => diagPow ζ (u : Fin 3 → ZMod p)) hy⟩

end CFSG.Quasithin.SteinbergBQ
