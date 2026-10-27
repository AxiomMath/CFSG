module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlkFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlkSwap
public import CFSG.Sporadic.Suz.Setup

public section

open Matrix Module

namespace CFSG.StandardType

namespace WitSpBlk

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot WitClSp WitSpNs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable {K : Type} [Field K] {n : ℕ}

@[expose] def basisIdx {d : ℕ} (c : Fin d → Fin n) (x : Fin d ⊕ Fin d) : Fin n ⊕ Fin n :=
  Sum.swap (Sum.map c c x)

theorem plane_basisIdx {d : ℕ} (c : Fin d → Fin n) (x : Fin d ⊕ Fin d) :
    plane (basisIdx c x) = c (Sum.elim id id x) := by
  rcases x with k | k <;> rfl

theorem constr_apply_eq_zero {d e : ℕ} (b : Basis (Fin d ⊕ Fin d) K (Fin e → K))
    (c : Fin d → Fin n) (z : Fin e → K) {y : Fin n ⊕ Fin n} (hy : ∀ x, basisIdx c x ≠ y) :
    (b.constr K (fun x => (Pi.single (basisIdx c x) 1 : Fin n ⊕ Fin n → K)) z) y = 0 := by
  rw [Basis.constr_apply_fintype, Finset.sum_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Pi.smul_apply, Pi.single_eq_of_ne (hy x).symm, smul_zero]

theorem sumMap_blockSwap_castAdd {d : ℕ} (hdn : d + d ≤ n) (x : Fin d ⊕ Fin d) :
    Sum.map (blockSwap n d) (blockSwap n d)
        (basisIdx (fun k => Fin.castLE hdn (Fin.castAdd d k)) x) =
      basisIdx (fun k => Fin.castLE hdn (Fin.natAdd d k)) x := by
  rcases x with k | k <;>
    simp only [basisIdx, Sum.map_inl, Sum.map_inr, Sum.swap_inl, Sum.swap_inr, blockSwap_castAdd]

theorem exists_basisIdx_natAdd {d : ℕ} (hdn : d + d ≤ n) {t : Fin n ⊕ Fin n}
    (ht₁ : d ≤ (plane t : ℕ)) (ht₂ : (plane t : ℕ) < d + d) :
    ∃ x, basisIdx (fun k => Fin.castLE hdn (Fin.natAdd d k)) x = t := by
  rcases t with j | j
  · refine ⟨Sum.inr ⟨j - d, by simp at ht₁ ht₂; omega⟩, ?_⟩
    simp only [basisIdx, Sum.map_inr, Sum.swap_inr, Sum.inl.injEq]
    ext
    simp only [Fin.val_castLE, Fin.val_natAdd]
    simp at ht₁
    omega
  · refine ⟨Sum.inl ⟨j - d, by simp at ht₁ ht₂; omega⟩, ?_⟩
    simp only [basisIdx, Sum.map_inl, Sum.swap_inl, Sum.inr.injEq]
    ext
    simp only [Fin.val_castLE, Fin.val_natAdd]
    simp at ht₁
    omega

theorem mulVec_single_of_mem_suppGroup {S : Set (Fin n ⊕ Fin n)} (hS : ParClosed S)
    {x : StatedSp n K} (hx : x ∈ suppGroup S) {t : Fin n ⊕ Fin n} (ht : t ∉ S) :
    mat n K x *ᵥ Pi.single t 1 = Pi.single t 1 := by
  funext a
  rw [← mat_apply_eq_mulVec, (mem_suppGroup_iff hS).mp hx t ht a, Matrix.one_apply,
    Pi.single_apply]

theorem exists_block_conj {e s r : ℕ} {A₀ : GL (Fin n ⊕ Fin n) K}
    {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {C : Matrix (Fin e) (Fin e) K}
    (hC : IsUnit (C - 1))
    (hreal : ∀ k : Fin s → ℕ, ∃ X : StatedSp n K, RootPlaneSp.SpBlockMat A₀ ε C X k)
    (hN : BlockNormalMat K C) {i₀ i₁ : Fin s} (h01 : i₀ ≠ i₁) {X X' : StatedSp n K}
    (hX : RootPlaneSp.SpBlockMat A₀ ε C X (Pi.single i₀ 1))
    (hX' : RootPlaneSp.SpBlockMat A₀ ε C X' (Pi.single i₁ 1)) :
    ∃ d : ℕ, d + d = e ∧ ∃ A₁ X₀ : StatedSp n K, X₀ ∈ suppGroup (blockCoords n d 0) ∧
      A₁ * X₀ * A₁⁻¹ = X ∧
      A₁ * (permSp K (blockSwap n d) * X₀ * (permSp K (blockSwap n d))⁻¹) * A₁⁻¹ = X' := by
  classical
  have hnd₀ := blockForm_nondegenerate hC hreal i₀
  have hnd₁ := blockForm_nondegenerate hC hreal i₁
  obtain ⟨Φ, hΦC, hΦ⟩ := hN _ _ (blockForm_isAlt i₀) (blockForm_isAlt i₁) hnd₀ hnd₁
    (blockForm_mulVec hreal i₀) (blockForm_mulVec hreal i₁)
  have hΦinj : Function.Injective (Φ *ᵥ ·) := by
    intro z z' h
    rw [← sub_eq_zero]
    refine hnd₀.1 _ fun y => ?_
    rw [LinearMap.map_sub₂, ← hΦ, ← hΦ]
    change blockForm A₀ ε i₁ (Φ *ᵥ z) (Φ *ᵥ y) - blockForm A₀ ε i₁ (Φ *ᵥ z') (Φ *ᵥ y) = 0
    rw [show Φ *ᵥ z = Φ *ᵥ z' from h, sub_self]
  have hΦsurj : Function.Surjective (Φ *ᵥ ·) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hΦinj)
  obtain ⟨d, b, hb⟩ := (blockForm_isAlt (A₀ := A₀) (ε := ε) i₀).exists_basis_toMatrix_eq_J hnd₀
  have hbJ : ∀ x y, blockForm A₀ ε i₀ (b x) (b y) = Matrix.J (Fin d) K x y := fun x y => by
    rw [← hb, LinearMap.BilinForm.toMatrix_apply]
  have hde : d + d = e := by
    have := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun] at this
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hcard : n + n = e * s + r := by
    have := Fintype.card_congr ε
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at this
    exact this
  have hs2 : 2 ≤ s := by
    have h0 := i₀.isLt
    have h1 := i₁.isLt
    have : (i₀ : ℕ) ≠ i₁ := fun h => h01 (Fin.ext h)
    omega
  have hdn : d + d ≤ n := by
    have := Nat.mul_le_mul_left e hs2
    omega
  refine ⟨d, hde, ?_⟩
  set c : Fin d → Fin n := fun k => Fin.castLE hdn (Fin.castAdd d k) with hc
  set c' : Fin d → Fin n := fun k => Fin.castLE hdn (Fin.natAdd d k) with hc'
  set emb₀ : (Fin e → K) →ₗ[K] (Fin n ⊕ Fin n → K) := (frameΦ A₀ ε).toLinearMap ∘ₗ
    LinearMap.inl K _ _ ∘ₗ LinearMap.single K (fun _ : Fin s => Fin e → K) i₀ with hemb₀d
  set emb₁ : (Fin e → K) →ₗ[K] (Fin n ⊕ Fin n → K) := (frameΦ A₀ ε).toLinearMap ∘ₗ
    LinearMap.inl K _ _ ∘ₗ LinearMap.single K (fun _ : Fin s => Fin e → K) i₁ ∘ₗ
      Matrix.toLin' Φ with hemb₁d
  have hemb₀ : ∀ z, emb₀ z = frameΦ A₀ ε (Pi.single i₀ z, 0) := fun z => rfl
  have hemb₁ : ∀ z, emb₁ z = frameΦ A₀ ε (Pi.single i₁ (Φ *ᵥ z), 0) := fun z => by
    simp only [hemb₁d, LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.inl_apply,
      LinearMap.coe_single, LinearEquiv.coe_coe]
  have hf00 : ∀ z z', form (emb₀ z) (emb₀ z') = blockForm A₀ ε i₀ z z' := fun z z' => by
    rw [hemb₀, hemb₀, blockForm_apply]
  have hf11 : ∀ z z', form (emb₁ z) (emb₁ z') = blockForm A₀ ε i₀ z z' := fun z z' => by
    rw [hemb₁, hemb₁, ← blockForm_apply, hΦ]
  have hf01 : ∀ z z', form (emb₀ z) (emb₁ z') = 0 := fun z z' => by
    rw [hemb₀, hemb₁, form_frameΦ_single hC hreal, Pi.single_eq_of_ne h01, LinearMap.map_zero]
  have hf10 : ∀ z z', form (emb₁ z) (emb₀ z') = 0 := fun z z' => by
    rw [hemb₀, hemb₁, form_frameΦ_single hC hreal, Pi.single_eq_of_ne (Ne.symm h01),
      LinearMap.map_zero]
  have hJ1 : ∀ k l : Fin d, Matrix.J (Fin d) K (Sum.inr k) (Sum.inl l) =
      if k = l then 1 else 0 := fun k l => by
    simp [Matrix.J, Matrix.one_apply]
  have hJ2 : ∀ k l : Fin d, Matrix.J (Fin d) K (Sum.inr k) (Sum.inr l) = 0 := fun k l => by
    simp [Matrix.J]
  have hJ3 : ∀ k l : Fin d, Matrix.J (Fin d) K (Sum.inl k) (Sum.inl l) = 0 := fun k l => by
    simp [Matrix.J]
  have hfam₀ : IsSpFamily (fun k => emb₀ (b (Sum.inr k))) (fun k => emb₀ (b (Sum.inl k))) :=
    ⟨fun k l => by rw [hf00, hbJ, hJ1], fun k l => by rw [hf00, hbJ, hJ2],
      fun k l => by rw [hf00, hbJ, hJ3]⟩
  have hfam₁ : IsSpFamily (fun k => emb₁ (b (Sum.inr k))) (fun k => emb₁ (b (Sum.inl k))) :=
    ⟨fun k l => by rw [hf11, hbJ, hJ1], fun k l => by rw [hf11, hbJ, hJ2],
      fun k l => by rw [hf11, hbJ, hJ3]⟩
  obtain ⟨A₁, hA₁⟩ := exists_sp_of_family hdn (hfam₀.append hfam₁ (fun _ _ => hf01 _ _)
    (fun _ _ => hf01 _ _) (fun _ _ => hf01 _ _) (fun _ _ => hf01 _ _))
  have hcol₀ : ∀ k, mat n K A₁ *ᵥ Pi.single (Sum.inl (c k)) 1 = emb₀ (b (Sum.inr k)) ∧
      mat n K A₁ *ᵥ Pi.single (Sum.inr (c k)) 1 = emb₀ (b (Sum.inl k)) := fun k => by
    have := hA₁ (Fin.castAdd d k)
    simp only [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl] at this
    exact this
  have hcol₁ : ∀ k, mat n K A₁ *ᵥ Pi.single (Sum.inl (c' k)) 1 = emb₁ (b (Sum.inr k)) ∧
      mat n K A₁ *ᵥ Pi.single (Sum.inr (c' k)) 1 = emb₁ (b (Sum.inl k)) := fun k => by
    have := hA₁ (Fin.natAdd d k)
    simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr] at this
    exact this
  set κ₀ := b.constr K (fun x => (Pi.single (basisIdx c x) 1 : Fin n ⊕ Fin n → K)) with hκ₀
  set κ₁ := b.constr K (fun x => (Pi.single (basisIdx c' x) 1 : Fin n ⊕ Fin n → K)) with hκ₁
  have hAκ₀ : ∀ z, mat n K A₁ *ᵥ κ₀ z = emb₀ z := by
    have : (Matrix.toLin' (mat n K A₁)) ∘ₗ κ₀ = emb₀ := b.ext fun x => by
      rw [LinearMap.comp_apply, hκ₀, Basis.constr_basis, Matrix.toLin'_apply]
      rcases x with k | k
      · exact (hcol₀ k).2
      · exact (hcol₀ k).1
    intro z
    rw [← this, LinearMap.comp_apply, Matrix.toLin'_apply]
  have hAκ₁ : ∀ z, mat n K A₁ *ᵥ κ₁ z = emb₁ z := by
    have : (Matrix.toLin' (mat n K A₁)) ∘ₗ κ₁ = emb₁ := b.ext fun x => by
      rw [LinearMap.comp_apply, hκ₁, Basis.constr_basis, Matrix.toLin'_apply]
      rcases x with k | k
      · exact (hcol₁ k).2
      · exact (hcol₁ k).1
    intro z
    rw [← this, LinearMap.comp_apply, Matrix.toLin'_apply]
  set P := permSp K (blockSwap n d) with hP
  have hPκ : ∀ z, mat n K P *ᵥ κ₀ z = κ₁ z := by
    have : (Matrix.toLin' (mat n K P)) ∘ₗ κ₀ = κ₁ := b.ext fun x => by
      rw [LinearMap.comp_apply, hκ₀, hκ₁, Basis.constr_basis, Basis.constr_basis,
        Matrix.toLin'_apply, hP, mat_permSp_mulVec_single, sumMap_blockSwap_castAdd]
    intro z
    rw [← this, LinearMap.comp_apply, Matrix.toLin'_apply]
  have hAinv : ∀ z w, mat n K A₁ *ᵥ z = w → mat n K A₁⁻¹ *ᵥ w = z := fun z w h => by
    rw [← h, mulVec_inv_mulVec]
  set X₀ := A₁⁻¹ * X * A₁ with hX₀
  set Y := A₁⁻¹ * X' * A₁ with hY
  have hX₀col : ∀ v, mat n K X *ᵥ (mat n K A₁ *ᵥ v) = mat n K A₁ *ᵥ v →
      mat n K X₀ *ᵥ v = v := fun v h => by
    rw [hX₀, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h,
      mulVec_inv_mulVec]
  have hYcol : ∀ v, mat n K X' *ᵥ (mat n K A₁ *ᵥ v) = mat n K A₁ *ᵥ v →
      mat n K Y *ᵥ v = v := fun v h => by
    rw [hY, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h,
      mulVec_inv_mulVec]
  have hκ₀t : ∀ z (t : Fin n ⊕ Fin n), d ≤ (plane t : ℕ) → form (κ₀ z) (Pi.single t 1) = 0 := by
    intro z t ht
    rw [form_single_right, constr_apply_eq_zero b c z fun x h => ?_, zero_mul]
    have h1 := congrArg (fun a => (plane a : ℕ)) h
    simp only [plane_basisIdx, plane_par, hc, Fin.val_castLE, Fin.val_castAdd] at h1
    have := (Sum.elim id id x).isLt
    omega
  have hκ₁t : ∀ z (t : Fin n ⊕ Fin n), ((plane t : ℕ) < d ∨ d + d ≤ (plane t : ℕ)) →
      form (κ₁ z) (Pi.single t 1) = 0 := by
    intro z t ht
    rw [form_single_right, constr_apply_eq_zero b c' z fun x h => ?_, zero_mul]
    have h1 := congrArg (fun a => (plane a : ℕ)) h
    simp only [plane_basisIdx, plane_par, hc', Fin.val_castLE, Fin.val_natAdd] at h1
    have := (Sum.elim id id x).isLt
    omega
  have hX₀mem : X₀ ∈ suppGroup (blockCoords n d 0) := by
    rw [mem_suppGroup_iff (parClosed_blockCoords n d 0)]
    intro t ht a
    have hpt : d ≤ (plane t : ℕ) := by
      by_contra hlt
      exact ht ⟨by simp, by simpa using (not_le.mp hlt)⟩
    rw [mat_apply_eq_mulVec, hX₀col _ (fix_of_orth hC hreal hX fun z => ?_), Pi.single_apply,
      Matrix.one_apply]
    rw [← hemb₀, ← hAκ₀, form_mulVec, hκ₀t z t hpt]
  have hYmem : Y ∈ suppGroup (blockCoords n d 1) := by
    rw [mem_suppGroup_iff (parClosed_blockCoords n d 1)]
    intro t ht a
    have hpt : (plane t : ℕ) < d ∨ d + d ≤ (plane t : ℕ) := by
      by_contra hcon
      push Not at hcon
      exact ht ⟨by simpa using hcon.1, by simp only [Nat.reduceAdd]; omega⟩
    rw [mat_apply_eq_mulVec, hYcol _ (fix_of_orth hC hreal hX' fun z => ?_), Pi.single_apply,
      Matrix.one_apply]
    obtain ⟨z', rfl⟩ := hΦsurj z
    rw [← hemb₁, ← hAκ₁, form_mulVec, hκ₁t z' t hpt]
  have hPX₀mem : P * X₀ * P⁻¹ ∈ suppGroup (blockCoords n d 1) :=
    suppGroup_mono (image_blockCoords_zero (by omega))
      (conj_permSp_mem_suppGroup (K := K) (blockSwap n d) hX₀mem)
  have hcolEq : ∀ t, mat n K (P * X₀ * P⁻¹) *ᵥ Pi.single t 1 = mat n K Y *ᵥ Pi.single t 1 := by
    intro t
    by_cases ht : t ∈ blockCoords n d 1
    · have ht₁ : d ≤ (plane t : ℕ) := by simpa using ht.1
      have ht₂ : (plane t : ℕ) < d + d := by
        have := ht.2
        omega
      obtain ⟨x, rfl⟩ := exists_basisIdx_natAdd hdn ht₁ ht₂
      have hPinv : mat n K P⁻¹ *ᵥ Pi.single (basisIdx c' x) 1 = Pi.single (basisIdx c x) 1 := by
        have h1 : mat n K P *ᵥ Pi.single (basisIdx c x) 1 = Pi.single (basisIdx c' x) 1 := by
          rw [hP, mat_permSp_mulVec_single, sumMap_blockSwap_castAdd]
        rw [← h1, mulVec_inv_mulVec]
      have hκ₀b : κ₀ (b x) = Pi.single (basisIdx c x) 1 := Basis.constr_basis _ _ _ _
      have hκ₁b : κ₁ (b x) = Pi.single (basisIdx c' x) 1 := Basis.constr_basis _ _ _ _
      have hL : mat n K (P * X₀ * P⁻¹) *ᵥ Pi.single (basisIdx c' x) 1 = κ₁ (C *ᵥ b x) := by
        rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPinv, ← hκ₀b,
          hX₀, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAκ₀, hemb₀,
          mat_mulVec_frameΦ_same hX, ← hemb₀, ← hAκ₀, mulVec_inv_mulVec, hPκ]
      have hR : mat n K Y *ᵥ Pi.single (basisIdx c' x) 1 = κ₁ (C *ᵥ b x) := by
        rw [← hκ₁b, hY, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAκ₁,
          hemb₁, mat_mulVec_frameΦ_same hX', Matrix.mulVec_mulVec, ← hΦC, ← Matrix.mulVec_mulVec,
          ← hemb₁, ← hAκ₁, mulVec_inv_mulVec]
      rw [hL, hR]
    · rw [mulVec_single_of_mem_suppGroup (parClosed_blockCoords n d 1) hPX₀mem ht,
        mulVec_single_of_mem_suppGroup (parClosed_blockCoords n d 1) hYmem ht]
  have hPY : P * X₀ * P⁻¹ = Y := by
    apply mat_injective
    ext a t
    rw [mat_apply_eq_mulVec, mat_apply_eq_mulVec, hcolEq]
  refine ⟨A₁, X₀, hX₀mem, by rw [hX₀]; group, ?_⟩
  rw [hPY, hY]
  group

end WitSpBlk

end CFSG.StandardType
