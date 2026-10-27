module

public import CFSG.Quasithin.Background.RonanD35

public section

namespace CFSG.Quasithin.RonanD35

open CFSG.Quasithin CFSG.Open
open scoped Matrix

section Matrices

variable {K : Type} [Field K]

@[expose] def sp4Mat (S : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 1 S 0 1

theorem sp4Mat_mul (S S' : Matrix (Fin 2) (Fin 2) K) :
    sp4Mat S * sp4Mat S' = sp4Mat (S + S') := by
  simp only [sp4Mat, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  rw [add_comm S' S]

theorem sp4Mat_zero : sp4Mat (0 : Matrix (Fin 2) (Fin 2) K) = 1 :=
  Matrix.fromBlocks_one

theorem sp4Mat_mul_neg (S : Matrix (Fin 2) (Fin 2) K) : sp4Mat S * sp4Mat (-S) = 1 := by
  rw [sp4Mat_mul, add_neg_cancel, sp4Mat_zero]

theorem sp4Mat_mulVec (S : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 ⊕ Fin 2 → K) :
    sp4Mat S *ᵥ x = Sum.elim (x ∘ Sum.inl + S *ᵥ (x ∘ Sum.inr)) (x ∘ Sum.inr) := by
  simp only [sp4Mat, Matrix.fromBlocks_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]

theorem sp4Mat_mulVec_sub {S : Matrix (Fin 2) (Fin 2) K} (hS : IsUnit S.det) (x : Fin 2 → K) :
    sp4Mat S *ᵥ Sum.elim (0 : Fin 2 → K) (S⁻¹ *ᵥ x) - Sum.elim (0 : Fin 2 → K) (S⁻¹ *ᵥ x) =
      Sum.elim x 0 := by
  rw [sp4Mat_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_add, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hS, Matrix.one_mulVec]
  funext i
  rcases i with i | i
  · simp only [Pi.sub_apply, Sum.elim_inl, Pi.zero_apply, sub_zero]
  · simp only [Pi.sub_apply, Sum.elim_inr, sub_self, Pi.zero_apply]

theorem sp4Mat_symplectic {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    (sp4Mat S)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sp4Mat S = Matrix.fromBlocks 0 1 (-1) 0 := by
  simp [sp4Mat, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hS]

@[expose] def sp4GL (S : Matrix (Fin 2) (Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K where
  val := sp4Mat S
  inv := sp4Mat (-S)
  val_inv := sp4Mat_mul_neg S
  inv_val := by rw [sp4Mat_mul, neg_add_cancel, sp4Mat_zero]

@[expose] def sp4Elt {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) : ↥(StatedSp 2 K) :=
  ⟨sp4GL S, Subgroup.subset_closure (sp4Mat_symplectic hS)⟩

@[simp] theorem sp4Elt_coe {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    (((sp4Elt hS : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sp4Mat S :=
  rfl

@[expose] def sp4H (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

theorem sp4H_transpose : (sp4H K)ᵀ = sp4H K := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sp4H_det : (sp4H K).det = -1 := by
  simp [sp4H, Matrix.det_fin_two_of]

theorem sp4_det_add_sp4H [CharP K 2] {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    (S + sp4H K).det = S.det + 1 := by
  have h10 : S 1 0 = S 0 1 := by
    have h := congrFun (congrFun hS 0) 1
    rwa [Matrix.transpose_apply] at h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e00 : (S + sp4H K) 0 0 = S 0 0 := by simp [sp4H]
  have e01 : (S + sp4H K) 0 1 = S 0 1 + 1 := by simp [sp4H]
  have e10 : (S + sp4H K) 1 0 = S 0 1 + 1 := by simp [sp4H, h10]
  have e11 : (S + sp4H K) 1 1 = S 1 1 := by simp [sp4H]
  rw [Matrix.det_fin_two, Matrix.det_fin_two, e00, e01, e10, e11, h10]
  linear_combination (-(S 0 1) - 1) * h2

@[expose] def sp4Sym (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a, b; b, 0]

theorem sp4Sym_transpose (a b : K) : (sp4Sym a b)ᵀ = sp4Sym a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Matrices

section Radical

variable {K : Type} [Field K]

@[expose] def sp4Rad (K : Type) [Field K] : Subgroup ↥(StatedSp 2 K) where
  carrier := {g | ∃ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S ∧
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sp4Mat S}
  one_mem' := ⟨0, Matrix.transpose_zero, sp4Mat_zero.symm⟩
  mul_mem' := by
    rintro a b ⟨S, hS, ha⟩ ⟨S', hS', hb⟩
    refine ⟨S + S', by rw [Matrix.transpose_add, hS, hS'], ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, ha, hb, sp4Mat_mul]
  inv_mem' := by
    rintro a ⟨S, hS, ha⟩
    refine ⟨-S, by rw [Matrix.transpose_neg, hS], ?_⟩
    rw [Subgroup.coe_inv]
    exact Units.inv_eq_of_mul_eq_one_right (by rw [ha, sp4Mat_mul_neg])

theorem sp4Rad_mem_iff {g : ↥(StatedSp 2 K)} :
    g ∈ sp4Rad K ↔ ∃ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S ∧
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sp4Mat S :=
  Iff.rfl

theorem sp4Elt_mem_sp4Rad {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) : sp4Elt hS ∈ sp4Rad K :=
  ⟨S, hS, rfl⟩

theorem sp4Rad_comm : ∀ a ∈ sp4Rad K, ∀ b ∈ sp4Rad K, a * b = b * a := by
  rintro a ⟨S, -, ha⟩ b ⟨S', -, hb⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, ha, hb, sp4Mat_mul,
    sp4Mat_mul, add_comm]

theorem sp4Rad_mul_self [CharP K 2] : ∀ a ∈ sp4Rad K, a * a = 1 := by
  rintro a ⟨S, -, ha⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, ha, sp4Mat_mul, CharTwo.add_self_eq_zero, sp4Mat_zero]
  rfl

theorem sp4Rad_ne_bot : sp4Rad K ≠ ⊥ := by
  intro h
  have h1 : sp4Elt (sp4H_transpose (K := K)) ∈ sp4Rad K := sp4Elt_mem_sp4Rad _
  rw [h, Subgroup.mem_bot] at h1
  have h2 := congrArg (fun g : ↥(StatedSp 2 K) =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inr 1)) h1
  simp [sp4Mat, sp4H] at h2

@[expose] def sp4Iso (K : Type) [Field K] : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K)) where
  carrier := {x | ∀ j, Multiplicative.toAdd x (Sum.inr j) = 0}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb j => by
    rw [toAdd_mul, Pi.add_apply, ha j, hb j, add_zero]
  inv_mem' := fun {a} ha j => by
    rw [toAdd_inv, Pi.neg_apply, ha j, neg_zero]

theorem sp4Iso_mem_iff {x : Multiplicative (Fin 2 ⊕ Fin 2 → K)} :
    x ∈ sp4Iso K ↔ ∀ j, Multiplicative.toAdd x (Sum.inr j) = 0 :=
  Iff.rfl

theorem sp4_index_le [Finite K] : (sp4Iso K).index ≤ Nat.card ↥(sp4Rad K) := by
  refine index_le_of_injective (sp4Iso K)
    (fun x => (⟨sp4Elt (sp4Sym_transpose (Multiplicative.toAdd x (Sum.inr 0))
      (Multiplicative.toAdd x (Sum.inr 1))), sp4Elt_mem_sp4Rad _⟩,
      ⟨Multiplicative.ofAdd (Sum.elim (Multiplicative.toAdd x ∘ Sum.inl) 0), fun _ => rfl⟩)) ?_
  intro x y hxy
  have h1 := congrArg (fun p : ↥(sp4Rad K) × ↥(sp4Iso K) =>
    ((((p.1 : ↥(sp4Rad K)) : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hxy
  have h2 := congrArg (fun p : ↥(sp4Rad K) × ↥(sp4Iso K) =>
    Multiplicative.toAdd ((p.2 : ↥(sp4Iso K)) : Multiplicative (Fin 2 ⊕ Fin 2 → K))) hxy
  apply Multiplicative.toAdd.injective
  funext i
  rcases i with i | i
  · exact congrFun h2 (Sum.inl i)
  · fin_cases i
    · exact congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 0)
    · exact congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 1)

end Radical

section Covering

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V Z : Subgroup W} {K : Type}
  [Field K] [CharP K 2] {π : ↥(StatedSp 2 K) →* ↥L}

theorem sp4_apply_eq_of_isUnit (hW : ∀ w : W, w * w = 1) (hLs : L ≤ stabSub V)
    (hZ : ∀ g ∈ L, ∀ z ∈ Z, g z = z) (β : ↥V →* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (hβs : Function.Surjective β) (hβk : ∀ u : ↥V, β u = 1 ↔ (u : W) ∈ Z)
    (hβe : ∀ (γ : ↥(StatedSp 2 K)) (u : ↥V) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ V),
      β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = natAct (StatedSp 2 K) γ (β u))
    {γ : ↥(StatedSp 2 K)} {S : Matrix (Fin 2) (Fin 2) K}
    (hγ : ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sp4Mat S)
    (hS : IsUnit S.det) {v : ↥V} (hv : β v ∈ sp4Iso K) :
    ((π γ : ↥L) : MulAut W) (v : W) = v := by
  have haV : ∀ x ∈ V, ((π γ : ↥L) : MulAut W) x ∈ V := fun x hx =>
    (mem_stabSub.mp (hLs (π γ).2) x).mpr hx
  have hγ2 : γ * γ = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hγ, sp4Mat_mul, CharTwo.add_self_eq_zero, sp4Mat_zero]
    rfl
  have ha2 : ((π γ : ↥L) : MulAut W) * ((π γ : ↥L) : MulAut W) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hγ2, map_one, Subgroup.coe_one]
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd
    (Sum.elim 0 (S⁻¹ *ᵥ (Multiplicative.toAdd (β v) ∘ Sum.inl))))
  refine apply_eq_of_lift hW ha2 (hZ _ (π γ).2) haV β hβk (u := u) ?_
  rw [hβe γ u (haV u u.2), hu]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, natAct, hγ]
  rw [← sub_eq_add_neg, sp4Mat_mulVec_sub hS]
  funext i
  rcases i with i | i
  · rfl
  · exact (sp4Iso_mem_iff.mp hv i).symm

theorem sp4_apply_eq (hW : ∀ w : W, w * w = 1) (hLs : L ≤ stabSub V)
    (hZ : ∀ g ∈ L, ∀ z ∈ Z, g z = z) (β : ↥V →* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (hβs : Function.Surjective β) (hβk : ∀ u : ↥V, β u = 1 ↔ (u : W) ∈ Z)
    (hβe : ∀ (γ : ↥(StatedSp 2 K)) (u : ↥V) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ V),
      β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = natAct (StatedSp 2 K) γ (β u))
    {γ : ↥(StatedSp 2 K)} {S : Matrix (Fin 2) (Fin 2) K}
    (hγ : ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sp4Mat S)
    (hS : Sᵀ = S) {v : ↥V} (hv : β v ∈ sp4Iso K) :
    ((π γ : ↥L) : MulAut W) (v : W) = v := by
  rcases eq_or_ne S.det 0 with hdet | hdet
  · have hH : IsUnit (sp4H K).det := by
      rw [sp4H_det]
      exact isUnit_one.neg
    have hSH : IsUnit (S + sp4H K).det := by
      rw [sp4_det_add_sp4H hS, hdet, zero_add]
      exact isUnit_one
    have hSHt : (S + sp4H K)ᵀ = S + sp4H K := by
      rw [Matrix.transpose_add, hS, sp4H_transpose]
    have hγ' : γ = sp4Elt hSHt * sp4Elt sp4H_transpose := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Units.val_mul, hγ, sp4Elt_coe, sp4Elt_coe, sp4Mat_mul, add_assoc,
        CharTwo.add_self_eq_zero, add_zero]
    rw [hγ', map_mul, Subgroup.coe_mul, MulAut.mul_apply,
      sp4_apply_eq_of_isUnit hW hLs hZ β hβs hβk hβe (sp4Elt_coe sp4H_transpose) hH hv,
      sp4_apply_eq_of_isUnit hW hLs hZ β hβs hβk hβe (sp4Elt_coe hSHt) hSH hv]
  · exact sp4_apply_eq_of_isUnit hW hLs hZ β hβs hβk hβe hγ (isUnit_iff_ne_zero.mpr hdet) hv

end Covering

theorem isFFModule_of_natSp4 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} {V Z : Subgroup W} (hLs : L ≤ stabSub V)
    (hZ : ∀ g ∈ L, ∀ z ∈ Z, g z = z) {K : Type} [Field K] [Finite K] [CharP K 2]
    {π : ↥(StatedSp 2 K) →* ↥L}
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia L V Z π) : IsFFModule (autSub L V) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_ambMap (D := FFModel.nat (StatedSp 2 K)) rfl hπ
  have hβs' : Function.Surjective β := fun m => hβs m (Subgroup.mem_top m)
  refine isFFModule_of_realizesVia (FFModel.nat_faithful _) hLs hπ β hβs' (sp4Rad K)
    sp4Rad_comm sp4Rad_mul_self sp4Rad_ne_bot (sp4Iso K) sp4_index_le ?_
  intro v hv a ha
  obtain ⟨S, hS, hSa⟩ := sp4Rad_mem_iff.mp ha
  exact sp4_apply_eq hW hLs hZ β hβs' hβk hβe hSa hS hv

end CFSG.Quasithin.RonanD35
