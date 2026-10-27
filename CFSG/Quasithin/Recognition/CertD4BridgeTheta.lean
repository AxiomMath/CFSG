module

public import CFSG.Quasithin.Recognition.CertD4BridgeData

public section

namespace CFSG.Quasithin

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

section Natural

variable (k : Type) [Field k] [CharP k 2]

@[expose] def d4bφ : ZMod 2 →+* k := ZMod.castHom (dvd_refl 2) k

@[expose] def d4bEk (i : Fin Tag.D4.rank) (s : Bool) : Matrix (Fin 8) (Fin 8) k :=
  (d4bφ k).mapMatrix (d4bEs i s)

theorem d4bEk_mul_self
    (i : Fin Tag.D4.rank) (s : Bool) : d4bEk k i s * d4bEk k i s = 0 := by
  rw [d4bEk, ← map_mul, d4bEs_mul_self, map_zero]

@[expose] def d4bUm (i : Fin Tag.D4.rank) (s : Bool) (c : k) : Matrix (Fin 8) (Fin 8) k :=
  1 + c • d4bEk k i s

theorem d4bUm_mul_self (i : Fin Tag.D4.rank) (s : Bool) (c : k) :
    d4bUm k i s c * d4bUm k i s c = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hE := d4bEk_mul_self k i s
  unfold d4bUm
  have hcc : c • d4bEk k i s + c • d4bEk k i s = 0 := by
    rw [← two_smul k (c • d4bEk k i s), h2, zero_smul]
  calc (1 + c • d4bEk k i s) * (1 + c • d4bEk k i s)
      = 1 + (c • d4bEk k i s + c • d4bEk k i s) +
          c • c • (d4bEk k i s * d4bEk k i s) := by
        simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add]
        abel
    _ = 1 := by rw [hcc, hE]; simp

@[expose] def d4bNat
    (i : Fin Tag.D4.rank) (s : Bool) (c : k) : GL (Fin 8) k :=
  ⟨d4bUm k i s c, d4bUm k i s c, d4bUm_mul_self k i s c, d4bUm_mul_self k i s c⟩

@[expose] def d4bΩ : Subgroup (GL (Fin 8) k) :=
  Subgroup.closure {B | ∃ (i : Fin Tag.D4.rank) (s : Bool) (c : k), B = d4bNat k i s c}

theorem d4bNat_mem
    (i : Fin Tag.D4.rank) (s : Bool) (c : k) : d4bNat k i s c ∈ d4bΩ k :=
  Subgroup.subset_closure ⟨i, s, c, rfl⟩

end Natural

section Theta

variable (k : Type) [Field k] [CharP k 2]

theorem d4b_toLabel_injective
    : Function.Injective (toLabel d4Certificate_check) := by
  rintro (j | m) (j' | m') h
  · simpa [toLabel] using h
  · simp [toLabel] at h
  · simp [toLabel] at h
  · simp only [toLabel, Sum.inr.injEq, Subtype.mk.injEq] at h
    exact congrArg Sum.inr (d4b_root_injective m m' h)

noncomputable def d4bθ₀
    (b : Label Tag.D4) : Matrix (Fin 8) (Fin 8) k :=
  (d4bφ k).mapMatrix (d4bTh (Function.surjInv (surjective_toLabel d4Certificate_check) b))

noncomputable def d4bθ
    : RootModule Tag.D4 k →ₗ[k] Matrix (Fin 8) (Fin 8) k :=
  Finsupp.linearCombination k (d4bθ₀ k)

theorem d4bθ_single
    (b : Label Tag.D4) (r : k) : d4bθ k (Finsupp.single b r) = r • d4bθ₀ k b := by
  simp [d4bθ]

theorem d4bθ₀_toLabel
    (a : Idx d4Certificate) :
    d4bθ₀ k (toLabel d4Certificate_check a) = (d4bφ k).mapMatrix (d4bTh a) := by
  have h := Function.surjInv_eq (surjective_toLabel d4Certificate_check) (toLabel d4Certificate_check a)
  have h' := d4b_toLabel_injective h
  simp only [d4bθ₀, h']

theorem d4bθ_toVec
    (c : Col d4Certificate) :
    d4bθ k (toVec d4Certificate_check k c) = (d4bφ k).mapMatrix (d4bCol c) := by
  rcases c with _ | ⟨a, z⟩
  · simp [d4bCol]
  · rw [toVec_some, map_smul, d4bθ_single, d4bθ₀_toLabel]
    ext r s
    simp [d4bCol, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]

theorem d4bθ_simple
    (i : Fin Tag.D4.rank) (s : Bool) (hm : d4bSimple i s < d4Certificate.roots.length) :
    d4bθ k (Finsupp.single (toLabel d4Certificate_check (.inr ⟨d4bSimple i s, hm⟩)) 1) =
      d4bEk k i s := by
  rw [d4bθ_single, d4bθ₀_toLabel, one_smul]
  rfl


theorem d4bθ_xOp_single
    (i : Fin Tag.D4.rank) (c : k) (a : Idx d4Certificate) :
    d4bθ k (xOp Tag.D4 k i c (Finsupp.single (toLabel d4Certificate_check a) 1)) =
      d4bUm k i true c * d4bθ k (Finsupp.single (toLabel d4Certificate_check a) 1) *
        d4bUm k i true c := by
  obtain ⟨h0, h1, h2, h3⟩ := d4b_check i a
  have e0 := xCoeff_toLabel d4Certificate_check k d4StringData_check i 0 a
  have e1 := xCoeff_toLabel d4Certificate_check k d4StringData_check i 1 a
  have e2 := xCoeff_toLabel d4Certificate_check k d4StringData_check i 2 a
  have e3 := xCoeff_toLabel d4Certificate_check k d4StringData_check i 3 a
  rw [xOp_eq_sum_xCoeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul]
  rw [e0, e1, e2, e3, d4bθ_toVec, d4bθ_toVec, d4bθ_toVec, d4bθ_toVec, h0, h1, h2, h3,
    d4bθ_single, d4bθ₀_toLabel, one_smul]
  simp only [map_add, map_mul, map_zero, pow_zero, pow_one, one_smul, smul_zero, add_zero]
  unfold d4bUm d4bEk
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_smul, pow_two]
  abel

theorem d4bθ_yOp_single
    (i : Fin Tag.D4.rank) (c : k) (a : Idx d4Certificate) :
    d4bθ k (yOp Tag.D4 k i c (Finsupp.single (toLabel d4Certificate_check a) 1)) =
      d4bUm k i false c * d4bθ k (Finsupp.single (toLabel d4Certificate_check a) 1) *
        d4bUm k i false c := by
  obtain ⟨h0, h1, h2, h3⟩ := d4b_check_y i a
  have e0 := yCoeff_toLabel d4Certificate_check k d4StringData_check i 0 a
  have e1 := yCoeff_toLabel d4Certificate_check k d4StringData_check i 1 a
  have e2 := yCoeff_toLabel d4Certificate_check k d4StringData_check i 2 a
  have e3 := yCoeff_toLabel d4Certificate_check k d4StringData_check i 3 a
  rw [yOp_eq_sum_yCoeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul]
  rw [e0, e1, e2, e3, d4bθ_toVec, d4bθ_toVec, d4bθ_toVec, d4bθ_toVec, h0, h1, h2, h3,
    d4bθ_single, d4bθ₀_toLabel, one_smul]
  simp only [map_add, map_mul, map_zero, pow_zero, pow_one, one_smul, smul_zero, add_zero]
  unfold d4bUm d4bEk
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_smul, pow_two]
  abel

theorem d4bθ_xOp
    (i : Fin Tag.D4.rank) (c : k) (v : RootModule Tag.D4 k) :
    d4bθ k (xOp Tag.D4 k i c v) = d4bUm k i true c * d4bθ k v * d4bUm k i true c := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, map_add, hv, hw, mul_add, add_mul]
  | single b r =>
    obtain ⟨a, rfl⟩ := surjective_toLabel d4Certificate_check b
    have h : Finsupp.single (toLabel d4Certificate_check a) r =
        r • Finsupp.single (toLabel d4Certificate_check a) (1 : k) := by simp
    rw [h, map_smul, map_smul, map_smul, d4bθ_xOp_single, Matrix.mul_smul, Matrix.smul_mul]

theorem d4bθ_yOp
    (i : Fin Tag.D4.rank) (c : k) (v : RootModule Tag.D4 k) :
    d4bθ k (yOp Tag.D4 k i c v) = d4bUm k i false c * d4bθ k v * d4bUm k i false c := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, map_add, hv, hw, mul_add, add_mul]
  | single b r =>
    obtain ⟨a, rfl⟩ := surjective_toLabel d4Certificate_check b
    have h : Finsupp.single (toLabel d4Certificate_check a) r =
        r • Finsupp.single (toLabel d4Certificate_check a) (1 : k) := by simp
    rw [h, map_smul, map_smul, map_smul, d4bθ_yOp_single, Matrix.mul_smul, Matrix.smul_mul]


@[expose] def D4bRel
    (A : ModGL Tag.D4 k) (B : GL (Fin 8) k) : Prop :=
  ∀ v : RootModule Tag.D4 k,
    d4bθ k ((A : Module.End k (RootModule Tag.D4 k)) v) * (B : Matrix (Fin 8) (Fin 8) k) =
      (B : Matrix (Fin 8) (Fin 8) k) * d4bθ k v

theorem d4b_rel_one : D4bRel k 1 1 := by
  intro v
  simp

theorem d4b_rel_mul
    {A A' : ModGL Tag.D4 k} {B B' : GL (Fin 8) k} (h : D4bRel k A B)
    (h' : D4bRel k A' B') : D4bRel k (A * A') (B * B') := by
  intro v
  have h1 := h ((A' : Module.End k (RootModule Tag.D4 k)) v)
  have h2 := h' v
  simp only [Units.val_mul, Module.End.mul_apply]
  calc d4bθ k ((A : Module.End k (RootModule Tag.D4 k)) ((A' : Module.End k (RootModule Tag.D4 k)) v)) *
        ((B : Matrix (Fin 8) (Fin 8) k) * (B' : Matrix (Fin 8) (Fin 8) k))
      = (d4bθ k ((A : Module.End k (RootModule Tag.D4 k)) ((A' : Module.End k (RootModule Tag.D4 k)) v)) *
          (B : Matrix (Fin 8) (Fin 8) k)) * (B' : Matrix (Fin 8) (Fin 8) k) := by
        rw [mul_assoc]
    _ = ((B : Matrix (Fin 8) (Fin 8) k) * d4bθ k ((A' : Module.End k (RootModule Tag.D4 k)) v)) *
          (B' : Matrix (Fin 8) (Fin 8) k) := by rw [h1]
    _ = (B : Matrix (Fin 8) (Fin 8) k) * (d4bθ k ((A' : Module.End k (RootModule Tag.D4 k)) v) *
          (B' : Matrix (Fin 8) (Fin 8) k)) := by rw [mul_assoc]
    _ = (B : Matrix (Fin 8) (Fin 8) k) * ((B' : Matrix (Fin 8) (Fin 8) k) * d4bθ k v) := by rw [h2]
    _ = ((B : Matrix (Fin 8) (Fin 8) k) * (B' : Matrix (Fin 8) (Fin 8) k)) * d4bθ k v := by
        rw [mul_assoc]

theorem d4b_rel_inv
    {A : ModGL Tag.D4 k} {B : GL (Fin 8) k} (h : D4bRel k A B) :
    D4bRel k A⁻¹ B⁻¹ := by
  intro v
  have hA : (A : Module.End k (RootModule Tag.D4 k))
      (((A⁻¹ : ModGL Tag.D4 k) : Module.End k (RootModule Tag.D4 k)) v) = v := by
    have h1 : ((A : Module.End k (RootModule Tag.D4 k)) *
        ((A⁻¹ : ModGL Tag.D4 k) : Module.End k (RootModule Tag.D4 k))) = 1 := Units.mul_inv A
    exact LinearMap.congr_fun h1 v
  have h1 := h (((A⁻¹ : ModGL Tag.D4 k) : Module.End k (RootModule Tag.D4 k)) v)
  rw [hA] at h1
  have hBB : ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * (B : Matrix (Fin 8) (Fin 8) k) = 1 :=
    Units.inv_mul B
  have hBB' : (B : Matrix (Fin 8) (Fin 8) k) * ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) = 1 :=
    Units.mul_inv B
  calc d4bθ k (((A⁻¹ : ModGL Tag.D4 k) : Module.End k (RootModule Tag.D4 k)) v) *
        ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k)
      = ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
          ((B : Matrix (Fin 8) (Fin 8) k) *
            d4bθ k (((A⁻¹ : ModGL Tag.D4 k) : Module.End k (RootModule Tag.D4 k)) v)) *
          ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) := by
        rw [← mul_assoc, hBB, one_mul]
    _ = ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
          (d4bθ k v * (B : Matrix (Fin 8) (Fin 8) k)) *
          ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) := by rw [h1]
    _ = ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * d4bθ k v := by
        rw [mul_assoc, mul_assoc, hBB', mul_one]

theorem d4b_rel_of_xOp
    (i : Fin Tag.D4.rank) (c : k) (A : ModGL Tag.D4 k)
    (h : (A : Module.End k (RootModule Tag.D4 k)) = xOp Tag.D4 k i c) :
    D4bRel k A (d4bNat k i true c) := by
  intro v
  rw [h, d4bθ_xOp]
  change d4bUm k i true c * d4bθ k v * d4bUm k i true c * d4bUm k i true c = _
  rw [mul_assoc (d4bUm k i true c * d4bθ k v), d4bUm_mul_self, mul_one]
  rfl

theorem d4b_rel_of_yOp
    (i : Fin Tag.D4.rank) (c : k) (A : ModGL Tag.D4 k)
    (h : (A : Module.End k (RootModule Tag.D4 k)) = yOp Tag.D4 k i c) :
    D4bRel k A (d4bNat k i false c) := by
  intro v
  rw [h, d4bθ_yOp]
  change d4bUm k i false c * d4bθ k v * d4bUm k i false c * d4bUm k i false c = _
  rw [mul_assoc (d4bUm k i false c * d4bθ k v), d4bUm_mul_self, mul_one]
  rfl

theorem d4b_exists_partner
    (A : ModGL Tag.D4 k) (hA : A ∈ adjointGroup Tag.D4 k) :
    ∃ B ∈ d4bΩ k, D4bRel k A B := by
  unfold adjointGroup at hA
  induction hA using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, c, h | h⟩ := hg
    · exact ⟨d4bNat k i true c, d4bNat_mem k i true c, d4b_rel_of_xOp k i c g h⟩
    · exact ⟨d4bNat k i false c, d4bNat_mem k i false c, d4b_rel_of_yOp k i c g h⟩
  | one => exact ⟨1, Subgroup.one_mem _, d4b_rel_one k⟩
  | mul g g' _ _ hg hg' =>
    obtain ⟨B, hB, r⟩ := hg
    obtain ⟨B', hB', r'⟩ := hg'
    exact ⟨B * B', Subgroup.mul_mem _ hB hB', d4b_rel_mul k r r'⟩
  | inv g _ hg =>
    obtain ⟨B, hB, r⟩ := hg
    exact ⟨B⁻¹, Subgroup.inv_mem _ hB, d4b_rel_inv k r⟩


theorem d4b_det_nat (i : Fin Tag.D4.rank) (s : Bool) (c : k) :
    (d4bNat k i s c : Matrix (Fin 8) (Fin 8) k).det = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hx : (d4bUm k i s c).det * (d4bUm k i s c).det = 1 := by
    rw [← Matrix.det_mul, d4bUm_mul_self, Matrix.det_one]
  have hsq : ((d4bUm k i s c).det - 1) ^ 2 = 0 := by
    linear_combination hx - ((d4bUm k i s c).det - 1) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)

theorem d4b_det_Ω (B : GL (Fin 8) k) (hB : B ∈ d4bΩ k) :
    (B : Matrix (Fin 8) (Fin 8) k).det = 1 := by
  induction hB using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, s, c, rfl⟩ := hg
    exact d4b_det_nat k i s c
  | one => simp
  | mul g g' _ _ hg hg' => rw [Units.val_mul, Matrix.det_mul, hg, hg', one_mul]
  | inv g _ hg =>
    have h : (g : Matrix (Fin 8) (Fin 8) k).det *
        ((g⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k).det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rwa [hg, one_mul] at h

theorem d4b_scalar (D : Matrix (Fin 8) (Fin 8) k)
    (h : ∀ (i : Fin Tag.D4.rank) (s : Bool), D * d4bEk k i s = d4bEk k i s * D) :
    ∃ c : k, D = c • (1 : Matrix (Fin 8) (Fin 8) k) := by
  have e : ∀ (i : Fin Tag.D4.rank) (s : Bool) (r c : Fin 8),
      (D * d4bEk k i s) r c = (d4bEk k i s * D) r c := fun i s r c => by rw [h i s]
  have b0 : D 0 1 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 1 1
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b1 : D 0 2 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 1 2
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b2 : D 0 3 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 1 3
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b3 : D 0 4 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 1 4
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b4 : D 0 5 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 1 5
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b5 : D 0 7 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 1 7
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b6 : D 1 0 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 0 0
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b7 : D 1 2 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 0 2
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b8 : D 1 3 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 0 3
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b9 : D 1 4 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 0 4
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b10 : D 1 5 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 0 5
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b11 : D 1 6 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 0 6
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b12 : D 1 7 = 0 := by
    have e1 := e ⟨2, by decide⟩ false 2 7
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b13 : D 2 0 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 3 0
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b14 : D 2 1 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 3 1
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b15 : D 2 3 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 3 3
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b16 : D 2 4 = 0 := by
    have e1 := e ⟨2, by decide⟩ true 1 4
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b17 : D 2 5 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 3 5
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b18 : D 2 6 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 3 6
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b19 : D 2 7 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 3 7
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b20 : D 3 0 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 2 0
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b21 : D 3 1 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 2 1
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b22 : D 3 2 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 2 2
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b23 : D 3 4 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 2 4
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b24 : D 3 5 = 0 := by
    have e1 := e ⟨3, by decide⟩ false 5 5
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b25 : D 3 6 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 2 6
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b26 : D 3 7 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 2 7
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b27 : D 4 0 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 5 0
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b28 : D 4 1 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 5 1
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b29 : D 4 2 = 0 := by
    have e1 := e ⟨3, by decide⟩ true 2 2
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b30 : D 4 3 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 5 3
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b31 : D 4 5 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 5 5
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b32 : D 4 6 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 5 6
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b33 : D 4 7 = 0 := by
    have e1 := e ⟨1, by decide⟩ false 5 7
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b34 : D 5 0 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 4 0
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b35 : D 5 1 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 4 1
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b36 : D 5 2 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 4 2
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b37 : D 5 3 = 0 := by
    have e1 := e ⟨2, by decide⟩ false 6 3
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b38 : D 5 4 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 4 4
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b39 : D 5 6 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 4 6
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b40 : D 5 7 = 0 := by
    have e1 := e ⟨1, by decide⟩ true 4 7
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b41 : D 6 0 = 0 := by
    have e1 := e ⟨2, by decide⟩ true 5 0
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b42 : D 6 1 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 7 1
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b43 : D 6 2 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 7 2
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b44 : D 6 3 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 7 3
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b45 : D 6 4 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 7 4
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b46 : D 6 5 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 7 5
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b47 : D 6 7 = 0 := by
    have e1 := e ⟨0, by decide⟩ false 7 7
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b48 : D 7 0 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 6 0
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b49 : D 7 2 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 6 2
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b50 : D 7 3 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 6 3
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b51 : D 7 4 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 6 4
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b52 : D 7 5 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 6 5
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b53 : D 7 6 = 0 := by
    have e1 := e ⟨0, by decide⟩ true 6 6
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1.symm
  have b54 : D 0 0 = D 1 1 := by
    have e1 := e ⟨0, by decide⟩ true 0 1
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1
  have b60 : D 0 6 = 0 := by
    have e1 := e ⟨2, by decide⟩ false 0 5
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1
  have b65 : D 1 1 = D 2 2 := by
    have e1 := e ⟨2, by decide⟩ true 1 2
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1
  have b76 : D 2 2 = D 3 3 := by
    have e1 := e ⟨1, by decide⟩ true 2 3
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1
  have b77 : D 2 2 = D 4 4 := by
    have e1 := e ⟨3, by decide⟩ true 2 4
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1
  have b91 : D 3 3 = D 5 5 := by
    have e1 := e ⟨3, by decide⟩ true 3 5
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1
  have b118 : D 5 5 = D 6 6 := by
    have e1 := e ⟨2, by decide⟩ true 5 6
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1
  have b129 : D 6 6 = D 7 7 := by
    have e1 := e ⟨0, by decide⟩ true 6 7
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1
  have b132 : D 7 1 = 0 := by
    have e1 := e ⟨2, by decide⟩ true 7 2
    simp [Matrix.mul_apply, d4bEk, d4bEs, d4bE, d4bSimple, d4bPos,
      RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    exact e1
  have t0 : D 0 1 = 0 := by linear_combination b0
  have t1 : D 0 2 = 0 := by linear_combination b1
  have t2 : D 0 3 = 0 := by linear_combination b2
  have t3 : D 0 4 = 0 := by linear_combination b3
  have t4 : D 0 5 = 0 := by linear_combination b4
  have t5 : D 0 6 = 0 := by linear_combination b60
  have t6 : D 0 7 = 0 := by linear_combination b5
  have t7 : D 1 0 = 0 := by linear_combination b6
  have t8 : D 1 2 = 0 := by linear_combination b7
  have t9 : D 1 3 = 0 := by linear_combination b8
  have t10 : D 1 4 = 0 := by linear_combination b9
  have t11 : D 1 5 = 0 := by linear_combination b10
  have t12 : D 1 6 = 0 := by linear_combination b11
  have t13 : D 1 7 = 0 := by linear_combination b12
  have t14 : D 2 0 = 0 := by linear_combination b13
  have t15 : D 2 1 = 0 := by linear_combination b14
  have t16 : D 2 3 = 0 := by linear_combination b15
  have t17 : D 2 4 = 0 := by linear_combination b16
  have t18 : D 2 5 = 0 := by linear_combination b17
  have t19 : D 2 6 = 0 := by linear_combination b18
  have t20 : D 2 7 = 0 := by linear_combination b19
  have t21 : D 3 0 = 0 := by linear_combination b20
  have t22 : D 3 1 = 0 := by linear_combination b21
  have t23 : D 3 2 = 0 := by linear_combination b22
  have t24 : D 3 4 = 0 := by linear_combination b23
  have t25 : D 3 5 = 0 := by linear_combination b24
  have t26 : D 3 6 = 0 := by linear_combination b25
  have t27 : D 3 7 = 0 := by linear_combination b26
  have t28 : D 4 0 = 0 := by linear_combination b27
  have t29 : D 4 1 = 0 := by linear_combination b28
  have t30 : D 4 2 = 0 := by linear_combination b29
  have t31 : D 4 3 = 0 := by linear_combination b30
  have t32 : D 4 5 = 0 := by linear_combination b31
  have t33 : D 4 6 = 0 := by linear_combination b32
  have t34 : D 4 7 = 0 := by linear_combination b33
  have t35 : D 5 0 = 0 := by linear_combination b34
  have t36 : D 5 1 = 0 := by linear_combination b35
  have t37 : D 5 2 = 0 := by linear_combination b36
  have t38 : D 5 3 = 0 := by linear_combination b37
  have t39 : D 5 4 = 0 := by linear_combination b38
  have t40 : D 5 6 = 0 := by linear_combination b39
  have t41 : D 5 7 = 0 := by linear_combination b40
  have t42 : D 6 0 = 0 := by linear_combination b41
  have t43 : D 6 1 = 0 := by linear_combination b42
  have t44 : D 6 2 = 0 := by linear_combination b43
  have t45 : D 6 3 = 0 := by linear_combination b44
  have t46 : D 6 4 = 0 := by linear_combination b45
  have t47 : D 6 5 = 0 := by linear_combination b46
  have t48 : D 6 7 = 0 := by linear_combination b47
  have t49 : D 7 0 = 0 := by linear_combination b48
  have t50 : D 7 1 = 0 := by linear_combination b132
  have t51 : D 7 2 = 0 := by linear_combination b49
  have t52 : D 7 3 = 0 := by linear_combination b50
  have t53 : D 7 4 = 0 := by linear_combination b51
  have t54 : D 7 5 = 0 := by linear_combination b52
  have t55 : D 7 6 = 0 := by linear_combination b53
  have t56 : D 1 1 = D 0 0 := by linear_combination -b54
  have t57 : D 2 2 = D 0 0 := by linear_combination -b65 - b54
  have t58 : D 3 3 = D 0 0 := by linear_combination -b76 - b65 - b54
  have t59 : D 4 4 = D 0 0 := by linear_combination -b77 - b65 - b54
  have t60 : D 5 5 = D 0 0 := by linear_combination -b91 - b76 - b65 - b54
  have t61 : D 6 6 = D 0 0 := by linear_combination -b118 - b91 - b76 - b65 - b54
  have t62 : D 7 7 = D 0 0 := by linear_combination -b129 - b118 - b91 - b76 - b65 - b54
  refine ⟨D 0 0, ?_⟩
  ext r c
  fin_cases r <;> fin_cases c <;> simp [Matrix.smul_apply] <;> assumption

theorem d4b_rel_unique
    [Finite k] (hk : Nat.card k = 8) {A : ModGL Tag.D4 k}
    {B B' : GL (Fin 8) k} (hB : B ∈ d4bΩ k) (hB' : B' ∈ d4bΩ k) (h : D4bRel k A B)
    (h' : D4bRel k A B') : B = B' := by
  have hBB : ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
      (B : Matrix (Fin 8) (Fin 8) k) = 1 := Units.inv_mul B
  have hBB' : (B : Matrix (Fin 8) (Fin 8) k) *
      ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) = 1 := Units.mul_inv B
  have hcomm : ∀ v : RootModule Tag.D4 k,
      ((B⁻¹ * B' : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * d4bθ k v =
        d4bθ k v * ((B⁻¹ * B' : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) := by
    intro v
    set T := d4bθ k v with hT
    set S := d4bθ k ((A : Module.End k (RootModule Tag.D4 k)) v) with hS
    have e1 : T = ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
        (S * (B : Matrix (Fin 8) (Fin 8) k)) := by
      rw [hS, h v, ← mul_assoc, hBB, one_mul]
    have e2 : S * (B' : Matrix (Fin 8) (Fin 8) k) = (B' : Matrix (Fin 8) (Fin 8) k) * T := h' v
    rw [Units.val_mul]
    have L : ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * (B' : Matrix (Fin 8) (Fin 8) k) * T =
        ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * S * (B' : Matrix (Fin 8) (Fin 8) k) := by
      rw [mul_assoc, ← e2, ← mul_assoc]
    have R : T * (((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
        (B' : Matrix (Fin 8) (Fin 8) k)) =
        ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * S * (B' : Matrix (Fin 8) (Fin 8) k) := by
      calc T * (((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
              (B' : Matrix (Fin 8) (Fin 8) k))
          = ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * (S * (B : Matrix (Fin 8) (Fin 8) k)) *
            (((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * (B' : Matrix (Fin 8) (Fin 8) k)) := by
            rw [← e1]
        _ = ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * S *
            ((B : Matrix (Fin 8) (Fin 8) k) * ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k)) *
            (B' : Matrix (Fin 8) (Fin 8) k) := by simp only [mul_assoc]
        _ = _ := by rw [hBB', mul_one]
    exact L.trans R.symm
  obtain ⟨c, hc⟩ := d4b_scalar k ((B⁻¹ * B' : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k)
    (fun i s => by
      have hm : d4bSimple i s < d4Certificate.roots.length := by
        cases s <;> fin_cases i <;> decide
      have := hcomm (Finsupp.single (toLabel d4Certificate_check (.inr ⟨d4bSimple i s, hm⟩)) 1)
      rwa [d4bθ_simple k i s hm] at this)
  have hdet := d4b_det_Ω k (B⁻¹ * B') (Subgroup.mul_mem _ (Subgroup.inv_mem _ hB) hB')
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = 8 := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hc1 : c = 1 := by
    have h8 : c ^ 8 = c := by
      have := FiniteField.pow_card c
      rwa [hcard] at this
    rw [← h8]
    exact hdet
  have hD1 : B⁻¹ * B' = 1 := Units.ext (by rw [hc, hc1, one_smul]; rfl)
  exact inv_mul_eq_one.1 hD1

noncomputable def d4bΨ
    [Finite k] (hk : Nat.card k = 8) :
    ↥(adjointGroup Tag.D4 k) →* GL (Fin 8) k :=
  MonoidHom.mk' (fun A => Classical.choose (d4b_exists_partner k A.1 A.2)) (by
    intro A A'
    obtain ⟨hB, hr⟩ := Classical.choose_spec (d4b_exists_partner k A.1 A.2)
    obtain ⟨hB', hr'⟩ := Classical.choose_spec (d4b_exists_partner k A'.1 A'.2)
    obtain ⟨hB'', hr''⟩ := Classical.choose_spec (d4b_exists_partner k (A * A').1 (A * A').2)
    exact d4b_rel_unique k hk hB'' (Subgroup.mul_mem _ hB hB') hr'' (d4b_rel_mul k hr hr'))

theorem d4bΨ_mem
    [Finite k] (hk : Nat.card k = 8) (A : ↥(adjointGroup Tag.D4 k)) :
    d4bΨ k hk A ∈ d4bΩ k :=
  (Classical.choose_spec (d4b_exists_partner k A.1 A.2)).1

theorem d4bΨ_rel
    [Finite k] (hk : Nat.card k = 8) (A : ↥(adjointGroup Tag.D4 k)) :
    D4bRel k A.1 (d4bΨ k hk A) :=
  (Classical.choose_spec (d4b_exists_partner k A.1 A.2)).2

theorem d4bΨ_eq
    [Finite k] (hk : Nat.card k = 8) (A : ↥(adjointGroup Tag.D4 k)) {B : GL (Fin 8) k}
    (hB : B ∈ d4bΩ k) (h : D4bRel k A.1 B) : d4bΨ k hk A = B :=
  d4b_rel_unique k hk (d4bΨ_mem k hk A) hB (d4bΨ_rel k hk A) h

theorem d4bΨ_of_xOp
    [Finite k] (hk : Nat.card k = 8) (A : ↥(adjointGroup Tag.D4 k))
    (i : Fin Tag.D4.rank) (c : k)
    (h : (A.1 : Module.End k (RootModule Tag.D4 k)) = xOp Tag.D4 k i c) :
    d4bΨ k hk A = d4bNat k i true c :=
  d4bΨ_eq k hk A (d4bNat_mem k i true c) (d4b_rel_of_xOp k i c A.1 h)

theorem d4bΨ_of_yOp
    [Finite k] (hk : Nat.card k = 8) (A : ↥(adjointGroup Tag.D4 k))
    (i : Fin Tag.D4.rank) (c : k)
    (h : (A.1 : Module.End k (RootModule Tag.D4 k)) = yOp Tag.D4 k i c) :
    d4bΨ k hk A = d4bNat k i false c :=
  d4bΨ_eq k hk A (d4bNat_mem k i false c) (d4b_rel_of_yOp k i c A.1 h)

end Theta

end CFSG.Quasithin
