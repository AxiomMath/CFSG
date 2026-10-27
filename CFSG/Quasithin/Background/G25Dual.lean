module

public import CFSG.Quasithin.Background.G13Perm
public import CFSG.Quasithin.Background.G2SL3

public section

namespace CFSG.Quasithin

open Matrix CFSG.Quasithin.G1 CFSG.Quasithin.SL2Model CFSG.Quasithin.SL3Model
open scoped MatrixGroups

section Dual

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def slT (A : SL(n, F)) : SL(n, F) := Matrix.SpecialLinearGroup.transpose A

theorem slT_coe (A : SL(n, F)) :
    (slT A : Matrix (Fin n) (Fin n) F) = (A : Matrix (Fin n) (Fin n) F)ᵀ :=
  rfl

theorem slT_mul (A B : SL(n, F)) : slT (A * B) = slT B * slT A := by
  apply Subtype.ext
  simp only [slT_coe, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem slT_one : slT (1 : SL(n, F)) = 1 := by
  apply Subtype.ext
  simp only [slT_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]

theorem slT_slT (A : SL(n, F)) : slT (slT A) = A := by
  apply Subtype.ext
  simp only [slT_coe, Matrix.transpose_transpose]

theorem slT_inv (A : SL(n, F)) : slT A⁻¹ = (slT A)⁻¹ := by
  rw [eq_comm, inv_eq_iff_mul_eq_one, ← slT_mul, inv_mul_cancel, slT_one]

variable (F n) in
@[expose] def dualHom : SL(n, F) →* SL(n, F) where
  toFun g := slT g⁻¹
  map_one' := by rw [inv_one, slT_one]
  map_mul' g h := by rw [_root_.mul_inv_rev, slT_mul]

theorem dualHom_apply (g : SL(n, F)) : dualHom F n g = slT g⁻¹ := rfl

theorem dualHom_dualHom (g : SL(n, F)) : dualHom F n (dualHom F n g) = g := by
  rw [dualHom_apply, dualHom_apply, ← slT_inv, inv_inv, slT_slT]

theorem dualHom_smul_dot (g : SL(n, F)) (f v : Fin n → F) :
    (dualHom F n g • f) ⬝ᵥ (g • v) = f ⬝ᵥ v := by
  change ((dualHom F n g : Matrix (Fin n) (Fin n) F) *ᵥ f) ⬝ᵥ
    ((g : Matrix (Fin n) (Fin n) F) *ᵥ v) = _
  rw [dualHom_apply, slT_coe, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul]
  have : ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  rw [this, Matrix.vecMul_one]

theorem dualHom_transvection [CharP F 2] {a b : Fin n} (hab : a ≠ b) (c : F) :
    dualHom F n (Matrix.SpecialLinearGroup.transvection hab c) =
      Matrix.SpecialLinearGroup.transvection hab.symm c := by
  rw [dualHom_apply, Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]
  apply Subtype.ext
  rw [slT_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

theorem wS_entry [CharP F 2] {i j : Fin n} (hij : i ≠ j) (a b : Fin n) :
    (wS F hij : Matrix (Fin n) (Fin n) F) a b = if Equiv.swap i j a = b then 1 else 0 := by
  have := wS_smul (F := F) hij (Pi.single b 1) a
  rw [G1.smul_eq_mulVec', Matrix.mulVec_single_one] at this
  simpa [Pi.single_apply] using this

theorem wS_smul_single [CharP F 2] {i j : Fin n} (hij : i ≠ j) (m : Fin n) :
    wS F hij • (Pi.single m 1 : Fin n → F) = Pi.single (Equiv.swap i j m) 1 := by
  funext k
  rw [wS_smul]
  simp only [Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem slT_wS [CharP F 2] {i j : Fin n} (hij : i ≠ j) : slT (wS F hij) = wS F hij := by
  apply Subtype.ext
  rw [slT_coe]
  ext a b
  rw [Matrix.transpose_apply, wS_entry, wS_entry]
  have : (Equiv.swap i j b = a) ↔ (Equiv.swap i j a = b) := by
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  simp only [this]

theorem dualHom_wS [CharP F 2] {i j : Fin n} (hij : i ≠ j) : dualHom F n (wS F hij) = wS F hij := by
  have h1 : (wS F hij)⁻¹ = wS F hij := inv_eq_of_mul_eq_one_right (wS_mul_self hij)
  rw [dualHom_apply, h1, slT_wS]

@[expose] def DiagLike (g : SL(n, F)) : Prop :=
  ∀ a b : Fin n, a ≠ b → (g : Matrix (Fin n) (Fin n) F) a b = 0

theorem DiagLike.slT {g : SL(n, F)} (h : DiagLike g) : DiagLike (slT g) := fun a b hab => by
  rw [slT_coe, Matrix.transpose_apply]
  exact h b a hab.symm

theorem DiagLike.inv {g : SL(n, F)} (h : DiagLike g) : DiagLike g⁻¹ := fun a b hab => by
  have hg : (g : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun i => (g : Matrix (Fin n) (Fin n) F) i i) := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [Matrix.diagonal_apply_ne _ hxy]
      exact h x y hxy
  rw [Matrix.SpecialLinearGroup.coe_inv, hg, Matrix.adjugate_diagonal]
  exact Matrix.diagonal_apply_ne _ hab

theorem DiagLike.smul_single {g : SL(n, F)} (h : DiagLike g) (m : Fin n) :
    ∃ c : F, g • (Pi.single m 1 : Fin n → F) = c • (Pi.single m 1 : Fin n → F) := by
  refine ⟨(g : Matrix (Fin n) (Fin n) F) m m, ?_⟩
  funext a
  rw [G1.smul_eq_mulVec', Matrix.mulVec_single_one]
  by_cases ham : a = m
  · subst ham
    simp
  · simp [ham, h a m ham]

theorem DiagLike.dualHom {g : SL(n, F)} (h : DiagLike g) : DiagLike (dualHom F n g) :=
  (h.inv).slT

theorem diagLike_embSL {n : ℕ} {i j : Fin n} (hij : i ≠ j) (d : Fˣ) :
    DiagLike (embSL hij (dgm d)) := by
  intro a b hab
  have hd : (dgm d : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(d : F), ((d⁻¹ : Fˣ) : F)] := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.diagonal]
  rw [embSL_coe, hd, emb_diagonal hij]
  exact Matrix.diagonal_apply_ne _ hab

end Dual

section Copies

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def copiesHom (s : ℕ) (A : SL(n, F)) :
    Multiplicative (Fin s → Fin n → F) →* Multiplicative (Fin s → Fin n → F) where
  toFun v := Multiplicative.ofAdd (fun l => A • Multiplicative.toAdd v l)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext l
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext l
    simp [smul_add]

theorem copiesHom_toAdd (s : ℕ) (A : SL(n, F)) (v : Multiplicative (Fin s → Fin n → F))
    (l : Fin s) :
    Multiplicative.toAdd (copiesHom s A v) l = A • Multiplicative.toAdd v l := rfl

theorem copiesHom_mul (s : ℕ) (A B : SL(n, F)) (v : Multiplicative (Fin s → Fin n → F)) :
    copiesHom s (A * B) v = copiesHom s A (copiesHom s B v) := by
  apply Multiplicative.toAdd.injective
  funext l
  simp [copiesHom_toAdd, mul_smul]

theorem copiesHom_one (s : ℕ) (v : Multiplicative (Fin s → Fin n → F)) :
    copiesHom s (1 : SL(n, F)) v = v := by
  apply Multiplicative.toAdd.injective
  funext l
  simp [copiesHom_toAdd]

theorem copiesHom_injective (s : ℕ) (A : SL(n, F)) : Function.Injective (copiesHom s A) := by
  intro a b h
  have h1 := congrArg (copiesHom s A⁻¹) h
  rwa [← copiesHom_mul, ← copiesHom_mul, inv_mul_cancel, copiesHom_one, copiesHom_one] at h1

theorem copiesHom_surjective (s : ℕ) (A : SL(n, F)) : Function.Surjective (copiesHom s A) := by
  intro b
  refine ⟨copiesHom s A⁻¹ b, ?_⟩
  rw [← copiesHom_mul, mul_inv_cancel, copiesHom_one]

theorem copiesHom_eq_one_iff (s : ℕ) (A : SL(n, F)) (v : Multiplicative (Fin s → Fin n → F)) :
    copiesHom s A v = 1 ↔ v = 1 := by
  constructor
  · intro h
    exact copiesHom_injective s A (h.trans (map_one (copiesHom s A)).symm)
  · rintro rfl
    exact map_one _

theorem copiesHom_equivariant {G : Type*} [Group G] {s : ℕ} {M Sx : Subgroup G}
    (β : ↥M →* SL(n, F)) (κ : SL(n, F) →* SL(n, F)) (hκ : ∀ g, κ (κ g) = g) (Q : SL(n, F))
    (φ : ↥Sx →* Multiplicative (Fin s → Fin n → F))
    (hφ : ∀ (m : ↥M) (g : SL(n, F)) (x y : ↥Sx), Q * κ g * Q⁻¹ = β m →
      (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
        φ y = Multiplicative.ofAdd (fun l => g • Multiplicative.toAdd (φ x) l))
    (m : ↥M) (x y : ↥Sx) (hy : (y : G) = (m : G) * (x : G) * (m : G)⁻¹) :
    (copiesHom s (κ Q)).comp φ y =
      Multiplicative.ofAdd
        (fun l => κ (β m) • Multiplicative.toAdd ((copiesHom s (κ Q)).comp φ x) l) := by
  have hg : Q * κ (κ (Q⁻¹ * β m * Q)) * Q⁻¹ = β m := by
    rw [hκ]
    group
  have h1 := hφ m (κ (Q⁻¹ * β m * Q)) x y hg hy
  apply Multiplicative.toAdd.injective
  funext l
  rw [MonoidHom.comp_apply, copiesHom_toAdd, h1]
  simp only [MonoidHom.comp_apply, copiesHom_toAdd, toAdd_ofAdd]
  rw [← mul_smul, ← mul_smul, map_mul, map_mul, map_inv]
  congr 1
  group

theorem forall_coord_eq_zero_iff (Q : SL(n, F)) (k : Fin n) (y : Fin n → F) :
    (∀ j, j ≠ k → y j = 0) ↔ ∃ c : F, Q • y = c • (Q • (Pi.single k 1 : Fin n → F)) := by
  constructor
  · intro h
    refine ⟨y k, ?_⟩
    have hy : y = y k • (Pi.single k 1 : Fin n → F) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp
      · simp [hj, h j hj]
    conv_lhs => rw [hy]
    rw [smul_comm]
  · rintro ⟨c, hc⟩
    have h1 : Q • y = Q • (c • (Pi.single k 1 : Fin n → F)) := by
      rw [hc]
      exact (smul_comm Q c _).symm
    have h2 : y = c • (Pi.single k 1 : Fin n → F) := MulAction.injective Q h1
    intro j hj
    rw [h2]
    simp [hj]

theorem dualHom_smul_dot_single (Q : SL(n, F)) (y : Fin n → F) (i : Fin n) :
    (dualHom F n Q • y) ⬝ᵥ (Q • (Pi.single i 1 : Fin n → F)) = y i := by
  rw [dualHom_smul_dot, dotProduct_single_one]

end Copies

end CFSG.Quasithin
