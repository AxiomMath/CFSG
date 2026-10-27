module

public import CFSG.RankThree.PartOne.FOC.TorusHom
public import CFSG.RankThree.PartOne.S11c.Sec66TorusPSU

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG Matrix
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo diagGL coe_diagGL isElementaryAbelian_range_comm
  commute_diagGL_swap)

section Abstract

theorem not_localRankLeTwo_of_torus_involution {T G : Type} [Group T] [Group G] {p : ℕ}
    {M : Type} [CommGroup M] (hMcard : Nat.card M = p) (hMp : ∀ y : M, y ^ p = 1)
    (φ : G →* T) (R : M × M × M →* G) (hR : Function.Injective (φ.comp R)) (u : G)
    (hu2 : u ^ 2 = 1) (hu1 : φ u ≠ 1) (hcomm : ∀ r, u * R r = R r * u) :
    ¬ LocalRankLeTwo p T := by
  intro hloc
  set Φ := φ.comp R with hΦ
  have hRel : IsElementaryAbelian p ↥Φ.range := isElementaryAbelian_range_comm Φ fun x =>
    Prod.ext (hMp x.1) (Prod.ext (hMp x.2.1) (hMp x.2.2))
  have hRcard : Nat.card ↥Φ.range = p ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hR).toEquiv, Nat.card_prod, Nat.card_prod,
      hMcard]
    ring
  have hU2 : orderOf (φ u) = 2 := by
    have h : (φ u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
    exact orderOf_eq_prime h hu1
  have hUne : Subgroup.zpowers (φ u) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hu1
  have hUp : IsPGroup 2 ↥(Subgroup.zpowers (φ u)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hU2, pow_one])
  refine hloc Φ.range hRel hRcard (Subgroup.zpowers (φ u)) hUne hUp ?_
  rintro _ ⟨x, rfl⟩
  have hxC : Φ x ∈ Subgroup.centralizer ({φ u} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    show φ (R x) * φ u = φ u * φ (R x)
    rw [← map_mul, ← map_mul, (hcomm x).symm]
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure] at hxC
  exact Subgroup.centralizer_le_normalizer _ hxC

end Abstract

section Matrices

variable {m : ℕ} {E : Type} [Field E]

@[expose] def torusEntry (m : ℕ) (t a b : Eˣ) : Fin m → Eˣ := fun i =>
  if i.val = 0 ∨ i.val = 1 then t else if i.val = 2 then a else if i.val = 3 then b
    else if i.val = 4 then (t ^ 2 * a * b)⁻¹ else 1

theorem torusEntry_mul (t a b t' a' b' : Eˣ) :
    torusEntry m (t * t') (a * a') (b * b') = torusEntry m t a b * torusEntry m t' a' b' := by
  funext i
  simp only [torusEntry, Pi.mul_apply]
  split_ifs
  · rfl
  · rfl
  · rfl
  · have : ((t * t') ^ 2 * (a * a') * (b * b')) = (t ^ 2 * a * b) * (t' ^ 2 * a' * b') := by
      rw [mul_pow]; ac_rfl
    rw [this, mul_inv]
  · simp

theorem torusEntry_one : torusEntry m (1 : Eˣ) 1 1 = 1 := by
  funext i
  simp only [torusEntry, Pi.one_apply]
  split_ifs <;> simp

theorem prod_torusEntry (hm : 5 ≤ m) (t a b : Eˣ) : ∏ i, torusEntry m t a b i = 1 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 5 := ⟨m - 5, by omega⟩
  simp [torusEntry, Fin.prod_univ_succ]
  group

@[expose] noncomputable def torusRep (m : ℕ) (E : Type) [Field E] (M : Subgroup Eˣ) :
    M × M × M →* GL (Fin m) E where
  toFun x := diagGL m E (torusEntry m (x.1 : Eˣ) (x.2.1 : Eˣ) (x.2.2 : Eˣ))
  map_one' := by
    show diagGL m E (torusEntry m ((1 : M) : Eˣ) ((1 : M) : Eˣ) ((1 : M) : Eˣ)) = 1
    rw [Subgroup.coe_one, torusEntry_one, map_one]
  map_mul' x y := by
    simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul, torusEntry_mul, map_mul]

theorem torusRep_apply (M : Subgroup Eˣ) (x : M × M × M) :
    torusRep m E M x = diagGL m E (torusEntry m (x.1 : Eˣ) (x.2.1 : Eˣ) (x.2.2 : Eˣ)) := rfl

theorem det_torusRep (hm : 5 ≤ m) (M : Subgroup Eˣ) (x : M × M × M) :
    GeneralLinearGroup.det (torusRep m E M x) = 1 := by
  apply Units.ext
  rw [torusRep_apply, GeneralLinearGroup.val_det_apply, coe_diagGL, Matrix.det_diagonal,
    ← Units.coe_prod, prod_torusEntry hm, Units.val_one]

theorem torusRep_injective (hm : 5 ≤ m) (M : Subgroup Eˣ) :
    Function.Injective (torusRep m E M) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hent : ∀ i, torusEntry m (x.1 : Eˣ) (x.2.1 : Eˣ) (x.2.2 : Eˣ) i = 1 := by
    intro i
    have h1 : ((torusRep m E M x : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i i = 1 := by
      rw [hx]
      simp
    rw [torusRep_apply, coe_diagGL, Matrix.diagonal_apply_eq] at h1
    exact Units.ext h1
  have h0 := hent ⟨0, by omega⟩
  have h2 := hent ⟨2, by omega⟩
  have h3 := hent ⟨3, by omega⟩
  simp only [torusEntry] at h0 h2 h3
  simp at h0 h2 h3
  exact Prod.ext h0 (Prod.ext h2 h3)

@[expose] noncomputable def invol (m : ℕ) (E : Type) [Field E] (hm : 3 ≤ m) : GL (Fin m) E :=
  Matrix.GeneralLinearGroup.swap E (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ *
    diagGL m E (Pi.mulSingle ⟨2, by omega⟩ (-1))

theorem invol_sq (hm : 3 ≤ m) : invol m E hm ^ 2 = 1 := by
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  set d : GL (Fin m) E := diagGL m E (Pi.mulSingle ⟨2, by omega⟩ (-1)) with hd
  have hcomm : Commute (Matrix.GeneralLinearGroup.swap E i₀ i₁) d := by
    rw [hd]
    refine (commute_diagGL_swap _ i₀ i₁ ?_).symm
    intro a
    by_cases ha0 : a = i₀
    · subst ha0
      simp [i₀, i₁, Fin.ext_iff]
    · by_cases ha1 : a = i₁
      · subst ha1
        simp [i₀, i₁, Fin.ext_iff]
      · rw [Equiv.swap_apply_of_ne_of_ne ha0 ha1]
  have hsw : Matrix.GeneralLinearGroup.swap E i₀ i₁ ^ 2 = 1 := by
    apply Units.ext
    rw [pow_two, Units.val_mul, Matrix.GeneralLinearGroup.val_swap, Matrix.swap_mul_self]
    rfl
  have hdd : d ^ 2 = 1 := by
    rw [hd, ← map_pow]
    have : (Pi.mulSingle (⟨2, by omega⟩ : Fin m) (-1 : Eˣ) : Fin m → Eˣ) ^ 2 = 1 := by
      funext i
      by_cases hi : i = ⟨2, by omega⟩
      · subst hi; simp
      · simp [Pi.mulSingle_eq_of_ne hi]
    rw [this, map_one]
  unfold invol
  rw [← hd, hcomm.mul_pow, hsw, hdd, one_mul]

theorem det_invol (hm : 3 ≤ m) : GeneralLinearGroup.det (invol m E hm) = 1 := by
  unfold invol
  rw [map_mul]
  have h1 : GeneralLinearGroup.det (Matrix.GeneralLinearGroup.swap E (⟨0, by omega⟩ : Fin m)
      ⟨1, by omega⟩) = -1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_swap, Matrix.swap,
      Matrix.det_permutation, Equiv.Perm.sign_swap (by simp [Fin.ext_iff])]
    simp
  have h2 : GeneralLinearGroup.det (diagGL m E (Pi.mulSingle (⟨2, by omega⟩ : Fin m) (-1))) = -1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, coe_diagGL, Matrix.det_diagonal, ← Units.coe_prod]
    simp
  rw [h1, h2]
  simp

theorem invol_commute_torusRep (hm : 5 ≤ m) (M : Subgroup Eˣ) (x : M × M × M) :
    Commute (invol m E (by omega)) (torusRep m E M x) := by
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  unfold invol
  refine Commute.mul_left ?_ ?_
  · rw [torusRep_apply]
    refine (commute_diagGL_swap _ i₀ i₁ ?_).symm
    intro a
    by_cases ha0 : a = i₀
    · subst ha0
      simp [torusEntry, i₀, i₁, Equiv.swap_apply_left]
    · by_cases ha1 : a = i₁
      · subst ha1
        simp [torusEntry, i₀, i₁, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne ha0 ha1]
  · rw [torusRep_apply]
    exact diagGL_commute _ _

theorem invol_apply_one_zero (hm : 3 ≤ m) :
    ((invol m E hm : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) ⟨1, by omega⟩ ⟨0, by omega⟩ = 1 := by
  unfold invol
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_swap, coe_diagGL, Matrix.mul_diagonal]
  simp [Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Fin.ext_iff]

end Matrices

section Unitary

variable {m : ℕ} {E : Type} [Field E] (σ : E →+* E)

@[expose] def UnitaryMat (A : Matrix (Fin m) (Fin m) E) : Prop := (A.map σ)ᵀ * A = 1

theorem UnitaryMat.mul {A B : Matrix (Fin m) (Fin m) E} (hA : UnitaryMat σ A)
    (hB : UnitaryMat σ B) : UnitaryMat σ (A * B) := by
  unfold UnitaryMat at *
  rw [Matrix.map_mul, Matrix.transpose_mul]
  calc (B.map σ)ᵀ * (A.map σ)ᵀ * (A * B) = (B.map σ)ᵀ * ((A.map σ)ᵀ * A) * B := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

theorem unitaryMat_diagonal (d : Fin m → E) (hd : ∀ i, σ (d i) * d i = 1) :
    UnitaryMat σ (diagonal d) := by
  unfold UnitaryMat
  rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  exact hd i

theorem unitaryMat_swap (i j : Fin m) : UnitaryMat σ (Matrix.swap E i j) := by
  unfold UnitaryMat
  have h : (Matrix.swap E i j).map σ = Matrix.swap E i j := by
    ext a b
    simp [Matrix.swap, Matrix.map_apply, PEquiv.toMatrix_apply, Equiv.Perm.permMatrix,
      apply_ite]
  rw [h, Matrix.transpose_swap, Matrix.swap_mul_self]

theorem norm_one_mul {y z : Eˣ} (hy : σ y * y = 1) (hz : σ z * z = 1) :
    σ ((y * z : Eˣ) : E) * ((y * z : Eˣ) : E) = 1 := by
  rw [Units.val_mul, map_mul]
  calc σ y * σ z * (y * z) = (σ y * y) * (σ z * z) := by ring
    _ = 1 := by rw [hy, hz, one_mul]

theorem norm_one_inv {y : Eˣ} (hy : σ y * y = 1) : σ ((y⁻¹ : Eˣ) : E) * ((y⁻¹ : Eˣ) : E) = 1 := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, ← _root_.mul_inv_rev, mul_comm, hy, inv_one]

theorem norm_one_torusEntry (M : Subgroup Eˣ) (hM : ∀ y ∈ M, σ y * y = 1) (t a b : M) (i : Fin m) :
    σ ((torusEntry m (t : Eˣ) (a : Eˣ) (b : Eˣ) i : Eˣ) : E) *
      ((torusEntry m (t : Eˣ) (a : Eˣ) (b : Eˣ) i : Eˣ) : E) = 1 := by
  simp only [torusEntry]
  split_ifs
  · exact hM _ t.2
  · exact hM _ a.2
  · exact hM _ b.2
  · rw [pow_two]
    exact norm_one_inv σ (norm_one_mul σ (norm_one_mul σ
      (norm_one_mul σ (hM _ t.2) (hM _ t.2)) (hM _ a.2)) (hM _ b.2))
  · simp

theorem unitaryMat_torusRep (M : Subgroup Eˣ) (hM : ∀ y ∈ M, σ y * y = 1) (x : M × M × M) :
    UnitaryMat σ ((torusRep m E M x : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) := by
  rw [torusRep_apply, coe_diagGL]
  exact unitaryMat_diagonal σ _ fun i => norm_one_torusEntry σ M hM _ _ _ i

theorem unitaryMat_invol (hm : 3 ≤ m) :
    UnitaryMat σ ((invol m E hm : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) := by
  unfold invol
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_swap, coe_diagGL]
  refine UnitaryMat.mul σ (unitaryMat_swap σ _ _) (unitaryMat_diagonal σ _ fun i => ?_)
  by_cases hi : i = (⟨2, by omega⟩ : Fin m)
  · subst hi
    simp
  · simp [Pi.mulSingle_eq_of_ne hi]

end Unitary

end CFSG.RankThree.PartOne.FOC
