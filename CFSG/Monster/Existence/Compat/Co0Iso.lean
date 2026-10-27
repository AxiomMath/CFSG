module

public import CFSG.Monster.Existence.Compat.LeechLattice
public import CFSG.Monster.ScalarKernel

public noncomputable section

namespace CFSG.Monster.Existence.Compat

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.ScalarKernel CFSG.Open Matrix

abbrev Lat : Type := ↥(codeLatticeSubgroup allOnes_mem_C)

@[expose] def conjLin {M N : Type*} [AddCommGroup M] [AddCommGroup N] (p : M ≃ₗ[ℤ] N) :
    (M ≃ₗ[ℤ] M) ≃* (N ≃ₗ[ℤ] N) where
  toFun e := p.symm.trans (e.trans p)
  invFun e := p.trans (e.trans p.symm)
  left_inv e := by ext x; simp
  right_inv e := by ext x; simp
  map_mul' e f := by ext x; simp

theorem conjLin_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N] (p : M ≃ₗ[ℤ] N)
    (e : M ≃ₗ[ℤ] M) (y : N) : conjLin p e y = p (e (p.symm y)) := rfl

theorem conjLin_symm_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N] (p : M ≃ₗ[ℤ] N)
    (e : N ≃ₗ[ℤ] N) (x : M) : (conjLin p).symm e x = p.symm (e (p x)) := rfl

theorem mat_inv (g : latticeO) : mat g⁻¹ = (mat g)ᵀ := by
  have h1 : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  calc mat g⁻¹ = mat g⁻¹ * (mat g * (mat g)ᵀ) := by rw [mat_mul_transpose, mul_one]
    _ = (mat g⁻¹ * mat g) * (mat g)ᵀ := by rw [Matrix.mul_assoc]
    _ = (mat g)ᵀ := by rw [h1, one_mul]

theorem mat_transpose_mul (g : latticeO) : (mat g)ᵀ * mat g = 1 :=
  mul_eq_one_comm.1 (mat_mul_transpose g)

@[expose] def actEquiv (g : latticeO) :
    Lat ≃+ Lat where
  toFun := latHom g⁻¹
  invFun := latHom g
  left_inv u := by
    rw [← latHom_mul, inv_mul_cancel, latHom_one]
  right_inv u := by
    rw [← latHom_mul, mul_inv_cancel, latHom_one]
  map_add' u v := map_add _ u v

@[expose] def actLin (g : latticeO) :
    Lat ≃ₗ[ℤ] Lat :=
  (actEquiv g).toIntLinearEquiv

theorem ratVec_actLin (g : latticeO) (u : Lat) :
    ratVec ((actLin g u : Lat) : Fin 24 → ℤ) =
      mat g *ᵥ ratVec (u : Fin 24 → ℤ) := by
  have h := ratVec_latHom g⁻¹ u
  rw [mat_inv, vecMul_transpose] at h
  exact h

theorem actLin_mul (g h : latticeO) : actLin (g * h) = actLin g * actLin h := by
  refine LinearEquiv.ext fun u => ?_
  show latHom (g * h)⁻¹ u = latHom g⁻¹ (latHom h⁻¹ u)
  rw [_root_.mul_inv_rev, latHom_mul]

theorem actLin_one : actLin 1 = 1 := by
  refine LinearEquiv.ext fun u => ?_
  show latHom (1 : latticeO)⁻¹ u = u
  rw [inv_one, latHom_one]

@[expose] def actHom : latticeO →* (Lat ≃ₗ[ℤ] Lat) where
  toFun := actLin
  map_one' := actLin_one
  map_mul' := actLin_mul

@[expose] def ipZ (a b : Fin 24 → ℤ) : ℤ := ∑ i, a i * b i

theorem dot_vecMul_vecMul {M : Matrix (Fin 24) (Fin 24) ℚ} (hM : M * Mᵀ = 1)
    (x y : Fin 24 → ℚ) : (x ᵥ* M) ⬝ᵥ (y ᵥ* M) = x ⬝ᵥ y := by
  have h := codeForm_vecMul_vecMul hM x y
  rw [codeForm_eq_dotProduct, codeForm_eq_dotProduct] at h
  exact (div_left_inj' (by norm_num : (8 : ℚ) ≠ 0)).1 h

theorem ratVec_dot (a b : Fin 24 → ℤ) : ratVec a ⬝ᵥ ratVec b = (ipZ a b : ℚ) := by
  simp [ipZ, dotProduct, ratVec]

theorem ipZ_actLin (g : latticeO) (u v : Lat) :
    ipZ (actLin g u : Fin 24 → ℤ) (actLin g v : Fin 24 → ℤ) =
      ipZ (u : Fin 24 → ℤ) (v : Fin 24 → ℤ) := by
  apply Int.cast_injective (α := ℚ)
  rw [← ratVec_dot, ← ratVec_dot, ratVec_actLin, ratVec_actLin, ← vecMul_transpose,
    ← vecMul_transpose]
  exact dot_vecMul_vecMul (M := (mat g)ᵀ)
    (by rw [transpose_transpose]; exact mat_transpose_mul g) _ _

theorem sum_sq_actLin (g : latticeO) (u : Lat) :
    ∑ i, ((actLin g u : Lat) : Fin 24 → ℤ) i ^ 2 = ∑ i, (u : Fin 24 → ℤ) i ^ 2 := by
  have h := ipZ_actLin g u u
  simpa only [ipZ, sq] using h

@[expose] def leechLin : Lat ≃ₗ[ℤ] monsterLeech :=
  (leechEquiv.toIntLinearEquiv : mogLattice ≃ₗ[ℤ] monsterLeech)

theorem coe_leechLin (u : Lat) : ((leechLin u : monsterLeech) : Fin 24 → ℤ) = permZ u := rfl

theorem coe_leechLin_symm (v : monsterLeech) :
    ((leechLin.symm v : Lat) : Fin 24 → ℤ) = permZ.symm v := rfl

theorem monsterLeechNorm_leechLin (u : Lat) :
    monsterLeechNorm (leechLin u) = ∑ i, (u : Fin 24 → ℤ) i ^ 2 := by
  rw [monsterLeechNorm, coe_leechLin, sum_permZ_sq]

@[expose] def co0Hom0 : latticeO →* (monsterLeech ≃ₗ[ℤ] monsterLeech) :=
  (conjLin leechLin).toMonoidHom.comp actHom

theorem co0Hom0_apply (g : latticeO) (v : monsterLeech) :
    co0Hom0 g v = leechLin (actLin g (leechLin.symm v)) := rfl

theorem co0Hom0_mem (g : latticeO) : co0Hom0 g ∈ monsterCo0 := by
  intro v
  rw [co0Hom0_apply, monsterLeechNorm_leechLin, sum_sq_actLin]
  conv_rhs => rw [← leechLin.apply_symm_apply v]
  rw [monsterLeechNorm_leechLin]

@[expose] def co0Hom : latticeO →* monsterCo0 :=
  co0Hom0.codRestrict monsterCo0 co0Hom0_mem

theorem coe_co0Hom (g : latticeO) : ((co0Hom g : monsterCo0) : monsterLeech ≃ₗ[ℤ] monsterLeech) =
    co0Hom0 g := rfl

@[expose] def eight (j : Fin 24) : Lat :=
  ⟨(8 : ℤ) • Pi.single j 1, smul_eight_mem_codeLattice _⟩

theorem coe_eight (j : Fin 24) : ((eight j : Lat) : Fin 24 → ℤ) = (8 : ℤ) • Pi.single j 1 := rfl

theorem ratVec_eight (j : Fin 24) :
    ratVec ((eight j : Lat) : Fin 24 → ℤ) = (8 : ℚ) • Pi.single j 1 := by
  funext i
  simp only [coe_eight, ratVec, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem eq_one_of_mulVec_eight {M : Matrix (Fin 24) (Fin 24) ℚ}
    (h : ∀ j, M *ᵥ ratVec ((eight j : Lat) : Fin 24 → ℤ) = ratVec ((eight j : Lat) : Fin 24 → ℤ)) :
    M = 1 := by
  ext i j
  have hj := congrFun (h j) i
  rw [ratVec_eight, mulVec_smul, Pi.smul_apply, mulVec_single_one, Pi.smul_apply] at hj
  have h8 : (M i j) = (Pi.single j 1 : Fin 24 → ℚ) i := by
    simpa [Matrix.col_apply] using hj
  rw [h8, Pi.single_apply, one_apply]

theorem co0Hom_injective : Function.Injective co0Hom := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h0 : co0Hom0 g = 1 := congrArg Subtype.val hg
  have h1 : actLin g = 1 := (conjLin leechLin).injective (by rw [map_one]; exact h0)
  have hmat : mat g = 1 := by
    refine eq_one_of_mulVec_eight fun j => ?_
    rw [← ratVec_actLin, h1]
    rfl
  exact mat_injective (hmat.trans mat_one.symm)

section Extend

variable (e : Lat →+ Lat)

@[expose] def ext8 : (Fin 24 → ℤ) →+ (Fin 24 → ℚ) where
  toFun x := fun i =>
    (((e ⟨(8 : ℤ) • x, smul_eight_mem_codeLattice x⟩ : Lat) : Fin 24 → ℤ) i : ℚ) / 8
  map_zero' := by
    funext i
    have h : (⟨(8 : ℤ) • (0 : Fin 24 → ℤ), smul_eight_mem_codeLattice 0⟩ : Lat) = 0 :=
      Subtype.ext (smul_zero _)
    show (((e ⟨(8 : ℤ) • (0 : Fin 24 → ℤ), smul_eight_mem_codeLattice 0⟩ : Lat) :
      Fin 24 → ℤ) i : ℚ) / 8 = 0
    rw [h, map_zero]
    simp
  map_add' x y := by
    funext i
    have h : (⟨(8 : ℤ) • (x + y), smul_eight_mem_codeLattice _⟩ : Lat) =
        ⟨(8 : ℤ) • x, smul_eight_mem_codeLattice _⟩ +
          ⟨(8 : ℤ) • y, smul_eight_mem_codeLattice _⟩ :=
      Subtype.ext (smul_add _ _ _)
    simp only [h, map_add, AddSubgroup.coe_add, Pi.add_apply, Int.cast_add, add_div]

theorem ext8_apply (x : Fin 24 → ℤ) (i : Fin 24) :
    ext8 e x i =
      (((e ⟨(8 : ℤ) • x, smul_eight_mem_codeLattice x⟩ : Lat) : Fin 24 → ℤ) i : ℚ) / 8 := rfl

theorem ext8_coe (u : Lat) : ext8 e (u : Fin 24 → ℤ) = ratVec ((e u : Lat) : Fin 24 → ℤ) := by
  funext i
  have h : (⟨(8 : ℤ) • (u : Fin 24 → ℤ), smul_eight_mem_codeLattice _⟩ : Lat) = (8 : ℤ) • u :=
    Subtype.ext (AddSubgroup.coe_zsmul _ _ _).symm
  rw [ext8_apply, h, map_zsmul, AddSubgroup.coe_zsmul]
  simp [ratVec]

@[expose] def matOf : Matrix (Fin 24) (Fin 24) ℚ := Matrix.of fun i j => ext8 e (Pi.single j 1) i

theorem ext8_eq_mulVec (x : Fin 24 → ℤ) : ext8 e x = matOf e *ᵥ ratVec x := by
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin 24 → ℤ) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  conv_lhs => rw [hx]
  rw [map_sum]
  funext i
  simp only [map_zsmul, Finset.sum_apply, Pi.smul_apply]
  simp only [zsmul_eq_mul, mulVec, dotProduct, matOf, of_apply, ratVec]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem ratVec_eq_matOf_mulVec (u : Lat) :
    ratVec ((e u : Lat) : Fin 24 → ℤ) = matOf e *ᵥ ratVec (u : Fin 24 → ℤ) := by
  rw [← ext8_coe, ext8_eq_mulVec]

theorem ipZ_smul_eight (x y : Fin 24 → ℤ) :
    ipZ ((8 : ℤ) • x) ((8 : ℤ) • y) = 64 * ipZ x y := by
  simp only [ipZ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ipZ_add_self (x y : Fin 24 → ℤ) :
    ipZ (x + y) (x + y) = ipZ x x + ipZ y y + 2 * ipZ x y := by
  simp only [ipZ, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ipZ_eq_of_self {e : Lat →+ Lat} (hn : ∀ u : Lat, ipZ (e u : Fin 24 → ℤ) (e u : Fin 24 → ℤ) =
    ipZ (u : Fin 24 → ℤ) (u : Fin 24 → ℤ)) (a b : Lat) :
    ipZ (e a : Fin 24 → ℤ) (e b : Fin 24 → ℤ) = ipZ (a : Fin 24 → ℤ) (b : Fin 24 → ℤ) := by
  have h1 := hn (a + b)
  rw [map_add] at h1
  simp only [AddSubgroup.coe_add, ipZ_add_self, hn a, hn b] at h1
  linarith

theorem ext8_dot {e : Lat →+ Lat}
    (hdot : ∀ a b : Lat, ipZ (e a : Fin 24 → ℤ) (e b : Fin 24 → ℤ) =
      ipZ (a : Fin 24 → ℤ) (b : Fin 24 → ℤ)) (x y : Fin 24 → ℤ) :
    ext8 e x ⬝ᵥ ext8 e y = (ipZ x y : ℚ) := by
  have h1 : ext8 e x ⬝ᵥ ext8 e y =
      (ipZ ((e ⟨(8 : ℤ) • x, smul_eight_mem_codeLattice x⟩ : Lat) : Fin 24 → ℤ)
        ((e ⟨(8 : ℤ) • y, smul_eight_mem_codeLattice y⟩ : Lat) : Fin 24 → ℤ) : ℚ) / 64 := by
    simp only [dotProduct, ext8_apply, ipZ, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, hdot]
  show ((ipZ ((8 : ℤ) • x) ((8 : ℤ) • y) : ℤ) : ℚ) / 64 = _
  rw [ipZ_smul_eight]
  push_cast
  ring

variable {e}

theorem ipZ_single (j k : Fin 24) :
    ipZ (Pi.single j 1 : Fin 24 → ℤ) (Pi.single k 1 : Fin 24 → ℤ) = if j = k then 1 else 0 := by
  simp only [ipZ, Pi.single_apply]
  by_cases h : j = k
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem matOf_transpose_mul
    (hdot : ∀ a b : Lat, ipZ (e a : Fin 24 → ℤ) (e b : Fin 24 → ℤ) =
      ipZ (a : Fin 24 → ℤ) (b : Fin 24 → ℤ)) : (matOf e)ᵀ * matOf e = 1 := by
  ext j k
  have h := ext8_dot hdot (Pi.single j 1) (Pi.single k 1)
  rw [ipZ_single] at h
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero] at h
  rw [Matrix.mul_apply, one_apply]
  simp only [transpose_apply, matOf, of_apply]
  exact h

theorem matOf_mul_transpose
    (hdot : ∀ a b : Lat, ipZ (e a : Fin 24 → ℤ) (e b : Fin 24 → ℤ) =
      ipZ (a : Fin 24 → ℤ) (b : Fin 24 → ℤ)) : matOf e * (matOf e)ᵀ = 1 :=
  mul_eq_one_comm.1 (matOf_transpose_mul hdot)

end Extend

theorem vecMul_eq_transpose_mulVec (M : Matrix (Fin 24) (Fin 24) ℚ) (x : Fin 24 → ℚ) :
    x ᵥ* M = Mᵀ *ᵥ x := by
  simpa using vecMul_transpose Mᵀ x

theorem exists_actLin_eq (e : Lat ≃ₗ[ℤ] Lat)
    (hn : ∀ u : Lat, ipZ (e u : Fin 24 → ℤ) (e u : Fin 24 → ℤ) =
      ipZ (u : Fin 24 → ℤ) (u : Fin 24 → ℤ)) :
    ∃ g : latticeO, actLin g = e := by
  have hdot : ∀ a b : Lat, ipZ ((e.toAddEquiv : Lat →+ Lat) a : Fin 24 → ℤ)
      ((e.toAddEquiv : Lat →+ Lat) b : Fin 24 → ℤ) = ipZ (a : Fin 24 → ℤ) (b : Fin 24 → ℤ) :=
    ipZ_eq_of_self (e := (e.toAddEquiv : Lat →+ Lat)) hn
  set M := matOf (e.toAddEquiv : Lat →+ Lat) with hM
  have hTM : Mᵀ * M = 1 := matOf_transpose_mul hdot
  have hMT : M * Mᵀ = 1 := matOf_mul_transpose hdot
  have hact : ∀ u : Lat, ratVec ((e u : Lat) : Fin 24 → ℤ) = M *ᵥ ratVec (u : Fin 24 → ℤ) :=
    fun u => ratVec_eq_matOf_mulVec (e.toAddEquiv : Lat →+ Lat) u
  have hL : (fun x => x ᵥ* M) '' latticeQ = latticeQ := by
    ext x
    constructor
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨((e.symm ⟨w, hw⟩ : Lat) : Fin 24 → ℤ), (e.symm ⟨w, hw⟩).2, ?_⟩
      have h1 := hact (e.symm ⟨w, hw⟩)
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : ratVec w = M *ᵥ ratVec ((e.symm ⟨w, hw⟩ : Lat) : Fin 24 → ℤ) := h1
      show _ = ratVec w ᵥ* M
      rw [vecMul_eq_transpose_mulVec, h2, mulVec_mulVec, hTM, one_mulVec]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨ratVec ((e ⟨w, hw⟩ : Lat) : Fin 24 → ℤ), ⟨_, (e ⟨w, hw⟩).2, rfl⟩, ?_⟩
      show ratVec ((e ⟨w, hw⟩ : Lat) : Fin 24 → ℤ) ᵥ* M = ratVec w
      rw [vecMul_eq_transpose_mulVec, hact ⟨w, hw⟩, mulVec_mulVec, hTM, one_mulVec]
  refine ⟨mkO M hMT hL, LinearEquiv.ext fun u => Subtype.ext (ratVec_injective ?_)⟩
  rw [ratVec_actLin, mat_mkO, hact]

theorem co0Hom_surjective : Function.Surjective co0Hom := by
  rintro ⟨e₀, he₀⟩
  set e : Lat ≃ₗ[ℤ] Lat := (conjLin leechLin).symm e₀ with he
  have hn : ∀ u : Lat, ipZ (e u : Fin 24 → ℤ) (e u : Fin 24 → ℤ) =
      ipZ (u : Fin 24 → ℤ) (u : Fin 24 → ℤ) := by
    intro u
    have h2 : leechLin (e u) = e₀ (leechLin u) := by
      rw [he, conjLin_symm_apply, LinearEquiv.apply_symm_apply]
    have h3 := monsterLeechNorm_leechLin (e u)
    rw [h2, he₀ (leechLin u), monsterLeechNorm_leechLin u] at h3
    simpa only [ipZ, sq] using h3.symm
  obtain ⟨g, hg⟩ := exists_actLin_eq e hn
  refine ⟨g, Subtype.ext ?_⟩
  rw [coe_co0Hom, co0Hom0, MonoidHom.comp_apply]
  show conjLin leechLin (actLin g) = e₀
  rw [hg, he, MulEquiv.apply_symm_apply]

@[expose] def co0Equiv : latticeO ≃* monsterCo0 :=
  MulEquiv.ofBijective co0Hom ⟨co0Hom_injective, co0Hom_surjective⟩

theorem co0Equiv_apply (g : latticeO) : co0Equiv g = co0Hom g := rfl

theorem actLin_negOneO (u : Lat) : actLin negOneO u = -u := by
  refine Subtype.ext (ratVec_injective ?_)
  rw [ratVec_actLin, mat_negOneO, AddSubgroup.coe_neg, ratVec_neg, neg_mulVec, one_mulVec]

@[expose] def negCo0 : monsterCo0 :=
  ⟨LinearEquiv.neg ℤ, fun v => by
    simp only [monsterLeechNorm, LinearEquiv.neg_apply, AddSubgroup.coe_neg, Pi.neg_apply, neg_sq]⟩

theorem coe_negCo0 (v : monsterLeech) :
    ((negCo0 : monsterCo0) : monsterLeech ≃ₗ[ℤ] monsterLeech) v = -v := rfl

theorem co0Equiv_negOneO : co0Equiv negOneO = negCo0 := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  show leechLin (actLin negOneO (leechLin.symm v)) = -v
  rw [actLin_negOneO, map_neg, LinearEquiv.apply_symm_apply]

end CFSG.Monster.Existence.Compat
