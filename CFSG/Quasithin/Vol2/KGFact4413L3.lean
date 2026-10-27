module

public import CFSG.Quasithin.Vol2.KGFact4413One
public import CFSG.Quasithin.SteinbergBSLinearThreeRoot

public section

namespace CFSG.Quasithin.H13.KG4413

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def dg3 : Fˣ × Fˣ →* SL(3, F) where
  toFun t := ⟨diagonal ![(t.1 : F), (t.2 : F), ((t.1 * t.2)⁻¹ : Fˣ)], by
    rw [det_diagonal, Fin.prod_univ_three]
    show (t.1 : F) * t.2 * ((t.1 * t.2)⁻¹ : Fˣ) = 1
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩
  map_one' := by
    apply Subtype.ext
    show diagonal _ = (1 : Matrix (Fin 3) (Fin 3) F)
    rw [← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Subtype.ext
    show diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · simp
    · simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Prod.fst_mul, Prod.snd_mul,
        Units.val_mul, Units.val_inv_eq_inv_val]
      ring

theorem coe_dg3 (t : Fˣ × Fˣ) : ((dg3 t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    diagonal ![(t.1 : F), (t.2 : F), ((t.1 * t.2)⁻¹ : Fˣ)] :=
  rfl

@[expose] noncomputable def dL3 (F : Type) [Field F] : Subgroup (projectiveSL 3 F) :=
  ((dg3 : Fˣ × Fˣ →* SL(3, F)).range).map (proj 3 F)

theorem dg3_mem_upperTriangular (t : Fˣ × Fˣ) : dg3 t ∈ upperTriangular 3 F := by
  intro i j hij
  rw [coe_dg3, diagonal_apply_ne _ (ne_of_gt hij)]

theorem upperTriangular_le_three :
    upperTriangular 3 F ≤ (dg3 : Fˣ × Fˣ →* SL(3, F)).range ⊔ unitriangular 3 F := by
  intro b hb
  have hbU : (b : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.1 hb
  have hdet : (b : Matrix (Fin 3) (Fin 3) F) 0 0 * (b : Matrix (Fin 3) (Fin 3) F) 1 1 *
      (b : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
    have h1 := Matrix.det_of_isUpperTriangular hbU
    rw [b.2, Fin.prod_univ_three] at h1
    exact h1.symm
  have h0 : (b : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet; exact zero_ne_one hdet
  have h1 : (b : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 := fun h => by
    rw [h, mul_zero, zero_mul] at hdet; exact zero_ne_one hdet
  set t : Fˣ × Fˣ := (Units.mk0 _ h0, Units.mk0 _ h1) with ht
  have hu : (dg3 t)⁻¹ * b ∈ unitriangular 3 F := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · exact (upperTriangular 3 F).mul_mem ((upperTriangular 3 F).inv_mem
        (dg3_mem_upperTriangular t)) hb i j hij
    · rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular
        (mem_upperTriangular_iff_isUpperTriangular.1 ((upperTriangular 3 F).inv_mem
          (dg3_mem_upperTriangular t))) hbU, ← map_inv, coe_dg3]
      fin_cases i
      · simp [ht, h0]
      · simp [ht, h1]
      · simp [ht]
        linear_combination hdet
  have hb' : b = dg3 t * ((dg3 t)⁻¹ * b) := by rw [mul_inv_cancel_left]
  rw [hb']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨t, rfl⟩) (Subgroup.mem_sup_right hu)

variable [Finite F]

omit [Finite F] in
theorem pow_eq_one_of_mem_dL3 {d : projectiveSL 3 F} (hd : d ∈ dL3 F) :
    d ^ (Nat.card F - 1) = 1 := by
  obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hd
  have h1 : t ^ (Nat.card F - 1) = 1 := by
    ext
    · exact congrArg Units.val (units_pow_card_sub_one t.1)
    · exact congrArg Units.val (units_pow_card_sub_one t.2)
  rw [← map_pow, ← map_pow, h1, map_one, map_one]

variable [CharP F 2]

theorem odd_orderOf_of_mem_dL3 {d : projectiveSL 3 F} (hd : d ∈ dL3 F) : Odd (orderOf d) :=
  (RankThree.PartOne.K159.odd_card_sub_one (K := F)).of_dvd_nat
    (orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_dL3 hd))

theorem odd_card_dL3 : Odd (Nat.card (dL3 F)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := dL3 F) 2 (even_iff_two_dvd.mp hev)
  have h1 := odd_orderOf_of_mem_dL3 z.2
  rw [Subgroup.orderOf_coe, hz] at h1
  exact absurd h1 (by decide)

theorem isPGroup_projUnitriangular_three : IsPGroup 2 (projUnitriangular 3 F) := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  rw [← hP]
  exact P.isPGroup'

theorem dL3_inf : dL3 F ⊓ projUnitriangular 3 F = ⊥ :=
  E2.BorelLift.inf_eq_bot_of_odd odd_card_dL3 isPGroup_projUnitriangular_three

theorem dL3_le_normalizer :
    dL3 F ≤ Subgroup.normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnitriangular 2]
  exact Subgroup.map_mono fun x ⟨t, ht⟩ => ht ▸ dg3_mem_upperTriangular t

omit [Finite F] [CharP F 2] in
theorem projUpperTriangular_le :
    projUpperTriangular 3 F ≤ dL3 F ⊔ projUnitriangular 3 F := by
  have h := Subgroup.map_mono (f := proj 3 F) (upperTriangular_le_three (F := F))
  rw [Subgroup.map_sup] at h
  exact h

@[expose] noncomputable def w0L3 (F : Type) [Field F] [CharP F 2] : projectiveSL 3 F :=
  proj 3 F wJ

omit [Finite F] in
theorem wJ_mul_dg3_mul_wJ (x y : Fˣ) :
    (wJ : SL(3, F)) * dg3 (x, y) * wJ = dg3 ((x * y)⁻¹, y) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wJ_coe, coe_dg3,
    coe_dg3]
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [wJMat, mul_comm]

omit [Finite F] in
theorem w0L3_not_mem : w0L3 F ∉ projUpperTriangular 3 F := by
  intro h
  have h1 : (wJ : SL(3, F)) ∈ ((upperTriangular 3 F).map (proj 3 F)).comap (proj 3 F) := h
  rw [Subgroup.comap_map_eq, ker_proj, sup_eq_left.2 (scalars_le_upperTriangular 3 F)] at h1
  have := h1 2 0 (by decide)
  rw [wJ_coe] at this
  simp [wJMat] at this

omit [Finite F] in
theorem w0L3_conj_mem_dL3 {d : projectiveSL 3 F} (hd : d ∈ dL3 F) :
    w0L3 F * d * (w0L3 F)⁻¹ ∈ dL3 F := by
  obtain ⟨_, ⟨⟨x, y⟩, rfl⟩, rfl⟩ := hd
  refine ⟨dg3 ((x * y)⁻¹, y), ⟨_, rfl⟩, ?_⟩
  rw [w0L3, ← map_inv (proj 3 F) wJ, wJ_inv, ← map_mul, ← map_mul, wJ_mul_dg3_mul_wJ]

omit [Finite F] in
theorem gammaZero_dL3 {d : projectiveSL 3 F} (hd : d ∈ dL3 F) :
    gammaZero F d = w0L3 F * d⁻¹ * (w0L3 F)⁻¹ := by
  obtain ⟨_, ⟨⟨x, y⟩, rfl⟩, rfl⟩ := hd
  have hinv : ((dg3 (x, y))⁻¹ : SL(3, F)) = dg3 (x⁻¹, y⁻¹) := by
    rw [← map_inv]
    rfl
  have hR : w0L3 F * (proj 3 F (dg3 (x, y)))⁻¹ * (w0L3 F)⁻¹ =
      proj 3 F (dg3 ((x⁻¹ * y⁻¹)⁻¹, y⁻¹)) := by
    rw [w0L3, ← map_inv (proj 3 F) (dg3 (x, y)), ← map_inv (proj 3 F) wJ, wJ_inv, hinv,
      ← map_mul, ← map_mul, wJ_mul_dg3_mul_wJ]
  rw [hR, gammaZero, MulAut.mul_apply, dualAut_proj, LinearFlag.conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have h1 : ((SpecialLinearGroup.toGL (wJ : SL(3, F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = wJMat := rfl
  have h2 : (((SpecialLinearGroup.toGL (wJ : SL(3, F)))⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = wJMat := by
    rw [← map_inv, wJ_inv]
    rfl
  rw [h1, h2, hinv]
  have h3 : ((dg3 (x⁻¹, y⁻¹)).transpose : Matrix (Fin 3) (Fin 3) F) =
      (dg3 (x⁻¹, y⁻¹) : Matrix (Fin 3) (Fin 3) F) := by
    show (dg3 (x⁻¹, y⁻¹) : Matrix (Fin 3) (Fin 3) F)ᵀ = _
    rw [coe_dg3, diagonal_transpose]
  rw [h3, ← wJ_coe, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    wJ_mul_dg3_mul_wJ]

omit [CharP F 2] in
theorem exists_fieldAut_dL3 (σ : F ≃+* F) :
    ∃ m : ℤ, ∀ d ∈ dL3 F, LinearFlag.fieldAut 3 F σ d = d ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (Units.map σ.toRingHom.toMonoidHom : Fˣ →* Fˣ)
  refine ⟨m, ?_⟩
  rintro _ ⟨_, ⟨⟨x, y⟩, rfl⟩, rfl⟩
  rw [fieldAut_proj, ← map_zpow, ← map_zpow]
  congr 1
  have hx : σ (x : F) = ((x ^ m : Fˣ) : F) := by
    have := congrArg Units.val (hm x)
    simpa using this
  have hy : σ (y : F) = ((y ^ m : Fˣ) : F) := by
    have := congrArg Units.val (hm y)
    simpa using this
  have hxy : σ (((x * y)⁻¹ : Fˣ) : F) = (((x ^ m * y ^ m)⁻¹ : Fˣ) : F) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, Units.val_mul, map_mul, hx, hy,
      Units.val_inv_eq_inv_val, Units.val_mul]
  have hpow : (x, y) ^ m = (x ^ m, y ^ m) := rfl
  rw [hpow]
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, coe_dg3, coe_dg3]
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, hx, hy]

omit [Finite F] [CharP F 2] in
theorem conjAut_dL3_mem {B : GL (Fin 3) F}
    (hB : ∀ i j : Fin 3, j < i → (B : Matrix (Fin 3) (Fin 3) F) i j = 0) {d : projectiveSL 3 F}
    (hd : d ∈ dL3 F) : d⁻¹ * LinearFlag.conjAut 3 F B d ∈ projUnitriangular 3 F := by
  obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hd
  rw [conjAut_proj, ← map_inv, ← map_mul]
  refine Subgroup.mem_map_of_mem _ ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hB' : (B : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun _ _ h => hB _ _ h
    have hBi : ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hB'
    have hd' := mem_upperTriangular_iff_isUpperTriangular.1
      ((upperTriangular 3 F).inv_mem (dg3_mem_upperTriangular t))
    have hdt := mem_upperTriangular_iff_isUpperTriangular.1 (dg3_mem_upperTriangular t)
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation]
    exact (hd'.mul ((hB'.mul hdt).mul hBi)) hij
  · have hB' : (B : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun _ _ h => hB _ _ h
    have hBi : ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hB'
    have hd' := mem_upperTriangular_iff_isUpperTriangular.1
      ((upperTriangular 3 F).inv_mem (dg3_mem_upperTriangular t))
    have hdt := mem_upperTriangular_iff_isUpperTriangular.1 (dg3_mem_upperTriangular t)
    have h1 : (B : Matrix (Fin 3) (Fin 3) F) * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation,
      mul_apply_self_of_isUpperTriangular hd' ((hB'.mul hdt).mul hBi),
      mul_apply_self_of_isUpperTriangular (hB'.mul hdt) hBi,
      mul_apply_self_of_isUpperTriangular hB' hdt]
    have h2 := mul_apply_self_of_isUpperTriangular hB' hBi i
    rw [h1, one_apply_eq] at h2
    have h3 := coe_inv_apply_self_of_isUpperTriangular hdt i
    calc ((dg3 t)⁻¹ : SL(3, F)) i i * ((B : Matrix (Fin 3) (Fin 3) F) i i *
          (dg3 t : Matrix (Fin 3) (Fin 3) F) i i * ((B⁻¹ : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) i i) =
          ((dg3 t : Matrix (Fin 3) (Fin 3) F) i i * ((dg3 t)⁻¹ : SL(3, F)) i i) *
            ((B : Matrix (Fin 3) (Fin 3) F) i i *
              ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i) := by ring
      _ = 1 := by rw [h3, ← h2, one_mul]

omit [Finite F] [CharP F 2] in
theorem conj_proj_eq_conjAut (g : SL(3, F)) :
    MulAut.conj (proj 3 F g) = LinearFlag.conjAut 3 F (SpecialLinearGroup.toGL g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective 3 F x
  rw [MulAut.conj_apply, conjAut_proj, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rfl

theorem exists_mem_normalizer_psl3 {α : MulAut (projectiveSL 3 F)}
    (hαU : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F)
    (hαs : α ∉ LinearFlag.semilinearAutGroup 3 F) {A : Subgroup (projectiveSL 3 F)}
    (hAN : A ≤ projUpperTriangular 3 F) (hAodd : Odd (Nat.card A))
    (hαA : ∀ a ∈ A, α a ∈ A ⊔ projUnitriangular 3 F) :
    ∃ x : projectiveSL 3 F, x ∉ projUpperTriangular 3 F ∧
      x ∈ Subgroup.normalizer (A : Set (projectiveSL 3 F)) := by
  have hU2 := isPGroup_projUnitriangular_three (F := F)
  obtain ⟨u, hu, huA⟩ := exists_conj_le_of_le_sup hU2 odd_card_dL3 dL3_le_normalizer hAodd
    (hAN.trans projUpperTriangular_le)
  set A₀ := A.map (MulAut.conj u).toMonoidHom with hA₀
  set α₁ := MulAut.conj u * α * (MulAut.conj u)⁻¹ with hα₁
  have huN : (projUnitriangular 3 F).map (MulAut.conj u).toMonoidHom = projUnitriangular 3 F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hy) (Subgroup.inv_mem _ hu)
    · intro hx
      refine ⟨u⁻¹ * x * u, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hx) hu,
        ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have huN' : (projUnitriangular 3 F).map (MulAut.conj u)⁻¹.toMonoidHom =
      projUnitriangular 3 F := map_inv_eq_of_map_eq huN
  have hα₁U : (projUnitriangular 3 F).map α₁.toMonoidHom = projUnitriangular 3 F := by
    rw [hα₁, CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
      CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, huN', hαU, huN]
  have huS : MulAut.conj u ∈ LinearFlag.semilinearAutGroup 3 F := by
    obtain ⟨g, rfl⟩ := proj_surjective 3 F u
    rw [conj_proj_eq_conjAut]
    exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)
  have hα₁s : α₁ ∉ LinearFlag.semilinearAutGroup 3 F := by
    intro h
    apply hαs
    have : α = (MulAut.conj u)⁻¹ * α₁ * MulAut.conj u := by rw [hα₁]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ huS) h) huS
  obtain ⟨B, σ, hB, hα₁eq⟩ := exists_eq_semilinear_mul_gammaZero hα₁U hα₁s
  have hα₁A : ∀ a ∈ A₀, α₁ a ∈ A₀ ⊔ projUnitriangular 3 F := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hαA a ha
    simp only [hα₁, MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.conj_apply,
      MulAut.inv_apply, MulAut.conj_symm_apply]
    have h2 : u⁻¹ * (u * a * u⁻¹) * u = a := by group
    rw [h2]
    have h3 : (A ⊔ projUnitriangular 3 F).map (MulAut.conj u).toMonoidHom ≤
        A₀ ⊔ projUnitriangular 3 F := by
      rw [Subgroup.map_sup, huN]
    exact h3 ⟨α a, h1, rfl⟩
  have hfg : ∀ a ∈ A₀, LinearFlag.fieldAut 3 F σ (gammaZero F a) ∈ A₀ := by
    intro a ha
    have haD : a ∈ dL3 F := huA ha
    have he : LinearFlag.fieldAut 3 F σ (gammaZero F a) ∈ dL3 F := by
      obtain ⟨m, hm⟩ := exists_fieldAut_dL3 (F := F) σ
      rw [gammaZero_dL3 haD]
      have h1 : w0L3 F * a⁻¹ * (w0L3 F)⁻¹ ∈ dL3 F :=
        w0L3_conj_mem_dL3 (Subgroup.inv_mem _ haD)
      rw [hm _ h1]
      exact Subgroup.zpow_mem _ h1 m
    have h1 := hα₁A a ha
    rw [hα₁eq, MulAut.mul_apply, MulAut.mul_apply] at h1
    have h2 := conjAut_dL3_mem hB he
    set e := LinearFlag.fieldAut 3 F σ (gammaZero F a) with he_def
    have h3 : e ∈ A₀ ⊔ projUnitriangular 3 F := by
      have := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.mem_sup_right h2))
      simpa [mul_assoc] using this
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A₀
      (projUnitriangular 3 F) ?_] at h3
    · obtain ⟨b, hb, v, hv, hbv⟩ := h3
      have hvD : v ∈ dL3 F := by
        have : v = b⁻¹ * e := by rw [← hbv]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (huA hb)) he
      have hv1 : v = 1 := by
        have : v ∈ dL3 F ⊓ projUnitriangular 3 F := ⟨hvD, hv⟩
        rw [dL3_inf, Subgroup.mem_bot] at this
        exact this
      have hbe : b = e := by
        have := hbv
        simp only [hv1, mul_one] at this
        exact this
      rw [← hbe]
      exact hb
    · exact (huA.trans dL3_le_normalizer)
  obtain ⟨m, hm⟩ := exists_fieldAut_dL3 (F := F) σ
  have hfA : ∀ b ∈ A₀, ∃ a ∈ A₀, LinearFlag.fieldAut 3 F σ a = b := by
    have hle : A₀.map (LinearFlag.fieldAut 3 F σ).toMonoidHom ≤ A₀ := by
      rintro _ ⟨a, ha, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hm a (huA ha)]
      exact Subgroup.zpow_mem _ ha m
    have hcard : Nat.card (A₀.map (LinearFlag.fieldAut 3 F σ).toMonoidHom) = Nat.card A₀ :=
      Subgroup.card_map_of_injective (LinearFlag.fieldAut 3 F σ).injective
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    intro b hb
    rw [← heq] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, ha, rfl⟩
  have hw0 : LinearFlag.fieldAut 3 F σ (w0L3 F) = w0L3 F := by
    rw [w0L3, fieldAut_proj]
    congr 1
    ext i j
    rw [SpecialLinearGroup.map_apply_coe, wJ_coe]
    fin_cases i <;> fin_cases j <;> simp [wJMat, RingHom.mapMatrix_apply]
  have hw : w0L3 F ∈ Subgroup.normalizer (A₀ : Set (projectiveSL 3 F)) := by
    refine A4.mem_normalizer_of_conj_mem fun b hb => ?_
    obtain ⟨a, ha, hab⟩ := hfA b⁻¹ (Subgroup.inv_mem _ hb)
    have h1 := hfg a ha
    rw [gammaZero_dL3 (huA ha), map_mul, map_mul, map_inv, map_inv, hw0, hab, inv_inv] at h1
    exact h1
  have huB : u ∈ projUpperTriangular 3 F := by
    show u ∈ (upperTriangular 3 F).map (proj 3 F)
    exact Subgroup.map_mono (unitriangular_le_upperTriangular (n := 3) (K := F)) hu
  refine ⟨u⁻¹ * w0L3 F * u, fun hx => w0L3_not_mem (F := F) ?_, ?_⟩
  · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ huB hx) (Subgroup.inv_mem _ huB)
    simpa [mul_assoc] using this
  · refine A4.mem_normalizer_of_conj_mem fun a ha => ?_
    have h1 : u * a * u⁻¹ ∈ A₀ := ⟨a, ha, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp hw _).mp h1
    obtain ⟨a', ha', ha'e⟩ := h2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at ha'e
    have : u⁻¹ * w0L3 F * u * a * (u⁻¹ * w0L3 F * u)⁻¹ = a' := by
      have e : u⁻¹ * w0L3 F * u * a * (u⁻¹ * w0L3 F * u)⁻¹ =
          u⁻¹ * (w0L3 F * (u * a * u⁻¹) * (w0L3 F)⁻¹) * u := by group
      rw [e, ← ha'e]
      group
    rw [this]
    exact ha'

end CFSG.Quasithin.H13.KG4413
