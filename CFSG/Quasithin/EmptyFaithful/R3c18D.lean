module

public import CFSG.Quasithin.EmptyFaithful.R3c18A
public import CFSG.Quasithin.EmptyFaithful.R3c18Fam
public import CFSG.Quasithin.EmptyFaithful.R3c18G
public import CFSG.Quasithin.EmptyFaithful.R3c18H
public import CFSG.Quasithin.EmptyFaithful.R3c18P
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.Quasithin

namespace R3c18

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open scoped MatrixGroups

section Cube

theorem isCube_of_prod_isCube {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) {n : ℕ}
    (hn : Odd n) (hn3 : ¬ 3 ∣ n) (hσ : σ ^ n = 1) (a : Kˣ)
    (hN : ∃ c : Kˣ, ∏ i ∈ Finset.range n, Units.map ((σ ^ i : K ≃+* K).toRingHom : K →* K) a =
      c ^ 3) : ∃ b : Kˣ, b ^ 3 = a := by
  obtain ⟨j, hj⟩ := exists_frob_pow σ
  have ht3 : ¬ 3 ∣ 2 ^ j := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hpow : ∀ x : Kˣ, x ^ ((2 ^ j) ^ n) = x := fun x => Units.ext (by
    rw [Units.val_pow_eq_pow_val, ← pow_iter_frob σ hj n x, hσ]
    rfl)
  refine isCube_of_prod_pow hn hn3 ht3 hpow a ?_
  obtain ⟨c, hc⟩ := hN
  refine ⟨c, ?_⟩
  rw [← hc]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact (pow_iter_frob σ hj i a).symm)

end Cube

section Norm

variable {K : Type} [Field K] [Finite K]

theorem mem_semilinear_of_odd_orderOf {α : MulAut (projectiveSL 3 K)} (hα : Odd (orderOf α)) :
    α ∈ semilinearAutGroup 3 K := by
  have hR := (automorphism_generation (K := K) (n := 3) le_rfl).1
  have hmem : α ∈ standardAutGroup 3 K := hR ▸ Subgroup.mem_top α
  have hδδ := (standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
  have hsq : α ^ 2 ∈ semilinearAutGroup 3 K := by
    rcases mem_or_mul_dualAut_mem hmem with h | h
    · exact pow_mem h 2
    · have h2 : α ^ 2 = (α * dualAut 3 K) * (dualAut 3 K * (α * dualAut 3 K) * dualAut 3 K) := by
        rw [show (α * dualAut 3 K) * (dualAut 3 K * (α * dualAut 3 K) * dualAut 3 K) =
          α * (dualAut 3 K * dualAut 3 K) * α * (dualAut 3 K * dualAut 3 K) by group, hδδ]
        simp [pow_two]
      rw [h2]
      exact mul_mem h (dualAut_mul_mul_dualAut_mem h)
  obtain ⟨m, hm⟩ := hα
  have hpow : α ^ (orderOf α) = 1 := pow_orderOf_eq_one α
  have : α = (α ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    have : 2 * (m + 1) = orderOf α + 1 := by omega
    rw [this, pow_succ, hpow, one_mul]
  rw [this]
  exact pow_mem hsq _

@[expose] noncomputable def normGL (σ : K ≃+* K) (A : GL (Fin 3) K) : ℕ → GL (Fin 3) K
  | 0 => 1
  | n + 1 => normGL σ A n * Matrix.GeneralLinearGroup.map (σ ^ n : K ≃+* K).toRingHom A

omit [Finite K] in
theorem pow_conjAut_mul_fieldAut (σ : K ≃+* K) (A : GL (Fin 3) K) (n : ℕ) :
    (conjAut 3 K A * fieldAut 3 K σ) ^ n =
      conjAut 3 K (normGL σ A n) * fieldAut 3 K (σ ^ n) := by
  obtain ⟨hmul, hfmul, hconj, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  induction n with
  | zero => simp [normGL]
  | succ m ih =>
    have h1 : fieldAut 3 K (σ ^ m) * conjAut 3 K A =
        conjAut 3 K (Matrix.GeneralLinearGroup.map (σ ^ m : K ≃+* K).toRingHom A) *
          fieldAut 3 K (σ ^ m) := by
      have := hconj (σ ^ m) A
      calc fieldAut 3 K (σ ^ m) * conjAut 3 K A
          = (fieldAut 3 K (σ ^ m) * conjAut 3 K A * (fieldAut 3 K (σ ^ m))⁻¹) *
            fieldAut 3 K (σ ^ m) := by group
        _ = _ := by rw [this]; rfl
    rw [pow_succ, ih, normGL, pow_succ]
    calc conjAut 3 K (normGL σ A m) * fieldAut 3 K (σ ^ m) * (conjAut 3 K A * fieldAut 3 K σ)
        = conjAut 3 K (normGL σ A m) * (fieldAut 3 K (σ ^ m) * conjAut 3 K A) * fieldAut 3 K σ := by
          group
      _ = conjAut 3 K (normGL σ A m) * (conjAut 3 K (Matrix.GeneralLinearGroup.map
            (σ ^ m : K ≃+* K).toRingHom A) * fieldAut 3 K (σ ^ m)) * fieldAut 3 K σ := by rw [h1]
      _ = (conjAut 3 K (normGL σ A m) * conjAut 3 K (Matrix.GeneralLinearGroup.map
            (σ ^ m : K ≃+* K).toRingHom A)) * (fieldAut 3 K (σ ^ m) * fieldAut 3 K σ) := by group
      _ = _ := by rw [hmul, hfmul]

omit [Finite K] in
theorem det_map_gl (f : K →+* K) (A : GL (Fin 3) K) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f A) =
      Units.map (f : K →* K) (Matrix.GeneralLinearGroup.det A) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map]
  exact (RingHom.map_det f _).symm

omit [Finite K] in
theorem det_normGL (σ : K ≃+* K) (A : GL (Fin 3) K) (n : ℕ) :
    Matrix.GeneralLinearGroup.det (normGL σ A n) =
      ∏ i ∈ Finset.range n, Units.map ((σ ^ i : K ≃+* K).toRingHom : K →* K)
        (Matrix.GeneralLinearGroup.det A) := by
  induction n with
  | zero => simp [normGL]
  | succ m ih =>
    rw [normGL, map_mul, ih, det_map_gl, Finset.prod_range_succ]

end Norm

section Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isCube_det_of_pow_eq_one {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {A : GL (Fin 3) K} {σ : K ≃+* K}
    (h : (conjAut 3 K A * fieldAut 3 K σ) ^ (p ^ k) = 1) :
    ∃ b : Kˣ, b ^ 3 = Matrix.GeneralLinearGroup.det A := by
  rw [pow_conjAut_mul_fieldAut] at h
  obtain ⟨hσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ h
  refine isCube_of_prod_isCube σ ?_ ?_ hσ _ ⟨c, ?_⟩
  · exact (hp.odd_of_ne_two hp2).pow
  · intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
  · rw [← det_normGL, ← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

omit [Finite K] [CharP K 2] in
theorem conjAut_mem_inner_of_isCube {A : GL (Fin 3) K}
    (h : ∃ b : Kˣ, b ^ 3 = Matrix.GeneralLinearGroup.det A) :
    conjAut 3 K A ∈ inner (projectiveSL 3 K) := by
  obtain ⟨b, hb⟩ := h
  set A' : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) b⁻¹ * A with hA'
  have hdet : (A' : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) (show Matrix.GeneralLinearGroup.det A' = 1 by
      rw [hA', map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hb]
      group)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  set g : SL(3, K) := ⟨(A' : Matrix (Fin 3) (Fin 3) K), hdet⟩ with hg
  have hAA : A = Matrix.GeneralLinearGroup.scalar (Fin 3) b * Matrix.SpecialLinearGroup.toGL g := by
    have : Matrix.SpecialLinearGroup.toGL g = A' := Units.ext rfl
    rw [this, hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨proj 3 K g, ?_⟩
  rw [← conjAut_toGL, hAA, map_mul, conjAut_scalar, one_mul]

end Inner

@[expose] def L3PRankShape : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] {p e : ℕ}, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card Kˣ →
    (∀ j : ℕ, 1 ≤ j → p ∣ Nat.card K ^ j - 1 → e ≤ j) →
    2 ≤ CFSG.pRank p (projectiveSL 3 K) → 2 * e ≤ 3

section Sylow

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem dvd_pred_of_two_le_pRank_l3 (hshape : L3PRankShape) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 2 ≤ CFSG.pRank p (projectiveSL 3 K)) : p ∣ Nat.card K - 1 := by
  classical
  by_contra hnd
  have : Fact p.Prime := ⟨hp⟩
  have hpKu : ¬ p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  have hQ0 : (Nat.card K : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, hf⟩ := FiniteField.card K 2
    have : Nat.card K = 2 ^ (f : ℕ) := by
      rw [Nat.card_eq_fintype_card]
      exact hf.2
    rw [this] at hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
    exact hp2 this
  have hex : ∃ j : ℕ, 1 ≤ j ∧ p ∣ Nat.card K ^ j - 1 := by
    refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
    have h1 : ((Nat.card K : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hQ0
    have hq1 : 1 ≤ Nat.card K ^ (p - 1) := Nat.one_le_pow _ _ Nat.card_pos
    rw [← (Nat.modEq_iff_dvd' hq1), ← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact h1.symm
  have hmin : ∀ j : ℕ, 1 ≤ j → p ∣ Nat.card K ^ j - 1 → Nat.find hex ≤ j :=
    fun j hj hd => Nat.find_min' hex ⟨hj, hd⟩
  have he := Nat.find_spec hex
  have h2e := hshape K hp hp2 hpKu hmin h
  have he1 : Nat.find hex ≠ 1 := fun h1 => hnd (by simpa [h1] using he.2)
  omega

end Sylow

section Diag

variable {K : Type} [Field K]

@[expose] noncomputable def diagSL (x : Kˣ × Kˣ) : SL(3, K) :=
  ⟨Matrix.diagonal ![(x.1 : K), (x.2 : K), (((x.1 * x.2)⁻¹ : Kˣ) : K)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩

theorem coe_diagSL (x : Kˣ × Kˣ) :
    (diagSL x : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(x.1 : K), (x.2 : K), (((x.1 * x.2)⁻¹ : Kˣ) : K)] := rfl

@[expose] noncomputable def diagHom : (Kˣ × Kˣ) →* SL(3, K) where
  toFun := diagSL
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_diagSL, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL, coe_diagSL, coe_diagSL,
      Matrix.diagonal_mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [mul_mul_mul_comm]
    ring

theorem map_diagHom (σ : K ≃+* K) (x : Kˣ × Kˣ) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (diagHom x) =
      diagHom (Units.map (σ : K →* K) x.1, Units.map (σ : K →* K) x.2) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  change σ.toRingHom ((diagSL x : Matrix (Fin 3) (Fin 3) K) i j) =
    (diagSL (Units.map (σ : K →* K) x.1, Units.map (σ : K →* K) x.2) :
      Matrix (Fin 3) (Fin 3) K) i j
  rw [coe_diagSL, coe_diagSL]
  fin_cases i <;> fin_cases j <;> simp

theorem eq_of_proj_diagHom_eq_one [Finite K] (x : Kˣ × Kˣ) (h : proj 3 K (diagHom x) = 1) :
    x.1 = x.2 ∧ x.1 ^ 3 = 1 := by
  obtain ⟨c, hc3, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h)
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  simp [diagHom, diagSL, Matrix.scalar_apply] at h0 h1
  have e0 : x.1 = c := Units.ext h0
  have e1 : x.2 = c := Units.ext h1
  exact ⟨e0.trans e1.symm, by rw [e0, hc3]⟩

end Diag

section ElemAbelian

variable {K : Type} [Field K] [Finite K]

theorem exists_sq_l3 (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {ζ : Kˣ}
    (hζ : orderOf ζ = p) (hfix : Units.map (σ : K →* K) ζ = ζ) :
    ∃ E : Subgroup (projectiveSL 3 K), Nat.card E = p ^ 2 ∧ CFSG.Open.IsElemAbelian p E ∧
      ∀ y ∈ E, fieldAut 3 K σ y = y := by
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  refine exists_sq_of_pair hp (fieldAut 3 K σ) (u := proj 3 K (diagHom (ζ, 1)))
    (v := proj 3 K (diagHom (1, ζ))) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fieldAut_proj, map_diagHom]
    simp [hfix]
  · rw [fieldAut_proj, map_diagHom]
    simp [hfix]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    ext <;> simp [mul_comm]
  · rw [← map_pow, ← map_pow]
    simp [hζp, Prod.mk_one_one]
  · rw [← map_pow, ← map_pow]
    simp [hζp, Prod.mk_one_one]
  · intro i j h
    rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul] at h
    obtain ⟨h1, h2⟩ := eq_of_proj_diagHom_eq_one _ h
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, one_pow, mul_one,
      one_mul] at h1 h2
    have hi : p ∣ i := by
      have : ζ ^ (i * 3) = 1 := by rw [pow_mul, h2]
      have h3 := orderOf_dvd_of_pow_eq_one this
      rw [hζ] at h3
      rcases (Nat.Prime.dvd_mul hp).1 h3 with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h) hp3
    refine ⟨hi, ?_⟩
    have hζi : ζ ^ i = 1 := by
      obtain ⟨m, rfl⟩ := hi
      rw [pow_mul, hζp, one_pow]
    have : ζ ^ j = 1 := by rw [← h1]; exact hζi
    rw [← hζ]
    exact orderOf_dvd_of_pow_eq_one this

end ElemAbelian

section Frame

@[expose] noncomputable def pFrameL3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hshape : L3PRankShape)
    (K : Type) [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) :
    PFrame p (projectiveSL 3 K) (K ≃+* K) where
  fld := fieldAut 3 K
  fld_inter := fun c hc => by
    obtain ⟨y, hy⟩ := hc
    obtain ⟨g, rfl⟩ := proj_surjective 3 K y
    have h1 : conjAut 3 K (Matrix.SpecialLinearGroup.toGL g)⁻¹ * fieldAut 3 K c = 1 := by
      rw [map_inv, conjAut_toGL, hy, inv_mul_cancel]
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ h1).1
  conj_mem := fun α k hα => by
    obtain ⟨A, σ, h⟩ := mem_semilinearAutGroup_iff.1 (mem_semilinear_of_odd_orderOf (by
      rw [hα]
      exact (hp.odd_of_ne_two (by omega)).pow))
    have hpow : (conjAut 3 K A * fieldAut 3 K σ) ^ (p ^ k) = 1 := by
      rw [← h, ← hα]
      exact pow_orderOf_eq_one α
    obtain ⟨b, hb⟩ := isCube_det_of_pow_eq_one hp (by omega) (by omega) hpow
    exact ⟨1, conjAut 3 K A, conjAut_mem_inner_of_isCube ⟨b, hb⟩, σ, by rw [h]; simp⟩
  sq := fun h2 c hc => by
    have hdvd : p ∣ Nat.card K - 1 := dvd_pred_of_two_le_pRank_l3 hshape hp (by omega) h2
    obtain ⟨hpf, k, hk, hkcard⟩ := exists_fixed_subfield hf hK c hc
    have hKk : Nat.card K = Nat.card k ^ p := by
      rw [hK, hkcard, ← pow_mul, Nat.div_mul_cancel hpf]
    have hq0 : 0 < Nat.card k := by
      rw [hkcard]
      exact pow_pos (by norm_num) _
    have hd' : p ∣ Nat.card k - 1 := by
      have h1 := (dvd_pow_sub_one_iff_of_pow hp hq0 1).1 (by rw [pow_one, ← hKk]; exact hdvd)
      simpa using h1
    have : Fact p.Prime := ⟨hp⟩
    have hcardU : p ∣ Nat.card kˣ := by
      rw [Nat.card_units]
      exact hd'
    obtain ⟨ζ₀, hζ₀⟩ := exists_prime_orderOf_dvd_card' p hcardU
    have hinj : Function.Injective (Units.map (k.subtype : k →+* K).toMonoidHom) :=
      Units.map_injective k.subtype.injective
    refine exists_sq_l3 c hp (by omega) (ζ := Units.map (k.subtype : k →+* K).toMonoidHom ζ₀)
      (by rw [orderOf_injective _ hinj ζ₀, hζ₀]) ?_
    apply Units.ext
    change c (ζ₀ : K) = (ζ₀ : K)
    exact hk _ ζ₀.1.2

theorem qLiePRankFam_l3 (hshape : L3PRankShape) :
    QLiePRankFam (fun S _ => ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) := by
  intro p hp hp5 X _ _ S _ hC _ ⟨f, hf, hm⟩ hS2 hX
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hm
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have : Fact p.Prime := ⟨hp⟩
  let e' : ↥S ≃* projectiveSL 3 K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
  exact pframe_core hC ((pFrameL3 hp hp5 hshape K hK hf).ofMulEquiv hp.one_lt e') hS2 hX

end Frame

end R3c18

end CFSG.Quasithin
