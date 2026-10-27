module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBFrame
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBVanish

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinB

open TauCeti TauCeti.TypeBSpinCarrier CFSG.TauCetiBridge.BigCell SpinFrame SpinFrame.BI
open MvPolynomial

variable (n : ℕ)

theorem lt_of_ne_last {i : Fin (n + 1)} (hi : i ≠ Fin.last n) : i.val < n := by
  have := Fin.val_lt_last hi
  simpa using this

theorem exists_rootUnit (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    ∃ (x y : BI (n + 1)) (_ : bmB (n + 1) x y = 0) (_ : qdB (n + 1) x * qdB (n + 1) y = 0),
      rootIntMatrix n k = gamB n x * gamB n y := by
  rcases k with i | i
  · by_cases hi : i = Fin.last n
    · subst hi
      exact ⟨cr (Fin.last n), BI.zeta, rfl, rfl, rootIntMatrix_inl_last n⟩
    · have hlt := lt_of_ne_last n hi
      refine ⟨cr i, an ⟨i.val + 1, by omega⟩, ?_, rfl, rootIntMatrix_inl_lt n i hlt⟩
      exact Frame.bmB_cr_an_eq_zero (fun h => by simp [Fin.ext_iff] at h)
  · by_cases hi : i = Fin.last n
    · subst hi
      exact ⟨BI.zeta, an (Fin.last n), rfl, rfl, rootIntMatrix_inr_last n⟩
    · have hlt := lt_of_ne_last n hi
      refine ⟨cr ⟨i.val + 1, by omega⟩, an i, ?_, rfl, rootIntMatrix_inr_lt n i hlt⟩
      exact Frame.bmB_cr_an_eq_zero (fun h => by simp [Fin.ext_iff] at h)

theorem coe_rootSubgroupPoints_eq {A : Type} [CommRing A] {k : Fin (n + 1) ⊕ Fin (n + 1)}
    {x y : BI (n + 1)} (hxy : bmB (n + 1) x y = 0) (hq : qdB (n + 1) x * qdB (n + 1) y = 0)
    (hk : rootIntMatrix n k = gamB n x * gamB n y) (u : A) :
    (rootSubgroupPoints n k A (Multiplicative.ofAdd u) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) = (frame n).rootUnit A hxy hq u := by
  ext : 1
  rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd, Frame.coe_rootUnit, Frame.rootMat,
    Frame.gamA, Frame.gamA, frame_gam, ← map_mul, ← hk]
  rfl

theorem det_one_add_smul_of_mul_self_eq_zero {K : Type*} [Field K] {m : ℕ}
    {X : Matrix (Fin m) (Fin m) K} (hX : X * X = 0) (u : K) : (1 + u • X).det = 1 := by
  have hnil : IsNilpotent X := ⟨2, by rw [pow_two, hX]⟩
  have hunit := Matrix.isUnit_charpolyRev_of_isNilpotent hnil
  obtain ⟨r, hr, hrp⟩ := Polynomial.isUnit_iff.1 hunit
  have h0 := Matrix.eval_charpolyRev (M := X)
  rw [← hrp, Polynomial.eval_C] at h0
  have h1 : X.charpolyRev = 1 := by rw [← hrp, h0, map_one]
  have h2 := congrArg (Polynomial.eval (-u)) h1
  rw [Polynomial.eval_one, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom,
    RingHom.map_det] at h2
  rw [← h2]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Polynomial.coe_evalRingHom,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    ring
  · simp only [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.smul_apply, smul_eq_mul,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Polynomial.coe_evalRingHom,
      Polynomial.eval_sub, Polynomial.eval_zero, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    ring

theorem det_rootUnit {K : Type*} [Field K] {x y : BI (n + 1)} (hxy : bmB (n + 1) x y = 0)
    (hq : qdB (n + 1) x * qdB (n + 1) y = 0) (u : K) :
    (((frame n).rootUnit K hxy hq u : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) K).det = 1 := by
  rw [Frame.coe_rootUnit]
  exact det_one_add_smul_of_mul_self_eq_zero ((frame n).rootMat_sq K hxy hq) u

theorem ratRootGroup_le_normGroup : ratRootGroup n ≤ (frame n).normGroup ℚ := by
  rw [ratRootGroup, Subgroup.closure_le]
  rintro _ ⟨k, t, rfl⟩
  obtain ⟨x, y, hxy, hq, hk⟩ := exists_rootUnit n k
  rw [SetLike.mem_coe, coe_rootSubgroupPoints_eq n hxy hq hk]
  exact (frame n).rootUnit_mem_normGroup ℚ hxy hq t

theorem det_eq_one_of_mem_ratRootGroup {s : Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ}
    (hs : s ∈ ratRootGroup n) : (s : Matrix (Fin (dimension n)) (Fin (dimension n)) ℚ).det = 1 := by
  have hle : ratRootGroup n ≤ (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ →* ℚˣ).ker := by
    rw [ratRootGroup, Subgroup.closure_le]
    rintro _ ⟨k, t, rfl⟩
    obtain ⟨x, y, hxy, hq, hk⟩ := exists_rootUnit n k
    rw [SetLike.mem_coe, MonoidHom.mem_ker, coe_rootSubgroupPoints_eq n hxy hq hk]
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_rootUnit n hxy hq t
  have h := MonoidHom.mem_ker.1 (hle hs)
  rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply] at h
  exact h

abbrev PolyRing : Type :=
  MvPolynomial (Fin (dimension n) × Fin (dimension n)) ℤ

abbrev genMat : Matrix (Fin (dimension n)) (Fin (dimension n)) (PolyRing n) :=
  coordMatrix (dimension n)

variable {n}

theorem mapMatrix_gamA {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : BI (n + 1)) :
    f.mapMatrix ((frame n).gamA A a) = (frame n).gamA B a := by
  ext r c
  simp [Frame.gamA]

theorem mapMatrix_vec {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (c : BI (n + 1) → A) : f.mapMatrix ((frame n).vec A c) = (frame n).vec B (f ∘ c) := by
  rw [Frame.vec, Frame.vec, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul f), ← RingHom.mapMatrix_apply,
    mapMatrix_gamA, Function.comp_apply]

theorem map_coord {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : BI (n + 1))
    (M : Matrix (Fin (dimension n)) (Fin (dimension n)) A) :
    f ((frame n).coord A a M) = (frame n).coord B a (f.mapMatrix M) :=
  rfl

variable {A : Type*} [CommRing A]

theorem mapMatrix_conj_adjugate (M : Matrix (Fin (dimension n)) (Fin (dimension n)) A)
    (a : BI (n + 1)) :
    (evalMat M).mapMatrix (genMat n * (frame n).gamA (PolyRing n) a * (genMat n).adjugate) =
      M * (frame n).gamA A a * M.adjugate := by
  rw [map_mul, map_mul, RingHom.map_adjugate, mapMatrix_evalMat_coordMatrix, mapMatrix_gamA]

variable (n) in
@[expose] def detPoly : PolyRing n :=
  (genMat n).det - 1

theorem evalMat_detPoly (M : Matrix (Fin (dimension n)) (Fin (dimension n)) A) :
    evalMat M (detPoly n) = M.det - 1 := by
  rw [detPoly, map_sub, map_one, RingHom.map_det, mapMatrix_evalMat_coordMatrix]

variable (n) in
@[expose] def normPoly (a : BI (n + 1)) (r c : Fin (dimension n)) : PolyRing n :=
  (genMat n * (frame n).gamA (PolyRing n) a * (genMat n).adjugate -
    (frame n).vec (PolyRing n) fun b => (frame n).coord (PolyRing n) b
      (genMat n * (frame n).gamA (PolyRing n) a * (genMat n).adjugate)) r c

theorem evalMat_normPoly (M : Matrix (Fin (dimension n)) (Fin (dimension n)) A) (a : BI (n + 1))
    (r c : Fin (dimension n)) :
    evalMat M (normPoly n a r c) = (M * (frame n).gamA A a * M.adjugate -
      (frame n).vec A fun b => (frame n).coord A b (M * (frame n).gamA A a * M.adjugate)) r c := by
  have key : evalMat M (normPoly n a r c) = ((evalMat M).mapMatrix
      (genMat n * (frame n).gamA (PolyRing n) a * (genMat n).adjugate -
        (frame n).vec (PolyRing n) fun b => (frame n).coord (PolyRing n) b
          (genMat n * (frame n).gamA (PolyRing n) a * (genMat n).adjugate))) r c :=
    rfl
  have hv : (⇑(evalMat M) ∘ fun b => (frame n).coord (PolyRing n) b
      (genMat n * (frame n).gamA (PolyRing n) a * (genMat n).adjugate)) =
      fun b => (frame n).coord A b (M * (frame n).gamA A a * M.adjugate) := by
    funext b
    rw [Function.comp_apply, map_coord, mapMatrix_conj_adjugate]
  rw [key, map_sub, mapMatrix_vec, mapMatrix_conj_adjugate, hv]

theorem adjugate_eq_inv_of_det_eq_one (g : Matrix.GeneralLinearGroup (Fin (dimension n)) A)
    (h : (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A).det = 1) :
    (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A).adjugate =
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) := by
  rw [Matrix.coe_units_inv]
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [Matrix.mul_adjugate, h, one_smul]

variable (n)

theorem evalMat_normPoly_of_mem {g : Matrix.GeneralLinearGroup (Fin (dimension n)) A}
    (hg : g ∈ (frame n).normGroup A)
    (hdet : (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A).det = 1) (a : BI (n + 1))
    (r c : Fin (dimension n)) : evalMat (g : Matrix _ _ A) (normPoly n a r c) = 0 := by
  rw [evalMat_normPoly, adjugate_eq_inv_of_det_eq_one g hdet]
  have h : (frame n).InSpan A ((g : Matrix _ _ A) * (frame n).gamA A a *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin (dimension n)) A) : Matrix _ _ A)) := (hg a).1
  rw [Frame.InSpan] at h
  rw [← h, sub_self, Matrix.zero_apply]

theorem det_eq_one_of_mem_points {A : Type} [CommRing A]
    {g : Matrix.GeneralLinearGroup (Fin (dimension n)) A} (hg : g ∈ points n A) :
    (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A).det = 1 := by
  have h := evalMat_eq_zero_of_mem_points n (detPoly n) (fun s hs => by
    rw [evalMat_detPoly, det_eq_one_of_mem_ratRootGroup n hs, sub_self]) hg
  rw [evalMat_detPoly, sub_eq_zero] at h
  exact h

theorem inSpan_conj_of_mem_points {A : Type} [CommRing A]
    {g : Matrix.GeneralLinearGroup (Fin (dimension n)) A} (hg : g ∈ points n A) (a : BI (n + 1)) :
    (frame n).InSpan A ((g : Matrix _ _ A) * (frame n).gamA A a *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin (dimension n)) A) : Matrix _ _ A)) := by
  have hzero : ∀ r c, evalMat (g : Matrix _ _ A) (normPoly n a r c) = 0 := fun r c =>
    evalMat_eq_zero_of_mem_points n _ (fun s hs => evalMat_normPoly_of_mem n
      (ratRootGroup_le_normGroup n hs) (det_eq_one_of_mem_ratRootGroup n hs) a r c) hg
  have hm : (g : Matrix _ _ A) * (frame n).gamA A a * (g : Matrix _ _ A).adjugate -
      (frame n).vec A (fun b => (frame n).coord A b
        ((g : Matrix _ _ A) * (frame n).gamA A a * (g : Matrix _ _ A).adjugate)) = 0 := by
    ext r c
    rw [← evalMat_normPoly]
    exact hzero r c
  rw [adjugate_eq_inv_of_det_eq_one g (det_eq_one_of_mem_points n hg), sub_eq_zero] at hm
  exact hm

theorem points_le_normGroup (A : Type) [CommRing A] : points n A ≤ (frame n).normGroup A :=
  fun g hg a => ⟨inSpan_conj_of_mem_points n hg a, by
    have h := inSpan_conj_of_mem_points n (inv_mem hg) a
    rwa [inv_inv] at h⟩

section CharTwo

variable {K : Type} [Field K]

instance nonempty_index : Nonempty (Fin (dimension n)) :=
  ⟨posS n ∅⟩

theorem dimension_eq : dimension n = 2 ^ (n + 1) := by
  simp [dimension, Fintype.card_finset]

theorem eq_one_of_pow_two_pow_eq_one (h2 : (2 : K) = 0) {c : K} :
    ∀ k : ℕ, c ^ 2 ^ k = 1 → c = 1
  | 0, h => by simpa using h
  | k + 1, h => by
    have hsq : (c ^ 2 ^ k) * (c ^ 2 ^ k) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact h
    have hx : (c ^ 2 ^ k - 1) * (c ^ 2 ^ k - 1) = 0 := by
      have e : (c ^ 2 ^ k - 1) * (c ^ 2 ^ k - 1) =
          (c ^ 2 ^ k) * (c ^ 2 ^ k) - 2 * c ^ 2 ^ k + 1 := by ring
      rw [e, hsq, h2, zero_mul, sub_zero, one_add_one_eq_two, h2]
    exact eq_one_of_pow_two_pow_eq_one h2 k (sub_eq_zero.1 (mul_self_eq_zero.1 hx))

variable (K) in
@[expose] def symplecticPoints (h2 : (2 : K) = 0) :
    points n K →* TauCeti.GLSymplectic (Fin (n + 1)) K :=
  ((frame n).symplecticHom h2).comp (Subgroup.inclusion (points_le_normGroup n K))

theorem symplecticPoints_injective (h2 : (2 : K) = 0) :
    Function.Injective (symplecticPoints n K h2) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hρ := (frame n).rho_eq_one_of_symplecticHom_eq_one h2 hg
  have hcomm : ∀ a, ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) K) * (frame n).gamA K a =
      (frame n).gamA K a * ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) K) := fun a => by
    have h := (frame n).conj_eq_of_rho_eq_one (points_le_normGroup n K g.2) hρ a
    have hgg : (↑(g : Matrix.GeneralLinearGroup (Fin (dimension n)) K)⁻¹ :
        Matrix (Fin (dimension n)) (Fin (dimension n)) K) *
        ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) K) * (frame n).gamA K a
        = ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
            Matrix (Fin (dimension n)) (Fin (dimension n)) K) * (frame n).gamA K a *
          ((↑(g : Matrix.GeneralLinearGroup (Fin (dimension n)) K)⁻¹ :
            Matrix (Fin (dimension n)) (Fin (dimension n)) K) *
          ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
            Matrix (Fin (dimension n)) (Fin (dimension n)) K)) := by rw [hgg, mul_one]
      _ = _ := by rw [← mul_assoc, h]
  have hs := eq_smul_one_of_commute n _ hcomm
  have hdet := det_eq_one_of_mem_points n g.2
  rw [hs, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc := eq_one_of_pow_two_pow_eq_one h2 (n + 1)
    ((congrArg (fun k => (((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) K) (posS n ∅) (posS n ∅)) ^ k)
        (dimension_eq n)).symm.trans hdet)
  rw [hc, one_smul] at hs
  apply Subtype.ext
  apply Units.ext
  rw [hs]
  rfl

theorem coe_symplecticPoints (h2 : (2 : K) = 0) (g : points n K) :
    (((symplecticPoints n K h2 g : TauCeti.GLSymplectic (Fin (n + 1)) K) :
      GL (Fin (n + 1) ⊕ Fin (n + 1)) K) : Matrix (Fin (n + 1) ⊕ Fin (n + 1))
        (Fin (n + 1) ⊕ Fin (n + 1)) K) = (frame n).sympMat (g : GL (Fin (dimension n)) K) :=
  rfl

theorem coe_symplecticPoints_rootSubgroupPoints (h2 : (2 : K) = 0)
    {k : Fin (n + 1) ⊕ Fin (n + 1)} {x y : BI (n + 1)} (hxy : bmB (n + 1) x y = 0)
    (hq : qdB (n + 1) x * qdB (n + 1) y = 0) (hk : rootIntMatrix n k = gamB n x * gamB n y)
    (u : K) :
    (((symplecticPoints n K h2 (rootSubgroupPoints n k K (Multiplicative.ofAdd u)) :
      TauCeti.GLSymplectic (Fin (n + 1)) K) : GL (Fin (n + 1) ⊕ Fin (n + 1)) K) :
        Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) K) =
      (frame n).sympMat ((frame n).rootUnit K hxy hq u) := by
  rw [coe_symplecticPoints, coe_rootSubgroupPoints_eq n hxy hq hk]

theorem coe_mulEquivGLSymplectic_differenceShortRootUnit {i j : Fin (n + 1)} (hij : i ≠ j)
    (c : K) :
    ((((TauCeti.GLSymplecticFin.mulEquivGLSymplectic (n + 1) K
      (TauCeti.GLSymplecticFin.differenceShortRootUnit hij c)) :
        TauCeti.GLSymplectic (Fin (n + 1)) K) : GL (Fin (n + 1) ⊕ Fin (n + 1)) K) :
          Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) K) =
      1 + Matrix.single (Sum.inl i) (Sum.inl j) c - Matrix.single (Sum.inr j) (Sum.inr i) c := by
  rw [TauCeti.GLSymplecticFin.coe_mulEquivGLSymplectic, Equiv.coe_reindexGL,
    TauCeti.GLSymplecticFin.coe_differenceShortRootUnit_eq_one_add_single_sub_single]
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, EmbeddingLike.apply_eq_iff_eq, Equiv.symm_symm]

theorem coe_mulEquivGLSymplectic_positiveLong (i : Fin (n + 1)) (c : K) :
    ((((TauCeti.GLSymplecticFin.mulEquivGLSymplectic (n + 1) K
      (TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit i c)) :
        TauCeti.GLSymplectic (Fin (n + 1)) K) : GL (Fin (n + 1) ⊕ Fin (n + 1)) K) :
          Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) K) =
      1 + Matrix.single (Sum.inl i) (Sum.inr i) c := by
  rw [TauCeti.GLSymplecticFin.coe_mulEquivGLSymplectic,
    TauCeti.GLSymplecticFin.coe_positiveLongRootTransvectionUnit,
    TauCeti.GLSymplecticFin.reindexGL_transvectionUnit (Sum.inl i) (Sum.inr i) Sum.inl_ne_inr,
    TauCeti.coe_transvectionUnit]
  rfl

theorem coe_mulEquivGLSymplectic_negativeLong (i : Fin (n + 1)) (c : K) :
    ((((TauCeti.GLSymplecticFin.mulEquivGLSymplectic (n + 1) K
      (TauCeti.GLSymplecticFin.negativeLongRootTransvectionUnit i c)) :
        TauCeti.GLSymplectic (Fin (n + 1)) K) : GL (Fin (n + 1) ⊕ Fin (n + 1)) K) :
          Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) K) =
      1 + Matrix.single (Sum.inr i) (Sum.inl i) c := by
  rw [TauCeti.GLSymplecticFin.coe_mulEquivGLSymplectic,
    TauCeti.GLSymplecticFin.coe_negativeLongRootTransvectionUnit,
    TauCeti.GLSymplecticFin.reindexGL_transvectionUnit (Sum.inr i) (Sum.inl i) Sum.inr_ne_inl,
    TauCeti.coe_transvectionUnit]
  rfl

theorem gl_ext_iff {x y : TauCeti.GLSymplectic (Fin (n + 1)) K} :
    x = y ↔ ((x : GL (Fin (n + 1) ⊕ Fin (n + 1)) K) : Matrix (Fin (n + 1) ⊕ Fin (n + 1))
      (Fin (n + 1) ⊕ Fin (n + 1)) K) = ((y : GL (Fin (n + 1) ⊕ Fin (n + 1)) K) :
        Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) K) :=
  ⟨fun h => h ▸ rfl, fun h => Subtype.ext (Units.ext h)⟩

theorem symplecticPoints_surjective (h2 : (2 : K) = 0) (hsq : ∀ c : K, ∃ u : K, u * u = c) :
    Function.Surjective (symplecticPoints n K h2) := by
  set e := TauCeti.GLSymplecticFin.mulEquivGLSymplectic (n + 1) K
  set H := (symplecticPoints n K h2).range.comap e.toMonoidHom
  have hneg : ∀ c : K, -c = c := fun c => by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
  have hadj : ∀ {i j : Fin (n + 1)} (hij : i ≠ j) (c : K),
      i.val + 1 = j.val ∨ j.val + 1 = i.val →
      TauCeti.GLSymplecticFin.differenceShortRootUnit hij c ∈ H := by
    intro i j hij c hadj
    rcases hadj with h | h
    · have hi : i.val < n := by omega
      have hj : j = ⟨i.val + 1, Nat.succ_lt_succ hi⟩ := Fin.ext h.symm
      subst hj
      refine ⟨rootSubgroupPoints n (.inl i) K (Multiplicative.ofAdd c), ?_⟩
      rw [MulEquiv.coe_toMonoidHom, gl_ext_iff, coe_symplecticPoints_rootSubgroupPoints n h2
        (Frame.bmB_cr_an_eq_zero hij) rfl (rootIntMatrix_inl_lt n i hi),
        (frame n).sympMat_rootUnit_cr_an hij c, coe_mulEquivGLSymplectic_differenceShortRootUnit]
    · have hj : j.val < n := by omega
      have hi : i = ⟨j.val + 1, Nat.succ_lt_succ hj⟩ := Fin.ext h.symm
      subst hi
      refine ⟨rootSubgroupPoints n (.inr j) K (Multiplicative.ofAdd c), ?_⟩
      rw [MulEquiv.coe_toMonoidHom, gl_ext_iff, coe_symplecticPoints_rootSubgroupPoints n h2
        (Frame.bmB_cr_an_eq_zero hij) rfl (rootIntMatrix_inr_lt n j hj),
        (frame n).sympMat_rootUnit_cr_an hij c, coe_mulEquivGLSymplectic_differenceShortRootUnit]
  have hpos : ∀ c : K,
      TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit (Fin.last n) c ∈ H := by
    intro c
    obtain ⟨u, hu⟩ := hsq c
    refine ⟨rootSubgroupPoints n (.inl (Fin.last n)) K (Multiplicative.ofAdd u), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, gl_ext_iff, coe_symplecticPoints_rootSubgroupPoints n h2
      (bmB_cr_zeta _) rfl (rootIntMatrix_inl_last n), Frame.sympMat_rootUnit_cr_zeta,
      coe_mulEquivGLSymplectic_positiveLong, hu, hneg]
  have hneg' : ∀ c : K,
      TauCeti.GLSymplecticFin.negativeLongRootTransvectionUnit (Fin.last n) c ∈ H := by
    intro c
    obtain ⟨u, hu⟩ := hsq c
    refine ⟨rootSubgroupPoints n (.inr (Fin.last n)) K (Multiplicative.ofAdd u), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, gl_ext_iff, coe_symplecticPoints_rootSubgroupPoints n h2
      (bmB_zeta_an _) rfl (rootIntMatrix_inr_last n), Frame.sympMat_rootUnit_zeta_an,
      coe_mulEquivGLSymplectic_negativeLong, hu, hneg]
  have htop : H = ⊤ := TauCeti.GLSymplecticFin.eq_top_of_root_subgroups H fun root c =>
    TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_apply_mem_of_adjacent_of_long H (Fin.last n)
      hadj hpos hneg' root c
  intro y
  have hy : e.symm y ∈ H := htop ▸ Subgroup.mem_top _
  obtain ⟨g, hg⟩ := hy
  refine ⟨g, ?_⟩
  rw [hg, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

@[expose] def pointsEquivSp (h2 : (2 : K) = 0) (hsq : ∀ c : K, ∃ u : K, u * u = c) :
    points n K ≃* TauCeti.GLSymplecticFin (n + 1) K :=
  (MulEquiv.ofBijective (symplecticPoints n K h2)
    ⟨symplecticPoints_injective n h2, symplecticPoints_surjective n h2 hsq⟩).trans
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic (n + 1) K).symm

end CharTwo

end CFSG.RankThree.PartTwo.Census.Carrier.SpinB
