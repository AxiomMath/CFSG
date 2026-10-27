module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDFrame
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDVanish
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDGen
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBPoints

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open TauCeti TauCeti.TypeDSpinCarrier CFSG.TauCetiBridge.BigCell SpinFrame
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open MvPolynomial
open scoped Matrix

variable (n : ℕ) (hn : 4 ≤ n)

theorem bmD_inl_inr_eq_zero {i j : Fin n} (hij : i ≠ j) : bmD n (.inl i) (.inr j) = 0 := by
  rw [bmD_inl_inr, ite_eq_right hij]

theorem fin_succ_ne (i : Fin n) (hi : i.val + 1 < n) : i ≠ ⟨i.val + 1, hi⟩ := fun h => by
  have := congrArg Fin.val h
  simp at this

theorem bmD_comm (a b : DI n) : bmD n a b = bmD n b a := by
  rcases a with i | i <;> rcases b with j | j
  · rfl
  · by_cases h : i = j
    · subst h
      rfl
    · rw [bmD_inl_inr, bmD_inr_inl, ite_eq_right h, ite_eq_right (Ne.symm h)]
  · by_cases h : i = j
    · subst h
      rfl
    · rw [bmD_inl_inr, bmD_inr_inl, ite_eq_right h, ite_eq_right (Ne.symm h)]
  · rfl

theorem exists_rootUnit (k : Fin n ⊕ Fin n) :
    ∃ (x y : DI n) (_ : bmD n x y = 0) (_ : qdD n x * qdD n y = 0),
      rootIntMatrix n hn k = gamD n x * gamD n y := by
  rcases k with i | i
  · by_cases hi : i.val + 1 < n
    · exact ⟨.inl i, .inr ⟨i.val + 1, hi⟩, bmD_inl_inr_eq_zero n (fin_succ_ne n i hi), rfl,
        rootIntMatrix_inl_lt n hn i hi⟩
    · have e : i = ⟨n - 1, by omega⟩ := Fin.ext (by have := i.isLt; simp only; omega)
      rw [e]
      exact ⟨.inl ⟨n - 2, by omega⟩, .inl ⟨n - 1, by omega⟩, rfl, rfl,
        rootIntMatrix_inl_fork n hn⟩
  · by_cases hi : i.val + 1 < n
    · exact ⟨.inl ⟨i.val + 1, hi⟩, .inr i, bmD_inl_inr_eq_zero n (fin_succ_ne n i hi).symm, rfl,
        rootIntMatrix_inr_lt n hn i hi⟩
    · have e : i = ⟨n - 1, by omega⟩ := Fin.ext (by have := i.isLt; simp only; omega)
      rw [e]
      exact ⟨.inr ⟨n - 1, by omega⟩, .inr ⟨n - 2, by omega⟩, rfl, rfl,
        rootIntMatrix_inr_fork n hn⟩

theorem coe_rootSubgroupPoints_eq {A : Type} [CommRing A] {k : Fin n ⊕ Fin n} {x y : DI n}
    (hxy : bmD n x y = 0) (hq : qdD n x * qdD n y = 0)
    (hk : rootIntMatrix n hn k = gamD n x * gamD n y) (u : A) :
    (rootSubgroupPoints n hn k A (Multiplicative.ofAdd u) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) = (frame n).rootUnit A hxy hq u := by
  ext : 1
  rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd, Frame.coe_rootUnit, Frame.rootMat,
    Frame.gamA, Frame.gamA, frame_gam, ← map_mul, ← hk]
  rfl

theorem det_rootUnit {K : Type*} [Field K] {x y : DI n} (hxy : bmD n x y = 0)
    (hq : qdD n x * qdD n y = 0) (u : K) :
    (((frame n).rootUnit K hxy hq u : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) K).det = 1 := by
  rw [Frame.coe_rootUnit]
  exact SpinB.det_one_add_smul_of_mul_self_eq_zero ((frame n).rootMat_sq K hxy hq) u

theorem ratRootGroup_le_normGroup : ratRootGroup n hn ≤ (frame n).normGroup ℚ := by
  rw [ratRootGroup, Subgroup.closure_le]
  rintro _ ⟨k, t, rfl⟩
  obtain ⟨x, y, hxy, hq, hk⟩ := exists_rootUnit n hn k
  rw [SetLike.mem_coe, coe_rootSubgroupPoints_eq n hn hxy hq hk]
  exact (frame n).rootUnit_mem_normGroup ℚ hxy hq t

theorem det_eq_one_of_mem_ratRootGroup {s : Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ}
    (hs : s ∈ ratRootGroup n hn) :
    (s : Matrix (Fin (dimension n)) (Fin (dimension n)) ℚ).det = 1 := by
  have hle : ratRootGroup n hn ≤ (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ →* ℚˣ).ker := by
    rw [ratRootGroup, Subgroup.closure_le]
    rintro _ ⟨k, t, rfl⟩
    obtain ⟨x, y, hxy, hq, hk⟩ := exists_rootUnit n hn k
    rw [SetLike.mem_coe, MonoidHom.mem_ker, coe_rootSubgroupPoints_eq n hn hxy hq hk]
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

theorem mapMatrix_gamA {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : DI n) :
    f.mapMatrix ((frame n).gamA A a) = (frame n).gamA B a := by
  ext r c
  simp [Frame.gamA]

theorem mapMatrix_vec {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (c : DI n → A) : f.mapMatrix ((frame n).vec A c) = (frame n).vec B (f ∘ c) := by
  rw [Frame.vec, Frame.vec, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul f), ← RingHom.mapMatrix_apply,
    mapMatrix_gamA, Function.comp_apply]

theorem map_coord {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : DI n)
    (M : Matrix (Fin (dimension n)) (Fin (dimension n)) A) :
    f ((frame n).coord A a M) = (frame n).coord B a (f.mapMatrix M) :=
  rfl

variable {A : Type*} [CommRing A]

theorem mapMatrix_conj_adjugate (M : Matrix (Fin (dimension n)) (Fin (dimension n)) A)
    (a : DI n) :
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
@[expose] def normPoly (a : DI n) (r c : Fin (dimension n)) : PolyRing n :=
  (genMat n * (frame n).gamA (PolyRing n) a * (genMat n).adjugate -
    (frame n).vec (PolyRing n) fun b => (frame n).coord (PolyRing n) b
      (genMat n * (frame n).gamA (PolyRing n) a * (genMat n).adjugate)) r c

theorem evalMat_normPoly (M : Matrix (Fin (dimension n)) (Fin (dimension n)) A) (a : DI n)
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

omit hn in
theorem evalMat_normPoly_of_mem {g : Matrix.GeneralLinearGroup (Fin (dimension n)) A}
    (hg : g ∈ (frame n).normGroup A)
    (hdet : (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A).det = 1) (a : DI n)
    (r c : Fin (dimension n)) : evalMat (g : Matrix _ _ A) (normPoly n a r c) = 0 := by
  rw [evalMat_normPoly, adjugate_eq_inv_of_det_eq_one g hdet]
  have h : (frame n).InSpan A ((g : Matrix _ _ A) * (frame n).gamA A a *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin (dimension n)) A) : Matrix _ _ A)) := (hg a).1
  rw [Frame.InSpan] at h
  rw [← h, sub_self, Matrix.zero_apply]

theorem det_eq_one_of_mem_points {A : Type} [CommRing A]
    {g : Matrix.GeneralLinearGroup (Fin (dimension n)) A} (hg : g ∈ points n hn A) :
    (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A).det = 1 := by
  have h := evalMat_eq_zero_of_mem_points n hn (detPoly n) (fun s hs => by
    rw [evalMat_detPoly, det_eq_one_of_mem_ratRootGroup n hn hs, sub_self]) hg
  rw [evalMat_detPoly, sub_eq_zero] at h
  exact h

theorem inSpan_conj_of_mem_points {A : Type} [CommRing A]
    {g : Matrix.GeneralLinearGroup (Fin (dimension n)) A} (hg : g ∈ points n hn A) (a : DI n) :
    (frame n).InSpan A ((g : Matrix _ _ A) * (frame n).gamA A a *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin (dimension n)) A) : Matrix _ _ A)) := by
  have hzero : ∀ r c, evalMat (g : Matrix _ _ A) (normPoly n a r c) = 0 := fun r c =>
    evalMat_eq_zero_of_mem_points n hn _ (fun s hs => evalMat_normPoly_of_mem n
      (ratRootGroup_le_normGroup n hn hs) (det_eq_one_of_mem_ratRootGroup n hn hs) a r c) hg
  have hm : (g : Matrix _ _ A) * (frame n).gamA A a * (g : Matrix _ _ A).adjugate -
      (frame n).vec A (fun b => (frame n).coord A b
        ((g : Matrix _ _ A) * (frame n).gamA A a * (g : Matrix _ _ A).adjugate)) = 0 := by
    ext r c
    rw [← evalMat_normPoly]
    exact hzero r c
  rw [adjugate_eq_inv_of_det_eq_one g (det_eq_one_of_mem_points n hn hg), sub_eq_zero] at hm
  exact hm

theorem points_le_normGroup (A : Type) [CommRing A] : points n hn A ≤ (frame n).normGroup A :=
  fun g hg a => ⟨inSpan_conj_of_mem_points n hn hg a, by
    have h := inSpan_conj_of_mem_points n hn (inv_mem hg) a
    rwa [inv_inv] at h⟩

section Orth

variable {K : Type} [Field K]

instance nonempty_index : Nonempty (Fin (dimension n)) :=
  ⟨posS n ∅⟩

theorem dimension_eq : dimension n = 2 ^ n := by
  simp [dimension, Fintype.card_finset]

variable (K) in
@[expose] def orthPoints : points n hn K →* GL (DI n) K :=
  (frame n).orthHom.comp (Subgroup.inclusion (points_le_normGroup n hn K))

theorem coe_orthPoints (g : points n hn K) :
    ((orthPoints n hn K g : GL (DI n) K) : Matrix (DI n) (DI n) K) =
      (frame n).rho K (g : GL (Fin (dimension n)) K) :=
  rfl

theorem orthPoints_injective (h2 : (2 : K) = 0) : Function.Injective (orthPoints n hn K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hρ : (frame n).rho K (g : GL (Fin (dimension n)) K) = 1 := by
    rw [← coe_orthPoints, hg, Units.val_one]
  have hcomm : ∀ a, ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) K) * (frame n).gamA K a =
      (frame n).gamA K a * ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) K) := fun a => by
    have h := (frame n).conj_eq_of_rho_eq_one (points_le_normGroup n hn K g.2) hρ a
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
  have hdet := det_eq_one_of_mem_points n hn g.2
  rw [hs, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc := SpinB.eq_one_of_pow_two_pow_eq_one h2 n
    ((congrArg (fun k => (((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) K) (posS n ∅) (posS n ∅)) ^ k)
        (dimension_eq n)).symm.trans hdet)
  rw [hc, one_smul] at hs
  apply Subtype.ext
  apply Units.ext
  rw [hs]
  rfl

theorem orthPoints_mem_isometries (g : points n hn K) :
    orthPoints n hn K g ∈ Subgroup.closure {A : GL (DI n) K |
      ∀ v, StatedQuadPlus n K ((A : Matrix (DI n) (DI n) K) *ᵥ v) = StatedQuadPlus n K v} :=
  Subgroup.subset_closure fun v => by
    unfold StatedQuadPlus
    exact (frame n).plusQuad_rho (points_le_normGroup n hn K g.2) v

theorem range_orthPoints_le_isometries :
    (orthPoints n hn K).range ≤ Subgroup.closure {A : GL (DI n) K |
      ∀ v, StatedQuadPlus n K ((A : Matrix (DI n) (DI n) K) *ᵥ v) = StatedQuadPlus n K v} := by
  rintro _ ⟨g, rfl⟩
  exact orthPoints_mem_isometries n hn g

omit hn in
theorem polar_quadPlus_single (v : DI n → K) (y : DI n) :
    QuadraticMap.polar (quadPlus n K) v (Pi.single y 1) = ∑ z, ((bmD n y z : ℤ) : K) * v z := by
  rcases y with j | j
  · rw [polar_quadPlus_single_inl]
    simp [Fintype.sum_sum_type]
  · rw [polar_quadPlus_single_inr]
    simp [Fintype.sum_sum_type]

omit hn in
theorem quadPlus_single (y : DI n) (u : K) : quadPlus n K (u • Pi.single y 1) = 0 := by
  rw [QuadraticMap.map_smul]
  rcases y with j | j <;> simp [quadPlus_apply, Pi.single_apply]

omit hn in
theorem toLinEquiv_eq_eichler {x y : DI n} (hxy : bmD n x y = 0) (hq : qdD n x * qdD n y = 0)
    (u : K) {A : GL (DI n) K}
    (hA : (A : Matrix (DI n) (DI n) K) = (frame n).rho K ((frame n).rootUnit K hxy hq u)) :
    toLinEquiv (DI n) K A = eichler (quadPlus n K) (Pi.single y 1) (u • Pi.single x 1) := by
  have hy : quadPlus n K (Pi.single y 1) = 0 := by
    simpa using quadPlus_single n y (1 : K)
  have hyx : bmD n y x = 0 := (bmD_comm n y x).trans hxy
  have hpol : QuadraticMap.polar (quadPlus n K) (Pi.single y 1) (u • Pi.single x 1) = 0 := by
    rw [QuadraticMap.polar_comm, QuadraticMap.polar_smul_left, polar_quadPlus_single]
    simp [Pi.single_apply, hyx]
  refine LinearEquiv.ext fun v => ?_
  rw [toLinEquiv_apply, hA, eichler_apply hy hpol, quadPlus_single, zero_mul, add_zero,
    QuadraticMap.polar_smul_right, polar_quadPlus_single, polar_quadPlus_single]
  funext b
  have e1 : ∀ z, (frame n).rho K ((frame n).rootUnit K hxy hq u) b z =
      (if b = z then 1 else 0) + u * (((bmD n y z : ℤ) : K) * (if b = x then 1 else 0) -
        ((bmD n x z : ℤ) : K) * (if b = y then 1 else 0)) := by
    intro z
    rw [Frame.rho_rootUnit]
    simp only [qdD_apply, Int.cast_zero, mul_zero, zero_mul, add_zero, sub_zero]
  simp only [Matrix.mulVec, dotProduct, e1, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply]
  have e2 : ∑ z, ((if b = z then (1 : K) else 0) +
      u * (((bmD n y z : ℤ) : K) * (if b = x then 1 else 0) -
        ((bmD n x z : ℤ) : K) * (if b = y then 1 else 0))) * v z =
      v b + u * (if b = x then 1 else 0) * ∑ z, ((bmD n y z : ℤ) : K) * v z -
        u * (if b = y then 1 else 0) * ∑ z, ((bmD n x z : ℤ) : K) * v z := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [add_sub_assoc]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [e2]
  ring

variable (K) in
abbrev imageLin : Subgroup ((DI n → K) ≃ₗ[K] (DI n → K)) :=
  (orthPoints n hn K).range.map (toLinEquiv (DI n) K).toMonoidHom

theorem eichler_mem_imageLin (k : Fin n ⊕ Fin n) {x y : DI n} (hxy : bmD n x y = 0)
    (hq : qdD n x * qdD n y = 0) (hk : rootIntMatrix n hn k = gamD n x * gamD n y) (u : K) :
    eichler (quadPlus n K) (Pi.single y 1) (u • Pi.single x 1) ∈ imageLin n hn K := by
  refine ⟨orthPoints n hn K (rootSubgroupPoints n hn k K (Multiplicative.ofAdd u)), ⟨_, rfl⟩, ?_⟩
  rw [MulEquiv.coe_toMonoidHom]
  exact toLinEquiv_eq_eichler n hxy hq u (by
    rw [coe_orthPoints, coe_rootSubgroupPoints_eq n hn hxy hq hk])

theorem simpleMem_imageLin : SimpleMem (plusFrame n K (by omega)) (imageLin n hn K) (by omega) := by
  refine ⟨fun k hk => ⟨fun c => ?_, fun c => ?_⟩, fun c => ?_, fun c => ?_⟩
  · simp only [plusFrame_vec, plusVec_true, plusVec_false]
    exact eichler_mem_imageLin n hn (.inl k) (x := .inl k) (y := .inr ⟨k.val + 1, hk⟩)
      (bmD_inl_inr_eq_zero n (fin_succ_ne n k hk)) rfl (rootIntMatrix_inl_lt n hn k hk) c
  · simp only [plusFrame_vec, plusVec_true, plusVec_false]
    exact eichler_mem_imageLin n hn (.inr k) (x := .inl ⟨k.val + 1, hk⟩) (y := .inr k)
      (bmD_inl_inr_eq_zero n (fin_succ_ne n k hk).symm) rfl (rootIntMatrix_inr_lt n hn k hk) c
  · simp only [plusFrame_vec, plusVec_true]
    exact eichler_mem_imageLin n hn (.inl ⟨n - 1, by omega⟩) (x := .inl ⟨n - 2, by omega⟩)
      (y := .inl ⟨n - 1, by omega⟩) rfl rfl (rootIntMatrix_inl_fork n hn) c
  · simp only [plusFrame_vec, plusVec_false]
    exact eichler_mem_imageLin n hn (.inr ⟨n - 1, by omega⟩) (x := .inr ⟨n - 1, by omega⟩)
      (y := .inr ⟨n - 2, by omega⟩) rfl rfl (rootIntMatrix_inr_fork n hn) c

theorem statedOmega_le_range : StatedOmega (StatedQuadPlus n K) ≤ (orthPoints n hn K).range := by
  rw [statedOmega_quadPlus_eq_map (by omega)]
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨C, hC, hCB⟩ := elementaryGroup_le_of_simple (by omega) (simpleMem_imageLin n hn) hB
  rw [← hCB, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact hC

theorem commutator_range :
    ⁅(orthPoints n hn K).range, (orthPoints n hn K).range⁆ = StatedOmega (StatedQuadPlus n K) := by
  apply le_antisymm
  · exact Subgroup.commutator_mono (range_orthPoints_le_isometries n hn)
      (range_orthPoints_le_isometries n hn)
  · have hperf := isPerfect_statedOmega_quadPlus (K := K) (n := n) (by omega)
    have e : ⁅StatedOmega (StatedQuadPlus n K), StatedOmega (StatedQuadPlus n K)⁆ =
        StatedOmega (StatedQuadPlus n K) := by
      rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [← e]
    exact Subgroup.commutator_mono (statedOmega_le_range n hn) (statedOmega_le_range n hn)

end Orth

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD
