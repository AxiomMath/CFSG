module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBPoints
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBGen
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDPoints

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame.Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {bm : Matrix ι ι ℤ} {qd : ι → ℤ}
  {N : Type} [Fintype N] [DecidableEq N] (F : Frame bm qd N) (A : Type*) [CommRing A]

@[expose] def vecHom : F.normGroup A →* GL ι A where
  toFun g := ⟨F.rho A g, F.rho A (g : GL N A)⁻¹, by
      rw [← rho_mul g.2 (inv_mem g.2), mul_inv_cancel, rho_one], by
      rw [← rho_mul (inv_mem g.2) g.2, inv_mul_cancel, rho_one]⟩
  map_one' := Units.ext rho_one
  map_mul' g h := Units.ext (rho_mul g.2 h.2)

theorem coe_vecHom (g : F.normGroup A) :
    ((F.vecHom A g : GL ι A) : Matrix ι ι A) = F.rho A g :=
  rfl

end CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame.Frame

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame.Frame

open BI CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {m : ℕ} {N : Type} [Fintype N] [DecidableEq N] (F : Frame (bmB m) (qdB m) N)
  (A : Type*) [CommRing A]

theorem vec_mul_vec_B (c : BI m → A) :
    F.vec A c * F.vec A c =
      algebraMap A (Matrix N N A) (∑ i, c (cr i) * c (an i) + c zeta ^ 2) := by
  set X : Matrix N N A := ∑ i, c (cr i) • F.gamA A (cr i)
  set Y : Matrix N N A := ∑ i, c (an i) • F.gamA A (an i)
  set Z : Matrix N N A := c zeta • F.gamA A zeta
  have hv : F.vec A c = X + Y + Z := by
    rw [vec, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.univ_unit,
      Finset.sum_singleton, add_assoc]
  have hX : X * X = 0 := sum_smul_mul_self_eq_zero _ _ _
    (fun i => by rw [gamA_sq, qdB_cr, Int.cast_zero, map_zero])
    (fun i j _ => by rw [gamA_anticomm, bmB_cr_cr, Int.cast_zero, map_zero])
  have hY : Y * Y = 0 := sum_smul_mul_self_eq_zero _ _ _
    (fun i => by rw [gamA_sq, qdB_an, Int.cast_zero, map_zero])
    (fun i j _ => by rw [gamA_anticomm, bmB_an_an, Int.cast_zero, map_zero])
  have hZ : Z * Z = algebraMap A (Matrix N N A) (c zeta ^ 2) := by
    rw [smul_mul_smul_comm, gamA_sq, qdB_zeta, Int.cast_one, map_one, ← pow_two,
      Algebra.algebraMap_eq_smul_one]
  have hXY : X * Y + Y * X =
      algebraMap A (Matrix N N A) (∑ i, c (cr i) * c (an i)) := by
    have e : ∀ i j, (c (cr i) • F.gamA A (cr i)) * (c (an j) • F.gamA A (an j)) +
        (c (an j) • F.gamA A (an j)) * (c (cr i) • F.gamA A (cr i)) =
        algebraMap A (Matrix N N A) (if i = j then c (cr i) * c (an j) else 0) := by
      intro i j
      rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (c (an j)), ← smul_add,
        gamA_anticomm, bmB_cr_an, Algebra.smul_def, ← map_mul]
      split_ifs <;> simp
    have hYX : Y * X = ∑ i, ∑ j,
        (c (an j) • F.gamA A (an j)) * (c (cr i) • F.gamA A (cr i)) := by
      rw [Finset.sum_mul_sum, Finset.sum_comm]
    rw [Finset.sum_mul_sum, hYX, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, e]
    rw [show (∑ x : Fin m, ∑ y : Fin m, algebraMap A (Matrix N N A)
        (if x = y then c (cr x) * c (an y) else 0)) = algebraMap A (Matrix N N A)
        (∑ x : Fin m, ∑ y : Fin m, if x = y then c (cr x) * c (an y) else 0) by
      simp only [map_sum]]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq Finset.univ i, ite_eq_left (Finset.mem_univ i)]
  have hZanti : ∀ {a : BI m}, bmB m a zeta = 0 → ∀ r : A,
      (r • F.gamA A a) * Z + Z * (r • F.gamA A a) = 0 := by
    intro a ha r
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (c zeta), ← smul_add, gamA_anticomm,
      ha, Int.cast_zero, map_zero, smul_zero]
  have hXZ : X * Z + Z * X = 0 := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => hZanti (bmB_cr_zeta i) _
  have hYZ : Y * Z + Z * Y = 0 := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => hZanti (bmB_an_zeta i) _
  have key : (X + Y + Z) * (X + Y + Z) =
      X * X + Y * Y + Z * Z + (X * Y + Y * X) + (X * Z + Z * X) + (Y * Z + Z * Y) := by
    noncomm_ring
  rw [hv, key, hX, hY, hZ, hXY, hXZ, hYZ, map_add]
  abel

variable {F A}

theorem oddQuad_rho [Nonempty N] {K : Type} [Field K] {g : GL N K} (hg : g ∈ F.normGroup K)
    (c : BI m → K) :
    StatedQuadOdd m K (F.rho K g *ᵥ c) = StatedQuadOdd m K c := by
  have h1 := F.vec_mul_vec_B K (F.rho K g *ᵥ c)
  have h2 : F.vec K (F.rho K g *ᵥ c) * F.vec K (F.rho K g *ᵥ c) =
      (g : Matrix N N K) * (F.vec K c * F.vec K c) * (↑g⁻¹ : Matrix N N K) := by
    have hgg : (↑g⁻¹ : Matrix N N K) * (g : Matrix N N K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [← conj_vec hg]
    calc (g : Matrix N N K) * F.vec K c * (↑g⁻¹ : Matrix N N K) *
          ((g : Matrix N N K) * F.vec K c * (↑g⁻¹ : Matrix N N K))
        = (g : Matrix N N K) * F.vec K c * ((↑g⁻¹ : Matrix N N K) * (g : Matrix N N K)) *
            F.vec K c * (↑g⁻¹ : Matrix N N K) := by noncomm_ring
      _ = _ := by rw [hgg]; noncomm_ring
  rw [h1, F.vec_mul_vec_B K c, ← Algebra.commutes, mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_one] at h2
  exact (algebraMap K (Matrix N N K)).injective h2

end CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame.Frame

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinB

open TauCeti TauCeti.TypeBSpinCarrier SpinFrame SpinFrame.BI
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open scoped Matrix

variable (n : ℕ)

section Orth

variable {K : Type} [Field K]

variable (K) in
@[expose] def orthPointsB : points n K →* GL (BI (n + 1)) K :=
  ((frame n).vecHom K).comp (Subgroup.inclusion (points_le_normGroup n K))

theorem coe_orthPointsB (g : points n K) :
    ((orthPointsB n K g : GL (BI (n + 1)) K) : Matrix (BI (n + 1)) (BI (n + 1)) K) =
      (frame n).rho K (g : GL (Fin (dimension n)) K) :=
  rfl

theorem orthPointsB_ker_le_center : (orthPointsB n K).ker ≤ Subgroup.center (points n K) := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hρ : (frame n).rho K (g : GL (Fin (dimension n)) K) = 1 := by
    rw [← coe_orthPointsB, hg, Units.val_one]
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
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hs, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]

theorem orthPointsB_mem_isometries (g : points n K) :
    orthPointsB n K g ∈ Subgroup.closure {A : GL (BI (n + 1)) K |
      ∀ v : BI (n + 1) → K,
        StatedQuadOdd (n + 1) K ((A : Matrix (BI (n + 1)) (BI (n + 1)) K) *ᵥ v) =
          StatedQuadOdd (n + 1) K v} :=
  Subgroup.subset_closure fun v => (frame n).oddQuad_rho (points_le_normGroup n K g.2) v

theorem range_orthPointsB_le_isometries :
    (orthPointsB n K).range ≤ Subgroup.closure {A : GL (BI (n + 1)) K |
      ∀ v : BI (n + 1) → K,
        StatedQuadOdd (n + 1) K ((A : Matrix (BI (n + 1)) (BI (n + 1)) K) *ᵥ v) =
          StatedQuadOdd (n + 1) K v} := by
  rintro _ ⟨g, rfl⟩
  exact orthPointsB_mem_isometries n g

omit [Field K] in
theorem bmB_comm {m : ℕ} (a b : BI m) : bmB m a b = bmB m b a := by
  rcases a with i | i | ⟨⟩ <;> rcases b with j | j | ⟨⟩
  · rfl
  · by_cases h : i = j
    · subst h
      rfl
    · rw [bmB_cr_an, bmB_an_cr, ite_eq_right h, ite_eq_right (Ne.symm h)]
  · rfl
  · by_cases h : i = j
    · subst h
      rfl
    · rw [bmB_an_cr, bmB_cr_an, ite_eq_right h, ite_eq_right (Ne.symm h)]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem polar_quadOdd_single (v : BI (n + 1) → K) (y : BI (n + 1)) :
    QuadraticMap.polar (quadOdd (n + 1) K) v (Pi.single y 1) =
      ∑ z, ((bmB (n + 1) y z : ℤ) : K) * v z := by
  rcases y with j | j | u
  · rw [polar_quadOdd_single_inl]
    simp [Fintype.sum_sum_type]
  · rw [polar_quadOdd_single_inr_inl]
    simp [Fintype.sum_sum_type]
  · cases u
    rw [polar_quadOdd_single_inr_inr, BI.sum_eq]
    simp only [show (Sum.inr (Sum.inr ()) : BI (n + 1)) = zeta from rfl, bmB_zeta_emb,
      bmB_zeta_zeta, Int.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
    norm_num

theorem quadOdd_smul_single (y : BI (n + 1)) (u : K) :
    quadOdd (n + 1) K (u • Pi.single y 1) = u ^ 2 * ((qdB (n + 1) y : ℤ) : K) := by
  rw [QuadraticMap.map_smul, smul_eq_mul, ← pow_two]
  congr 1
  rcases y with j | j | u
  · simp [quadOdd_apply, Pi.single_apply]
  · simp [quadOdd_apply, Pi.single_apply]
  · cases u
    simp [quadOdd_apply]

theorem rho_rootUnit_mulVec {x y : BI (n + 1)} (hxy : bmB (n + 1) x y = 0)
    (hq : qdB (n + 1) x * qdB (n + 1) y = 0) (u : K) (v : BI (n + 1) → K) (b : BI (n + 1)) :
    ((frame n).rho K ((frame n).rootUnit K hxy hq u) *ᵥ v) b =
      v b + u * (if b = x then 1 else 0) * ∑ z, ((bmB (n + 1) y z : ℤ) : K) * v z -
        u * (if b = y then 1 else 0) * ∑ z, ((bmB (n + 1) x z : ℤ) : K) * v z -
        u * u * (((qdB (n + 1) x : ℤ) : K) * (if b = y then 1 else 0) *
            ∑ z, ((bmB (n + 1) y z : ℤ) : K) * v z +
          ((qdB (n + 1) y : ℤ) : K) * (if b = x then 1 else 0) *
            ∑ z, ((bmB (n + 1) x z : ℤ) : K) * v z) := by
  have e : ∀ z, (frame n).rho K ((frame n).rootUnit K hxy hq u) b z * v z =
      (if b = z then v z else 0) +
        u * (if b = x then 1 else 0) * (((bmB (n + 1) y z : ℤ) : K) * v z) -
        u * (if b = y then 1 else 0) * (((bmB (n + 1) x z : ℤ) : K) * v z) -
        u * u * ((((qdB (n + 1) x : ℤ) : K) * (if b = y then 1 else 0)) *
            (((bmB (n + 1) y z : ℤ) : K) * v z) +
          (((qdB (n + 1) y : ℤ) : K) * (if b = x then 1 else 0)) *
            (((bmB (n + 1) x z : ℤ) : K) * v z)) := by
    intro z
    rw [Frame.rho_rootUnit]
    split_ifs <;> ring
  simp only [Matrix.mulVec, dotProduct, e, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]

theorem toLinEquiv_eq_eichler_right {x y : BI (n + 1)} (hxy : bmB (n + 1) x y = 0)
    (hq : qdB (n + 1) x * qdB (n + 1) y = 0) (hqy : qdB (n + 1) y = 0) (u : K)
    {A : GL (BI (n + 1)) K}
    (hA : A.val = (frame n).rho K ((frame n).rootUnit K hxy hq u)) :
    toLinEquiv (BI (n + 1)) K A =
      eichler (quadOdd (n + 1) K) (Pi.single y 1) (u • Pi.single x 1) := by
  have hy : quadOdd (n + 1) K (Pi.single y 1) = 0 := by
    have h := quadOdd_smul_single n y (1 : K)
    rwa [one_smul, hqy, Int.cast_zero, mul_zero] at h
  have hyx : bmB (n + 1) y x = 0 := (bmB_comm y x).trans hxy
  have hpol : QuadraticMap.polar (quadOdd (n + 1) K) (Pi.single y 1) (u • Pi.single x 1) = 0 := by
    rw [QuadraticMap.polar_comm, QuadraticMap.polar_smul_left, polar_quadOdd_single]
    simp [Pi.single_apply, hyx]
  refine LinearEquiv.ext fun v => ?_
  rw [toLinEquiv_apply, hA, eichler_apply hy hpol, quadOdd_smul_single,
    QuadraticMap.polar_smul_right, polar_quadOdd_single, polar_quadOdd_single]
  funext b
  rw [rho_rootUnit_mulVec]
  simp only [hqy, Int.cast_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  ring

theorem toLinEquiv_eq_eichler_left {x y : BI (n + 1)} (hxy : bmB (n + 1) x y = 0)
    (hq : qdB (n + 1) x * qdB (n + 1) y = 0) (hqx : qdB (n + 1) x = 0) (u : K)
    {A : GL (BI (n + 1)) K}
    (hA : A.val = (frame n).rho K ((frame n).rootUnit K hxy hq u)) :
    toLinEquiv (BI (n + 1)) K A =
      eichler (quadOdd (n + 1) K) (Pi.single x 1) ((-u) • Pi.single y 1) := by
  have hx : quadOdd (n + 1) K (Pi.single x 1) = 0 := by
    have h := quadOdd_smul_single n x (1 : K)
    rwa [one_smul, hqx, Int.cast_zero, mul_zero] at h
  have hpol : QuadraticMap.polar (quadOdd (n + 1) K) (Pi.single x 1) ((-u) • Pi.single y 1) =
      0 := by
    rw [QuadraticMap.polar_comm, QuadraticMap.polar_smul_left, polar_quadOdd_single]
    simp [Pi.single_apply, hxy]
  refine LinearEquiv.ext fun v => ?_
  rw [toLinEquiv_apply, hA, eichler_apply hx hpol, quadOdd_smul_single,
    QuadraticMap.polar_smul_right, polar_quadOdd_single, polar_quadOdd_single]
  funext b
  rw [rho_rootUnit_mulVec]
  simp only [hqx, Int.cast_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  ring

variable (K) in
abbrev imageLinB : Subgroup ((BI (n + 1) → K) ≃ₗ[K] (BI (n + 1) → K)) :=
  (orthPointsB n K).range.map (toLinEquiv (BI (n + 1)) K).toMonoidHom

theorem eichler_mem_imageLinB_right (k : Fin (n + 1) ⊕ Fin (n + 1)) {x y : BI (n + 1)}
    (hxy : bmB (n + 1) x y = 0) (hq : qdB (n + 1) x * qdB (n + 1) y = 0)
    (hqy : qdB (n + 1) y = 0) (hk : rootIntMatrix n k = gamB n x * gamB n y) (u : K) :
    eichler (quadOdd (n + 1) K) (Pi.single y 1) (u • Pi.single x 1) ∈ imageLinB n K := by
  refine ⟨orthPointsB n K (rootSubgroupPoints n k K (Multiplicative.ofAdd u)), ⟨_, rfl⟩, ?_⟩
  rw [MulEquiv.coe_toMonoidHom]
  exact toLinEquiv_eq_eichler_right n hxy hq hqy u (by
    rw [coe_orthPointsB, coe_rootSubgroupPoints_eq n hxy hq hk])

theorem eichler_mem_imageLinB_left (k : Fin (n + 1) ⊕ Fin (n + 1)) {x y : BI (n + 1)}
    (hxy : bmB (n + 1) x y = 0) (hq : qdB (n + 1) x * qdB (n + 1) y = 0)
    (hqx : qdB (n + 1) x = 0) (hk : rootIntMatrix n k = gamB n x * gamB n y) (u : K) :
    eichler (quadOdd (n + 1) K) (Pi.single x 1) ((-u) • Pi.single y 1) ∈ imageLinB n K := by
  refine ⟨orthPointsB n K (rootSubgroupPoints n k K (Multiplicative.ofAdd u)), ⟨_, rfl⟩, ?_⟩
  rw [MulEquiv.coe_toMonoidHom]
  exact toLinEquiv_eq_eichler_left n hxy hq hqx u (by
    rw [coe_orthPointsB, coe_rootSubgroupPoints_eq n hxy hq hk])

theorem fin_succ_ne' (i : Fin (n + 1)) (hi : i.val < n) : i ≠ ⟨i.val + 1, by omega⟩ :=
  fun h => by
    have := congrArg Fin.val h
    simp at this

theorem chainMem_imageLinB : ChainMem (oddFrame (n + 1) K) (imageLinB n K) := by
  intro k hk
  have hkn : k.val < n := by omega
  refine ⟨fun c => ?_, fun c => ?_⟩
  · simp only [oddFrame_vec, oddVec_true, oddVec_false]
    exact eichler_mem_imageLinB_right n (.inl k) (x := cr k) (y := an ⟨k.val + 1, hk⟩)
      (Frame.bmB_cr_an_eq_zero (fin_succ_ne' n k hkn)) rfl rfl (rootIntMatrix_inl_lt n k hkn) c
  · simp only [oddFrame_vec, oddVec_true, oddVec_false]
    exact eichler_mem_imageLinB_right n (.inr k) (x := cr ⟨k.val + 1, hk⟩) (y := an k)
      (Frame.bmB_cr_an_eq_zero (fin_succ_ne' n k hkn).symm) rfl rfl
      (rootIntMatrix_inr_lt n k hkn) c

theorem shortMem_imageLinB (s : Bool) :
    ShortMem (oddFrame (n + 1) K) (imageLinB n K) ⟨n + 1 - 1, by omega⟩ s := by
  intro c
  have hl : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [hl]
  cases s
  · simp only [oddFrame_vec, oddVec_false, oddFrame_z, oddZ]
    exact eichler_mem_imageLinB_right n (.inr (Fin.last n)) (x := zeta) (y := an (Fin.last n))
      (bmB_zeta_an _) rfl rfl (rootIntMatrix_inr_last n) c
  · simp only [oddFrame_vec, oddVec_true, oddFrame_z, oddZ]
    have h := eichler_mem_imageLinB_left n (K := K) (.inl (Fin.last n)) (x := cr (Fin.last n))
      (y := zeta) (bmB_cr_zeta _) rfl rfl (rootIntMatrix_inl_last n) (-c)
    rwa [neg_neg] at h

theorem elementaryGroup_le_imageLinB (h2 : (2 : K) ≠ 0) (hn : 1 ≤ n) :
    elementaryGroup (quadOdd (n + 1) K) ≤ imageLinB n K :=
  elementaryGroup_le_of_simpleB h2 (by omega) (chainMem_imageLinB n) (shortMem_imageLinB n)

theorem statedOmega_le_rangeB (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    StatedOmega (StatedQuadOdd (n + 1) K) ≤ (orthPointsB n K).range := by
  rw [statedOmega_quadOdd_eq_map h2 (by omega)]
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨C, hC, hCB⟩ := elementaryGroup_le_imageLinB n h2 (by omega) hB
  rw [← hCB, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact hC

theorem commutator_rangeB (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    ⁅(orthPointsB n K).range, (orthPointsB n K).range⁆ =
      StatedOmega (StatedQuadOdd (n + 1) K) := by
  apply le_antisymm
  · exact Subgroup.commutator_mono (range_orthPointsB_le_isometries n)
      (range_orthPointsB_le_isometries n)
  · have hperf := isPerfect_statedOmega_quadOdd (K := K) (n := n + 1) h2 (by omega)
    have e : ⁅StatedOmega (StatedQuadOdd (n + 1) K), StatedOmega (StatedQuadOdd (n + 1) K)⁆ =
        StatedOmega (StatedQuadOdd (n + 1) K) := by
      rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [← e]
    exact Subgroup.commutator_mono (statedOmega_le_rangeB n h2 hn) (statedOmega_le_rangeB n h2 hn)

end Orth

end CFSG.RankThree.PartTwo.Census.Carrier.SpinB
