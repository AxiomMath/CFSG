module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.SteinbergBQPlaneDiagonal

public section

namespace CFSG.Quasithin.H13.PSL3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.SteinbergBQ

variable {F : Type*} [Field F]

@[expose] noncomputable def statedProjEquivProjectiveSL (n : ℕ) (F : Type) [Field F] :
    CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL n F) ≃*
      projectiveSL n F :=
  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n F).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n := n) (K := F)).symm)

theorem transvection_commutator {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (s t : F) :
    SpecialLinearGroup.transvection hij s * SpecialLinearGroup.transvection hjk t *
        (SpecialLinearGroup.transvection hij s)⁻¹ * (SpecialLinearGroup.transvection hjk t)⁻¹ =
      SpecialLinearGroup.transvection hik (s * t) := by
  rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (SpecialLinearGroup.transvection hij s : Matrix (Fin n) (Fin n) F) *
      (SpecialLinearGroup.transvection hjk t : Matrix (Fin n) (Fin n) F) *
      (SpecialLinearGroup.transvection hij (-s) : Matrix (Fin n) (Fin n) F) *
      (SpecialLinearGroup.transvection hjk (-t) : Matrix (Fin n) (Fin n) F) =
      (SpecialLinearGroup.transvection hik (s * t) : Matrix (Fin n) (Fin n) F)
  simp only [SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    mul_one, one_mul, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hjk.symm,
    single_mul_single_of_ne _ _ _ _ hij.symm, single_mul_single_of_ne _ _ _ _ hik.symm]
  simp only [zero_mul, add_zero, mul_neg, neg_mul, neg_neg, ← single_neg]
  abel

theorem transvection_mul_transvection_pow_three [CharP F 2] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (SpecialLinearGroup.transvection hij (1 : F) * SpecialLinearGroup.transvection hij.symm 1) ^ 3
      = 1 := by
  rw [pow_three]
  apply Subtype.ext
  change (SpecialLinearGroup.transvection hij (1 : F) : Matrix (Fin n) (Fin n) F) *
      (SpecialLinearGroup.transvection hij.symm (1 : F) : Matrix (Fin n) (Fin n) F) *
      ((SpecialLinearGroup.transvection hij (1 : F) : Matrix (Fin n) (Fin n) F) *
      (SpecialLinearGroup.transvection hij.symm (1 : F) : Matrix (Fin n) (Fin n) F) *
      ((SpecialLinearGroup.transvection hij (1 : F) : Matrix (Fin n) (Fin n) F) *
      (SpecialLinearGroup.transvection hij.symm (1 : F) : Matrix (Fin n) (Fin n) F))) = 1
  simp only [SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    mul_one, one_mul, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hij,
    single_mul_single_of_ne _ _ _ _ hij.symm]
  simp only [mul_zero, add_zero]
  abel_nf
  have heven : ∀ (k : ℤ) (X : Matrix (Fin n) (Fin n) F), Even k → k • X = 0 := by
    rintro k X ⟨m, rfl⟩
    have hXX : X + X = 0 := by
      ext a b
      simp only [Matrix.add_apply, Matrix.zero_apply]
      exact CharTwo.add_self_eq_zero _
    rw [add_zsmul, ← zsmul_add, hXX, zsmul_zero]
  rw [heven 8 _ ⟨4, rfl⟩, heven 8 _ ⟨4, rfl⟩, heven 12 _ ⟨6, rfl⟩, heven 4 _ ⟨2, rfl⟩]
  simp

theorem transvection_mul_transvection_not_mem_scalars {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F) * SpecialLinearGroup.transvection hij.symm 1 ∉
      scalars n F := by
  rintro ⟨c, -, hc⟩
  have h := congrFun (congrFun hc i) j
  change ((SpecialLinearGroup.transvection hij (1 : F) : Matrix (Fin n) (Fin n) F) *
      (SpecialLinearGroup.transvection hij.symm (1 : F) : Matrix (Fin n) (Fin n) F)) i j = _ at h
  simp only [SpecialLinearGroup.transvection_coe, mul_add, add_mul, mul_one, one_mul,
    single_mul_single_same, Matrix.add_apply,
    Matrix.one_apply_ne hij, Matrix.single_apply, scalar_apply, diagonal_apply_ne _ hij] at h
  simp [hij, hij.symm] at h

theorem exists_inversion_of_ne_one : ∀ w : Equiv.Perm (Fin 3), w ≠ 1 →
    ∃ a b : Fin 3, a < b ∧ w b < w a := by
  decide

theorem le_projUpperTriangular_of_not_three_dvd [CharP F 2] {D : Subgroup (projectiveSL 3 F)}
    (hUD : projUnitriangular 3 F ≤ D) (h3 : ¬ 3 ∣ Nat.card D) : D ≤ projUpperTriangular 3 F := by
  classical
  intro x hx
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell g
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.mp hw
  obtain ⟨c, hc⟩ := isMonomial_signedPermMatrix (K := F) (n := 3) w
  by_cases hw1 : w = 1
  · subst hw1
    have hdiag : signedPermutation 3 F 1 ∈ upperTriangular 3 F := by
      intro i j hji
      have h1 := congrFun (hc j) i
      rw [Matrix.mulVec_single_one] at h1
      simp only [Equiv.Perm.one_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
        (ne_of_gt hji), ite_false, mul_zero] at h1
      exact h1
    exact ⟨_, mul_mem (mul_mem hb₁ hdiag) hb₂, rfl⟩
  · exfalso
    obtain ⟨a, b, hab, hba⟩ := exists_inversion_of_ne_one w hw1
    have hab' : a ≠ b := ne_of_lt hab
    have hwab : w a ≠ w b := w.injective.ne hab'
    have hconj := monomial_conj_transvection (M := signedPermutation 3 F w) (w := w) (c := c)
      hc hab' ((c b : F) * (c a : F)⁻¹)
    have hcoef : (c a : F) * (c b : F)⁻¹ * ((c b : F) * (c a : F)⁻¹) = 1 := by
      field_simp
    rw [hcoef] at hconj
    have hT := transvection_mem_unitriangular (K := F) hab ((c b : F) * (c a : F)⁻¹)
    set g := b₁ * signedPermutation 3 F w * b₂ with hg
    set u := b₂⁻¹ * SpecialLinearGroup.transvection hab' ((c b : F) * (c a : F)⁻¹) * b₂ with hu
    have huU : u ∈ unitriangular 3 F := by
      have h1 := conj_mem_unitriangular (inv_mem hb₂) hT
      rwa [inv_inv] at h1
    have hlow : proj 3 F (b₁ * SpecialLinearGroup.transvection hwab 1 * b₁⁻¹) ∈ D := by
      have h1 : b₁ * SpecialLinearGroup.transvection hwab 1 * b₁⁻¹ = g * u * g⁻¹ := by
        rw [hg, hu, ← hconj]
        group
      rw [h1, map_mul, map_mul, map_inv]
      exact mul_mem (mul_mem hx (hUD ⟨u, huU, rfl⟩)) (inv_mem hx)
    have hup : proj 3 F (b₁ * SpecialLinearGroup.transvection hwab.symm 1 * b₁⁻¹) ∈ D :=
      hUD ⟨_, conj_mem_unitriangular hb₁ (transvection_mem_unitriangular (K := F) hba 1), rfl⟩
    set M := SpecialLinearGroup.transvection hwab (1 : F) *
      SpecialLinearGroup.transvection hwab.symm 1 with hM
    set y := proj 3 F (b₁ * M * b₁⁻¹) with hy
    have hyD : y ∈ D := by
      have h1 : y = proj 3 F (b₁ * SpecialLinearGroup.transvection hwab 1 * b₁⁻¹) *
          proj 3 F (b₁ * SpecialLinearGroup.transvection hwab.symm 1 * b₁⁻¹) := by
        rw [hy, ← map_mul, hM]
        congr 1
        group
      rw [h1]
      exact mul_mem hlow hup
    have hy3 : y ^ 3 = 1 := by
      rw [hy, ← map_pow, conj_pow, hM, transvection_mul_transvection_pow_three hwab, mul_one,
        mul_inv_cancel, map_one]
    have hy1 : y ≠ 1 := by
      intro h1
      rw [hy, proj_eq_one_iff] at h1
      apply transvection_mul_transvection_not_mem_scalars (F := F) hwab
      have h2 := (scalars_normal 3 F).conj_mem _ h1 b₁⁻¹
      rwa [inv_inv, show b₁⁻¹ * (b₁ * M * b₁⁻¹) * b₁ = M by group] at h2
    have hord : orderOf (⟨y, hyD⟩ : D) = 3 :=
      orderOf_eq_prime (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hy3))
        (fun h => hy1 (congrArg Subtype.val h))
    have h4 : orderOf (⟨y, hyD⟩ : D) ∣ Nat.card D := orderOf_dvd_natCard _
    rw [hord] at h4
    exact h3 h4

theorem injective_diag_of_charpoly_eq {T : Matrix (Fin 3) (Fin 3) F} (hT : T.IsUpperTriangular)
    {d : Fin 3 → F} (hd : Function.Injective d) (hchar : T.charpoly = (diagonal d).charpoly) :
    Function.Injective fun i => T i i := by
  classical
  rw [charpoly_of_isUpperTriangular T hT, charpoly_diagonal] at hchar
  have hroots : (Finset.univ.val.map fun i => T i i) = Finset.univ.val.map d := by
    have h1 := congrArg Polynomial.roots hchar
    rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod] at h1
    have e1 : (Finset.univ.val.map fun i => Polynomial.X - Polynomial.C (T i i)) =
        ((Finset.univ.val.map fun i => T i i).map fun a => Polynomial.X - Polynomial.C a) := by
      rw [Multiset.map_map]
      rfl
    have e2 : (Finset.univ.val.map fun i => Polynomial.X - Polynomial.C (d i)) =
        ((Finset.univ.val.map d).map fun a => Polynomial.X - Polynomial.C a) := by
      rw [Multiset.map_map]
      rfl
    rw [e1, e2, Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C]
      at h1
    exact h1
  have hnd : (Finset.univ.val.map d).Nodup :=
    Multiset.Nodup.map hd Finset.univ.nodup
  rw [← hroots] at hnd
  intro i j hij
  exact Multiset.inj_on_of_nodup_map hnd i (Finset.mem_val.mpr (Finset.mem_univ i)) j
    (Finset.mem_val.mpr (Finset.mem_univ j)) hij

theorem exists_unitriangular_conj_diagonal {b : SpecialLinearGroup (Fin 3) F}
    (hb : b ∈ upperTriangular 3 F) (h01 : (b : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ b 1 1)
    (h02 : (b : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ b 2 2)
    (h12 : (b : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ b 2 2) :
    ∃ u ∈ unitriangular 3 F, ((u⁻¹ * b * u : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = diagonal fun i => (b : Matrix (Fin 3) (Fin 3) F) i i := by
  set B : Matrix (Fin 3) (Fin 3) F := (b : Matrix (Fin 3) (Fin 3) F) with hB
  have h10 : B 1 0 = 0 := hb 1 0 (by decide)
  have h20 : B 2 0 = 0 := hb 2 0 (by decide)
  have h21 : B 2 1 = 0 := hb 2 1 (by decide)
  have e01 : B 1 1 - B 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h01)
  have e12 : B 2 2 - B 1 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  have e02 : B 2 2 - B 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h02)
  set s := B 0 1 / (B 1 1 - B 0 0) with hs
  set t := B 1 2 / (B 2 2 - B 1 1) with ht
  set r := (B 0 1 * t + B 0 2) / (B 2 2 - B 0 0) with hr
  set U : Matrix (Fin 3) (Fin 3) F := !![1, s, r; 0, 1, t; 0, 0, 1] with hU
  have hUdet : U.det = 1 := by simp [hU, det_fin_three]
  set u : SpecialLinearGroup (Fin 3) F := ⟨U, hUdet⟩ with hu
  have huU : u ∈ unitriangular 3 F := by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> simp [hu, hU]
  have hBU : B * U = U * diagonal fun i => B i i := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hU, Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, diagonal_apply]
    · rw [hs]; field_simp; ring
    · rw [hr]; field_simp; ring
    · rw [ht]; field_simp; ring
  refine ⟨u, huU, ?_⟩
  have h1 : ((u⁻¹ * b * u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((u⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (B * U) := by
    change ((u⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * B * U = _
    rw [Matrix.mul_assoc]
  rw [h1, hBU, ← Matrix.mul_assoc]
  have h2 : ((u⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * U = 1 := by
    change ((u⁻¹ * u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
    rw [inv_mul_cancel]
    rfl
  rw [h2, Matrix.one_mul]

theorem exists_unitriangular_monomial {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {X : SpecialLinearGroup (Fin 3) F}
    (hX : ((X : Matrix (Fin 3) (Fin 3) F)⁻¹ * diagPow ζ (regVec p : Fin 3 → ZMod p) *
      X).IsUpperTriangular) :
    ∃ u ∈ unitriangular 3 F, ∃ w : Equiv.Perm (Fin 3),
      IsMonomial ((X * u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) w := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp3 : 3 ≤ p := by omega
  set r : Matrix (Fin 3) (Fin 3) F := diagPow ζ (regVec p : Fin 3 → ZMod p) with hr
  set T : Matrix (Fin 3) (Fin 3) F := (X : Matrix (Fin 3) (Fin 3) F)⁻¹ * r * X with hT
  have hXinv : ((X⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (X : Matrix (Fin 3) (Fin 3) F)⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    change ((X⁻¹ * X : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
    rw [inv_mul_cancel]
    rfl
  have hdetr : r.det = 1 := det_diagPow hζ.pow_eq_one (regVec p).2
  have hdetT : T.det = 1 := by
    rw [hT, det_mul, det_mul, hdetr, mul_one, ← det_mul, ← hXinv]
    change ((X⁻¹ * X : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1
    rw [inv_mul_cancel]
    exact det_one
  set b : SpecialLinearGroup (Fin 3) F := ⟨T, hdetT⟩ with hb
  have hbB : b ∈ upperTriangular 3 F := fun i j hji => hX hji
  have hchar : T.charpoly = r.charpoly := by
    have := Matrix.charpoly_units_conj' (SpecialLinearGroup.toGL X) r
    simpa using this
  have hinj := injective_diag_of_charpoly_eq hX (regVec_pow_injective hp3 hζ) hchar
  obtain ⟨u, huU, hu⟩ := exists_unitriangular_conj_diagonal hbB (fun h => absurd (hinj h)
    (by decide)) (fun h => absurd (hinj h) (by decide)) (fun h => absurd (hinj h) (by decide))
  refine ⟨u, huU, ?_⟩
  set N : Matrix (Fin 3) (Fin 3) F := ((X * u : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) with hN
  set N' : Matrix (Fin 3) (Fin 3) F := (((X * u)⁻¹ : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) with hN'
  have hN'N : N' * N = 1 := by
    change (((X * u)⁻¹ * (X * u) : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1
    rw [inv_mul_cancel]
    rfl
  have hNN' : N * N' = 1 := by
    change (((X * u) * (X * u)⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1
    rw [mul_inv_cancel]
    rfl
  have hconj : N' * r * N = diagonal fun i => (b : Matrix (Fin 3) (Fin 3) F) i i := by
    rw [← hu]
    change (((X * u)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * r *
      ((X * u : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((u⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * T *
        (u : Matrix (Fin 3) (Fin 3) F)
    rw [_root_.mul_inv_rev, hT, ← hXinv]
    change ((u⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((X⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * r *
        ((X : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F)) = _
    simp only [Matrix.mul_assoc]
  obtain ⟨w, t, ht0, ht⟩ := exists_perm_of_conj_diagonal hp3 hζ hN'N hNN' _ hconj
  exact ⟨w, fun m => Units.mk0 (t m) (ht0 m), fun m => by rw [Units.val_mk0]; exact ht m⟩

theorem eq_finRotate_or_of_pow_three : ∀ w : Equiv.Perm (Fin 3), w ≠ 1 → w ^ 3 = 1 →
    w = finRotate 3 ∨ w = (finRotate 3)⁻¹ := by
  decide

end CFSG.Quasithin.H13.PSL3
