module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUBasic
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinearSU
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSURoot
public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeLevi
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.StandardType

namespace RootCentSU

open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits OTwoGen
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom mat_iotaHom iotaMat
  iotaMat_isBlkOn mid mem_range_mid rev_mid mid_injective val_mid mid_ne_zero mid_ne_last
  submatrix_iotaMat)

section Generation

theorem sq_eq_one_of_add_self {A M : Type*} [AddGroup A] [Monoid M] (φ : Multiplicative A →* M)
    (hA : ∀ a : A, a + a = 0) (c : Multiplicative A) : φ c ^ 2 = 1 := by
  rw [pow_two, ← map_mul]
  have h : c * c = 1 := Multiplicative.toAdd.injective (by
    rw [toAdd_mul, toAdd_one, hA])
  rw [h, map_one]

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem top_le_closure_SU (hF : Nat.card F = (2 ^ f) ^ 2) {k : ℕ} (hk : 2 ≤ k) :
    (⊤ : Subgroup (SU (unitaryInvolution F 2 f) k)) ≤
      Subgroup.closure {x | ∃ j : ℕ, x ^ (2 ^ j) = 1} := by
  have hσ := unitaryInvolution_involutive hF
  have h1 : (1 : F) + unitaryInvolution F 2 f 1 = 0 := by
    rw [map_one, CharTwo.add_self_eq_zero]
  refine (eq_top_of_rootElements_le hσ ⟨1, one_ne_zero, h1⟩
    (fun _ hx => exists_add_unitaryInvolution_eq hF hx) (fun x hx => ?_) hk _ ?_ ?_ ?_).ge
  · rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨0, by simp⟩
    · exact CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hF hx hx0
  · intro i j hij hi hj _ c
    exact Subgroup.subset_closure ⟨1, by
      rw [pow_one]
      exact sq_eq_one_of_add_self _ (fun a => CharTwo.add_self_eq_zero a) c⟩
  · intro i hi c
    exact Subgroup.subset_closure ⟨1, by
      rw [pow_one]
      exact sq_eq_one_of_add_self _ (fun a => Subtype.ext (CharTwo.add_self_eq_zero (a : F))) c⟩
  · intro i k' hi hik hk' x hx
    obtain ⟨a, b, -, hxm⟩ := hx
    refine Subgroup.subset_closure ⟨2, Subtype.ext (Units.ext ?_)⟩
    have e2 : heisenbergMatrix (unitaryInvolution F 2 f) i k' a b *
        heisenbergMatrix (unitaryInvolution F 2 f) i k' a b =
        heisenbergMatrix (unitaryInvolution F 2 f) i k' 0 (a * unitaryInvolution F 2 f a) := by
      rw [heisenbergMatrix_mul _ hi hik hk', CharTwo.add_self_eq_zero, CharTwo.sub_eq_add,
        CharTwo.add_self_eq_zero, zero_add]
    have e4 : heisenbergMatrix (unitaryInvolution F 2 f) i k' 0 (a * unitaryInvolution F 2 f a) *
        heisenbergMatrix (unitaryInvolution F 2 f) i k' 0 (a * unitaryInvolution F 2 f a) = 1 := by
      rw [heisenbergMatrix_mul _ hi hik hk', add_zero, CharTwo.add_self_eq_zero, zero_mul,
        sub_zero, heisenbergMatrix_zero]
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hxm, show 2 ^ 2 = 2 + 2 from rfl, pow_add,
      pow_two, e2, e4, Subgroup.coe_one, Units.val_one]

end Generation

section Unipotent

theorem pow_three_eq_zero_of_level {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (N : Matrix ι ι R) (lv : ι → ℕ) (hlv : ∀ a, lv a ≤ 2)
    (hN : ∀ a b, lv a ≤ lv b → N a b = 0) : N ^ 3 = 0 := by
  ext a b
  rw [pow_three, Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases h1 : lv a ≤ lv c
  · rw [hN a c h1, zero_mul]
  by_cases h2 : lv c ≤ lv d
  · rw [hN c d h2, zero_mul, mul_zero]
  by_cases h3 : lv d ≤ lv b
  · rw [hN d b h3, mul_zero, mul_zero]
  have := hlv a
  omega

theorem one_add_mul_self {R : Type*} [Ring R] {X : R} (hX : X + X = 0) :
    (1 + X) * (1 + X) = 1 + X * X := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, add_assoc, ← add_assoc X X, hX,
    zero_add]

theorem one_add_pow_four {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CharP R 2]
    {N : Matrix ι ι R} (hN : N ^ 3 = 0) : (1 + N) ^ 4 = 1 := by
  have h2 : ∀ X : Matrix ι ι R, X + X = 0 := fun X => by
    ext a b
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  have hN4 : N * N * (N * N) = 0 := by
    rw [show N * N * (N * N) = N * N ^ 3 by rw [pow_three]; noncomm_ring, hN, mul_zero]
  rw [show 4 = 2 + 2 from rfl, pow_add, pow_two, one_add_mul_self (h2 N),
    one_add_mul_self (h2 _), hN4, add_zero]

end Unipotent

section Commute

variable {F : Type} [Field F] {k : ℕ}

theorem ggInvUMatrix_one_eq : ggInvUMatrix (k + 2) 1 F = 1 + single (Fin.last (k + 1)) 0 1 := by
  rw [ggInvUMatrix_one (by omega)]
  have hL : Fin.rev (⟨0, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) := by
    ext
    simp
  rw [hL]
  rfl

theorem commute_single_of_commute {A : Matrix (Fin (k + 2)) (Fin (k + 2)) F}
    (hA : A * ggInvUMatrix (k + 2) 1 F = ggInvUMatrix (k + 2) 1 F * A) :
    A * single (Fin.last (k + 1)) 0 1 = single (Fin.last (k + 1)) 0 1 * A := by
  rw [ggInvUMatrix_one_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hA
  exact add_left_cancel hA

theorem col_last_of_commute {A : Matrix (Fin (k + 2)) (Fin (k + 2)) F}
    (hA : A * ggInvUMatrix (k + 2) 1 F = ggInvUMatrix (k + 2) 1 F * A) (a : Fin (k + 2)) :
    A a (Fin.last (k + 1)) = if a = Fin.last (k + 1) then A 0 0 else 0 := by
  have h := congrFun (congrFun (commute_single_of_commute hA) a) 0
  rw [mul_single_apply_same, mul_one] at h
  by_cases ha : a = Fin.last (k + 1)
  · rw [ite_eq_left ha, h, ha, single_mul_apply_same, one_mul]
  · rw [ite_eq_right ha, h, single_mul_apply_of_ne _ _ _ _ _ ha]

theorem row_zero_of_commute {A : Matrix (Fin (k + 2)) (Fin (k + 2)) F}
    (hA : A * ggInvUMatrix (k + 2) 1 F = ggInvUMatrix (k + 2) 1 F * A) (b : Fin (k + 2)) :
    A 0 b = if b = 0 then A (Fin.last (k + 1)) (Fin.last (k + 1)) else 0 := by
  have h := congrFun (congrFun (commute_single_of_commute hA) (Fin.last (k + 1))) b
  rw [single_mul_apply_same, one_mul] at h
  by_cases hb : b = 0
  · rw [ite_eq_left hb, ← h, hb, mul_single_apply_same, mul_one]
  · rw [ite_eq_right hb, ← h, mul_single_apply_of_ne _ _ _ _ _ hb]

theorem corner_eq_of_commute {A : Matrix (Fin (k + 2)) (Fin (k + 2)) F}
    (hA : A * ggInvUMatrix (k + 2) 1 F = ggInvUMatrix (k + 2) 1 F * A) :
    A (Fin.last (k + 1)) (Fin.last (k + 1)) = A 0 0 := by
  rw [col_last_of_commute hA, ite_eq_left rfl]

theorem commute_of_isBlkOn {A : Matrix (Fin (k + 2)) (Fin (k + 2)) F}
    (hA : CFSG.LieType.Steinberg.IsBlkOn mid A) :
    A * ggInvUMatrix (k + 2) 1 F = ggInvUMatrix (k + 2) 1 F * A := by
  have hL : Fin.last (k + 1) ∉ Set.range (mid (m := k)) := by
    rw [mem_range_mid]
    simp
  have h0 : (0 : Fin (k + 2)) ∉ Set.range (mid (m := k)) := by
    rw [mem_range_mid]
    simp
  rw [ggInvUMatrix_one_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  by_cases hb : b = 0
  · subst hb
    rw [mul_single_apply_same, mul_one, hA a _ (Or.inr hL)]
    by_cases ha : a = Fin.last (k + 1)
    · subst ha
      rw [single_mul_apply_same, one_mul, hA _ _ (Or.inl h0), one_apply_eq, one_apply_eq]
    · rw [single_mul_apply_of_ne _ _ _ _ _ ha, one_apply_ne ha]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hb]
    by_cases ha : a = Fin.last (k + 1)
    · subst ha
      rw [single_mul_apply_same, one_mul, hA _ _ (Or.inl h0), one_apply_ne (Ne.symm hb)]
    · rw [single_mul_apply_of_ne _ _ _ _ _ ha]

theorem det_eq_det_submatrix_mid {M : Matrix (Fin (k + 2)) (Fin (k + 2)) F}
    (hrow : ∀ b, M 0 b = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b)
    (hcol : ∀ a, M a (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) a (Fin.last (k + 1))) :
    M.det = (M.submatrix mid mid).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · rw [hrow, one_apply_eq, Fin.val_zero, pow_zero, one_mul, one_mul, Fin.succAbove_zero,
      Matrix.det_succ_column _ (Fin.last k), Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [Matrix.submatrix_apply, Fin.succ_last, hcol, one_apply_eq, mul_one, Fin.val_last,
        ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, Fin.succAbove_last,
        Matrix.submatrix_submatrix]
      congr 2
    · intro i _
      rw [Matrix.submatrix_apply, Fin.succ_last, hcol, one_apply_ne (fun h => by
        have := congrArg Fin.val h
        simp at this
        omega), mul_zero, zero_mul]
  · intro j _
    rw [hrow, one_apply_ne (Fin.succ_ne_zero j).symm, mul_zero, zero_mul]

end Commute

section Decomposition

variable {F : Type} [Field F] {k : ℕ}

theorem zero_not_mem_range_mid : (0 : Fin (k + 2)) ∉ Set.range (mid (m := k)) := by
  rw [mem_range_mid]
  simp

theorem last_not_mem_range_mid : Fin.last (k + 1) ∉ Set.range (mid (m := k)) := by
  rw [mem_range_mid]
  simp

theorem isometry_submatrix_mid {σ : F ≃+* F} (x : SU σ (k + 2))
    (hrow : ∀ b, mat σ (k + 2) x 0 b = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b) :
    conjTr σ ((mat σ (k + 2) x).submatrix mid mid) * antidiag k *
      (mat σ (k + 2) x).submatrix mid mid = antidiag k := by
  ext i j
  rw [CFSG.LieType.Steinberg.conjTr_mul_antidiag_mul_apply,
    Fintype.sum_of_injective mid mid_injective _
      (fun t => σ (mat σ (k + 2) x t (mid i)) * mat σ (k + 2) x (Fin.rev t) (mid j)) ?_ ?_,
    sum_mat_mul_mat x (mid i) (mid j)]
  · simp only [antidiag, Matrix.of_apply, rev_mid, mid_injective.eq_iff]
  · intro t ht
    by_cases h0 : t = 0
    · subst h0
      rw [hrow, one_apply_ne (Ne.symm (mid_ne_zero i)), map_zero, zero_mul]
    · have hL : t = Fin.last (k + 1) := by
        rw [mem_range_mid] at ht
        have h0' : (t : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
        ext
        simp only [Fin.val_last]
        omega
      subst hL
      rw [Fin.rev_last, hrow, one_apply_ne (Ne.symm (mid_ne_zero j)), mul_zero]
  · intro s
    rw [rev_mid]
    rfl

theorem pow_four_eq_one_of_blocks [CharP F 2] {σ : F ≃+* F} {r : SU σ (k + 2)}
    (hrow : ∀ b, mat σ (k + 2) r 0 b = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b)
    (hcol : ∀ a, mat σ (k + 2) r a (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) a (Fin.last (k + 1)))
    (hmid : ∀ i j, mat σ (k + 2) r (mid i) (mid j) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) (mid i) (mid j)) :
    r ^ (2 ^ 2) = 1 := by
  set N := mat σ (k + 2) r - 1 with hN
  have hlev : N ^ 3 = 0 := by
    refine pow_three_eq_zero_of_level N
      (fun a => if (a : ℕ) = 0 then 0 else if (a : ℕ) = k + 1 then 2 else 1)
      (fun a => by split_ifs <;> omega) (fun a b hab => ?_)
    rw [hN, Matrix.sub_apply, sub_eq_zero]
    by_cases ha : (a : ℕ) = 0
    · rw [show a = 0 from Fin.ext ha]
      exact hrow b
    by_cases hb : (b : ℕ) = k + 1
    · rw [show b = Fin.last (k + 1) from Fin.ext hb]
      exact hcol a
    have ha1 : (a : ℕ) ≠ k + 1 := by
      intro h
      simp only [h, hb, ite_false, ite_true] at hab
      split_ifs at hab <;> omega
    have hb0 : (b : ℕ) ≠ 0 := by
      intro h
      simp only [ha, ha1, h, ite_false, ite_true] at hab
      omega
    obtain ⟨i, rfl⟩ : a ∈ Set.range (mid (m := k)) := by
      rw [mem_range_mid]
      have := a.isLt
      omega
    obtain ⟨j, rfl⟩ : b ∈ Set.range (mid (m := k)) := by
      rw [mem_range_mid]
      have := b.isLt
      omega
    exact hmid i j
  apply mat_injective
  rw [map_pow, map_one, show mat σ (k + 2) r = 1 + N by rw [hN]; abel]
  exact one_add_pow_four hlev

theorem mem_ggOTwoPrime_centralizer_of_corner_of_gen [CharP F 2] {σ : F ≃+* F}
    (hgen : (⊤ : Subgroup (SU σ k)) ≤ Subgroup.closure {x | ∃ j : ℕ, x ^ (2 ^ j) = 1})
    {M : SU σ (k + 2)}
    (hM : M ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))
    (h1 : mat σ (k + 2) M (Fin.last (k + 1)) (Fin.last (k + 1)) = 1) :
    M ∈ ggOTwoPrime (centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) := by
  have hT : mat σ (k + 2) (ggInvSU σ (k + 2) 1) = ggInvUMatrix (k + 2) 1 F := by
    rw [mat_apply]
    exact coe_ggInvSU (n := k + 2) (l := 1) σ (by omega)
  have hcommC : ∀ x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))),
      mat σ (k + 2) x * ggInvUMatrix (k + 2) 1 F = ggInvUMatrix (k + 2) 1 F * mat σ (k + 2) x := by
    intro x hx
    rw [← hT, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hx]
  have hιC : (iotaHom (σ := σ) (m := k)).range ≤
      centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) := by
    rintro _ ⟨B', rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply mat_injective
    rw [map_mul, map_mul, hT, mat_iotaHom]
    exact commute_of_isBlkOn (iotaMat_isBlkOn _)
  have hA := hcommC M hM
  have h00 : mat σ (k + 2) M 0 0 = 1 := by
    rw [← corner_eq_of_commute hA]
    exact h1
  have hcol : ∀ a, mat σ (k + 2) M a (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) a (Fin.last (k + 1)) := by
    intro a
    rw [col_last_of_commute hA, h00, Matrix.one_apply]
  have hrow : ∀ b, mat σ (k + 2) M 0 b = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b := by
    intro b
    rw [row_zero_of_commute hA, h1]
    by_cases hb : b = 0
    · rw [hb, ite_eq_left rfl, one_apply_eq]
    · rw [ite_eq_right hb, one_apply_ne (Ne.symm hb)]
  have hdet : ((mat σ (k + 2) M).submatrix mid mid).det = 1 := by
    rw [← det_eq_det_submatrix_mid hrow hcol]
    exact M.2.1
  have hBu : IsUnit ((mat σ (k + 2) M).submatrix mid mid).det := by
    rw [hdet]
    exact isUnit_one
  let Bsu : SU σ k := ⟨⟨(mat σ (k + 2) M).submatrix mid mid,
    ((mat σ (k + 2) M).submatrix mid mid)⁻¹, Matrix.mul_nonsing_inv _ hBu,
    Matrix.nonsing_inv_mul _ hBu⟩, hdet, isometry_submatrix_mid M hrow⟩
  have hmatB : mat σ k Bsu = (mat σ (k + 2) M).submatrix mid mid := rfl
  have hrC : (iotaHom Bsu)⁻¹ * M ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hιC ⟨Bsu, rfl⟩)) hM
  have hmr : mat σ (k + 2) ((iotaHom Bsu)⁻¹ * M) =
      iotaMat (mat σ k Bsu⁻¹) * mat σ (k + 2) M := by
    rw [map_mul, ← map_inv, mat_iotaHom]
  have hIB := iotaMat_isBlkOn (mat σ k Bsu⁻¹)
  have hrrow : ∀ b, mat σ (k + 2) ((iotaHom Bsu)⁻¹ * M) 0 b =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b := by
    intro b
    rw [hmr, Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [hIB 0 0 (Or.inl zero_not_mem_range_mid), one_apply_eq, one_mul, hrow]
    · intro c _ hc
      rw [hIB 0 c (Or.inl zero_not_mem_range_mid), one_apply_ne (Ne.symm hc), zero_mul]
    · simp
  have hrcol : ∀ a, mat σ (k + 2) ((iotaHom Bsu)⁻¹ * M) a (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) a (Fin.last (k + 1)) := by
    intro a
    rw [hmr, Matrix.mul_apply, Finset.sum_eq_single (Fin.last (k + 1))]
    · rw [hcol, one_apply_eq, mul_one, hIB a _ (Or.inr last_not_mem_range_mid)]
    · intro c _ hc
      rw [hcol, one_apply_ne hc, mul_zero]
    · simp
  have hrmid : ∀ i j, mat σ (k + 2) ((iotaHom Bsu)⁻¹ * M) (mid i) (mid j) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) (mid i) (mid j) := by
    intro i j
    have h := congrFun (congrFun (CFSG.LieType.Steinberg.submatrix_mul_of_isBlkOn mid_injective
      hIB (N := mat σ (k + 2) M)) i) j
    rw [Matrix.submatrix_apply, ← hmr, submatrix_iotaMat, ← hmatB, ← map_mul, inv_mul_cancel,
      map_one] at h
    rw [h]
    by_cases hij : i = j
    · subst hij
      rw [one_apply_eq, one_apply_eq]
    · rw [one_apply_ne hij, one_apply_ne (mid_injective.ne hij)]
  have hr4 := pow_four_eq_one_of_blocks hrrow hrcol hrmid
  have hMr : M = iotaHom Bsu * ((iotaHom Bsu)⁻¹ * M) := by
    rw [mul_inv_cancel_left]
  rw [hMr]
  exact mul_mem (range_le_ggOTwoPrime _ hιC hgen ⟨Bsu, rfl⟩)
    (Subgroup.subset_closure ⟨hrC, 2, hr4⟩)

theorem mem_ggOTwoPrime_centralizer_of_corner [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hk : 2 ≤ k) {M : SU (unitaryInvolution F 2 f) (k + 2)}
    (hM : M ∈ centralizer ({ggInvSU (unitaryInvolution F 2 f) (k + 2) 1} :
      Set (SU (unitaryInvolution F 2 f) (k + 2))))
    (h1 : mat (unitaryInvolution F 2 f) (k + 2) M (Fin.last (k + 1)) (Fin.last (k + 1)) = 1) :
    M ∈ ggOTwoPrime (centralizer ({ggInvSU (unitaryInvolution F 2 f) (k + 2) 1} :
      Set (SU (unitaryInvolution F 2 f) (k + 2)))) :=
  mem_ggOTwoPrime_centralizer_of_corner_of_gen (top_le_closure_SU hF hk) hM h1

end Decomposition

end RootCentSU

end CFSG.StandardType
