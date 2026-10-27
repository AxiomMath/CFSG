module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34TorusM
public import CFSG.Quasithin.Vol2.Ch9Sec3L34KGT
public import CFSG.Quasithin.Vol2.Ch9Sec3L34KG1
public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfB
public import CFSG.Quasithin.Vol2.Ch1EightFourInit

public section

namespace CFSG.Quasithin.H13.Ch9.L34T

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter

variable {k : Type} [Field k]

theorem apply_self_ne_zero {D : GL (Fin 3) k}
    (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular) (i : Fin 3) :
    (D : Matrix (Fin 3) (Fin 3) k) i i ≠ 0 := by
  intro h0
  have hdet := (GeneralLinearGroup.det D).ne_zero
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular hD] at hdet
  exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) h0)

theorem cube_apply_self {M : Matrix (Fin 3) (Fin 3) k} (hM : M.IsUpperTriangular) (i : Fin 3) :
    (M ^ 3) i i = M i i ^ 3 := by
  rw [pow_succ, pow_two, mul_apply_self_of_isUpperTriangular (hM.mul hM) hM,
    mul_apply_self_of_isUpperTriangular hM hM]
  ring

theorem eq_one_of_two_pow_of_three {G : Type*} [Group G] {x : G} {m : ℕ} (h2 : x ^ 2 ^ m = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.gcd (2 ^ m) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem exists_upper_of_mem (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {E : Subgroup (MulAut (projectiveSL 3 k))} (hE9 : Nat.card E = 9)
    (hEU : ∀ e ∈ E, (projUnitriangular 3 k).map (e : MulAut (projectiveSL 3 k)).toMonoidHom =
      projUnitriangular 3 k)
    {e : MulAut (projectiveSL 3 k)} (he : e ∈ E) :
    ∃ D : GL (Fin 3) k, (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular ∧
      e = LinearFlag.conjAut 3 k D ∧ e ^ 3 = 1 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have h9 : e ^ 9 = 1 := by
    have h := pow_card_eq_one' (G := ↥E) (x := ⟨e, he⟩)
    rw [hE9] at h
    simpa using congrArg Subtype.val h
  obtain ⟨D, rfl⟩ := exists_conjAut_of_pow hk hσ (by decide : Odd 9) h9
  have hD := isUpperTriangular_of_map_conjAut hk (hEU _ he)
  refine ⟨D, hD, rfl, ?_⟩
  have hD3 : ((D ^ 3 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular := by
    rw [Units.val_pow_eq_pow_val]
    exact hD.pow 3
  have hdiag : ∀ i, ((D ^ 3 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i = 1 := by
    intro i
    rw [Units.val_pow_eq_pow_val, cube_apply_self hD]
    exact LinearFieldFour.pow_three_eq_one hk (apply_self_ne_zero hD i)
  obtain ⟨m, hm⟩ := exists_pow_conjAut_eq_one hD3 (by rw [hdiag, hdiag]) (by rw [hdiag, hdiag])
  rw [map_pow] at hm
  refine eq_one_of_two_pow_of_three hm ?_
  rw [← pow_mul]
  exact h9

theorem eq_one_of_mem_of_diag (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {E : Subgroup (MulAut (projectiveSL 3 k))} (hE9 : Nat.card E = 9)
    (hEU : ∀ e ∈ E, (projUnitriangular 3 k).map (e : MulAut (projectiveSL 3 k)).toMonoidHom =
      projUnitriangular 3 k)
    {D : GL (Fin 3) k} (hDE : LinearFlag.conjAut 3 k D ∈ E)
    (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular)
    (h0 : (D : Matrix (Fin 3) (Fin 3) k) 0 0 = (D : Matrix (Fin 3) (Fin 3) k) 2 2)
    (h1 : (D : Matrix (Fin 3) (Fin 3) k) 1 1 = (D : Matrix (Fin 3) (Fin 3) k) 2 2) :
    LinearFlag.conjAut 3 k D = 1 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨-, -, -, h3⟩ := exists_upper_of_mem hk hσ hE9 hEU hDE
  obtain ⟨m, hm⟩ := exists_pow_conjAut_eq_one hD h0 h1
  exact eq_one_of_two_pow_of_three hm h3

theorem exists_mem_diag_eq (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {E : Subgroup (MulAut (projectiveSL 3 k))} (hE9 : Nat.card E = 9)
    (hEU : ∀ e ∈ E, (projUnitriangular 3 k).map (e : MulAut (projectiveSL 3 k)).toMonoidHom =
      projUnitriangular 3 k) :
    ∃ D : GL (Fin 3) k, (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular ∧
      LinearFlag.conjAut 3 k D ∈ E ∧
      (D : Matrix (Fin 3) (Fin 3) k) 1 1 = (D : Matrix (Fin 3) (Fin 3) k) 2 2 ∧
      (D : Matrix (Fin 3) (Fin 3) k) 0 0 ≠ (D : Matrix (Fin 3) (Fin 3) k) 1 1 := by
  classical
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hex : ∀ x : ↥E, ∃ D : GL (Fin 3) k, (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular ∧
      (x : MulAut (projectiveSL 3 k)) = LinearFlag.conjAut 3 k D := fun x => by
    obtain ⟨D, hD, he, -⟩ := exists_upper_of_mem hk hσ hE9 hEU x.2
    exact ⟨D, hD, he⟩
  choose Df hDf hxDf using hex
  set f : ↥E → k := fun x => (Df x : Matrix (Fin 3) (Fin 3) k) 1 1 *
    ((Df x : Matrix (Fin 3) (Fin 3) k) 2 2)⁻¹ with hf
  have hnot : ¬ Function.Injective f := fun hinj => by
    have := Nat.card_le_card_of_injective f hinj
    rw [hE9, hk] at this
    omega
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnot
  set D := (Df x)⁻¹ * Df y with hDdef
  have hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular := by
    rw [hDdef, Units.val_mul]
    exact (isUpperTriangular_inv (hDf x)).mul (hDf y)
  have hdiag : ∀ i, (D : Matrix (Fin 3) (Fin 3) k) i i =
      ((Df x : Matrix (Fin 3) (Fin 3) k) i i)⁻¹ * (Df y : Matrix (Fin 3) (Fin 3) k) i i := by
    intro i
    rw [hDdef, Units.val_mul, mul_apply_self_of_isUpperTriangular (isUpperTriangular_inv (hDf x))
      (hDf y), inv_apply_self_of_upper (hDf x)]
  have hDE : LinearFlag.conjAut 3 k D ∈ E := by
    rw [hDdef, map_mul, map_inv, ← hxDf x, ← hxDf y]
    exact E.mul_mem (E.inv_mem x.2) y.2
  have hx1 := apply_self_ne_zero (hDf x) 1
  have hx2 := apply_self_ne_zero (hDf x) 2
  have hy1 := apply_self_ne_zero (hDf y) 1
  have hy2 := apply_self_ne_zero (hDf y) 2
  have h12 : (D : Matrix (Fin 3) (Fin 3) k) 1 1 = (D : Matrix (Fin 3) (Fin 3) k) 2 2 := by
    rw [hdiag, hdiag]
    simp only [hf] at hxy
    field_simp at hxy ⊢
    linear_combination -hxy
  refine ⟨D, hD, hDE, h12, fun h01 => hne ?_⟩
  have h1 := eq_one_of_mem_of_diag hk hσ hE9 hEU hDE hD (h01.trans h12) h12
  rw [hDdef, map_mul, map_inv, ← hxDf x, ← hxDf y, inv_mul_eq_one] at h1
  exact Subtype.ext h1

theorem eq_mul_scalar_of_conjAut_eq [Finite k] {X Y : GL (Fin 3) k}
    (h : LinearFlag.conjAut 3 k X = LinearFlag.conjAut 3 k Y) :
    ∃ c : kˣ, X = Y * GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := k) (n := 3) le_rfl (Y⁻¹ * X) 1
    (by rw [map_one, mul_one, map_mul, map_inv, h, inv_mul_cancel])
  exact ⟨c, by rw [hc, mul_inv_cancel_left]⟩

theorem mul_scalar_apply_self (Y : GL (Fin 3) k) (c : kˣ) (i : Fin 3) :
    ((Y * GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i =
      (Y : Matrix (Fin 3) (Fin 3) k) i i * c := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal]

theorem torus_a (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {E : Subgroup (MulAut (projectiveSL 3 k))} (hE9 : Nat.card E = 9)
    (hEU : ∀ e ∈ E, (projUnitriangular 3 k).map (e : MulAut (projectiveSL 3 k)).toMonoidHom =
      projUnitriangular 3 k)
    {α : MulAut (projectiveSL 3 k)}
    (hαU : (projUnitriangular 3 k).map α.toMonoidHom = projUnitriangular 3 k)
    (hunif : (∀ e ∈ E, α * e * α⁻¹ = e) ∨ (∀ e ∈ E, α * e * α⁻¹ = e⁻¹)) (i : Fin 2) :
    (FieldFourCover.projRad k i).map α.toMonoidHom = FieldFourCover.projRad k i := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨⟨A, a, b⟩, rfl⟩ := exists_nf hσ hk α
  rcases zmod_two_cases b with rfl | rfl
  · exact map_projRad_of_nf hk hαU i
  · exfalso
    have hA := isUpperTriangular_of_map_nf_one hk hσ hαU
    obtain ⟨D, hD, hDE, h12, h01⟩ := exists_mem_diag_eq hk hσ hE9 hEU
    have hconj := conj_nf_one hk hσ A D a
    obtain ⟨-, hXd⟩ := conj_twist_diag σ a hA hD
    have key : ∀ Y : GL (Fin 3) k, (Y : Matrix (Fin 3) (Fin 3) k) 1 1 =
        (Y : Matrix (Fin 3) (Fin 3) k) 2 2 →
        LinearFlag.conjAut 3 k (A * twistF σ a (twistD 1 D) * A⁻¹) = LinearFlag.conjAut 3 k Y →
          False := by
      intro Y hY hXY
      obtain ⟨c, hc⟩ := eq_mul_scalar_of_conjAut_eq hXY
      have h1 : ((A * twistF σ a (twistD 1 D) * A⁻¹ : GL (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) 1 1 =
          ((A * twistF σ a (twistD 1 D) * A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2 := by
        rw [hc, mul_scalar_apply_self, mul_scalar_apply_self, hY]
      rw [hXd 1, hXd 2] at h1
      have r1 : Fin.rev (1 : Fin 3) = 1 := rfl
      have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
      rw [r1, r2] at h1
      exact h01 (inv_inj.mp ((σ ^ a.val).injective h1)).symm
    rcases hunif with h | h
    · exact key D h12 (by rw [← hconj]; exact h _ hDE)
    · refine key D⁻¹ ?_ (by rw [← hconj, map_inv]; exact h _ hDE)
      rw [inv_apply_self_of_upper hD, inv_apply_self_of_upper hD, h12]

theorem cube_roots_cases {x y z : k} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxy : x ≠ y) (hyz : y ≠ z) : x * z = y ^ 2 ∨ x = z := by
  by_cases hxz : x = z
  · exact Or.inr hxz
  left
  have e1 : x ^ 2 + x * y + y ^ 2 = 0 := by
    have h : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by linear_combination hx - hy
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hxy)
  have e3 : x ^ 2 + x * z + z ^ 2 = 0 := by
    have h : (x - z) * (x ^ 2 + x * z + z ^ 2) = 0 := by linear_combination hx - hz
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hxz)
  have e2 : y ^ 2 + y * z + z ^ 2 = 0 := by
    have h : (y - z) * (y ^ 2 + y * z + z ^ 2) = 0 := by linear_combination hy - hz
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hyz)
  have hs : x + y + z = 0 := by
    have h : (y - z) * (x + y + z) = 0 := by linear_combination e1 - e3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hyz)
  have hxyz : x * y * z = 1 := by
    have h2 : x ^ 2 = y * z := by linear_combination e1 - y * hs
    linear_combination -x * h2 + hx
  linear_combination (-x * z) * hy + y ^ 2 * hxyz

theorem pow_apply_self {M : Matrix (Fin 3) (Fin 3) k} (hM : M.IsUpperTriangular) (n : ℕ)
    (i : Fin 3) : (M ^ n) i i = M i i ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_apply_self_of_isUpperTriangular (hM.pow n) hM, ih, pow_succ]

theorem ringEquiv_one_apply (t : k) : (1 : k ≃+* k) t = t := rfl

theorem inv_eq_sq_of_cube {t : k} (h : t ^ 3 = 1) : t⁻¹ = t ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h)

theorem sq_inv_eq_of_cube {t : k} (h : t ^ 3 = 1) : (t ^ 2)⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact h)

theorem exists_pow_diag_const (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    (a : ZMod 2) {D X : GL (Fin 3) k} (hD : (D : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular)
    (hX : (X : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular)
    (hXd : ∀ i, (X : Matrix (Fin 3) (Fin 3) k) i i =
      (σ ^ a.val) (((D : Matrix (Fin 3) (Fin 3) k) (Fin.rev i) (Fin.rev i))⁻¹))
    (hxy : (D : Matrix (Fin 3) (Fin 3) k) 0 0 ≠ (D : Matrix (Fin 3) (Fin 3) k) 1 1)
    (hyz : (D : Matrix (Fin 3) (Fin 3) k) 1 1 ≠ (D : Matrix (Fin 3) (Fin 3) k) 2 2) :
    ∃ n : ℕ, ∀ i, (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i =
      (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2 := by
  have hDn : ∀ n : ℕ, ((D ^ n : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular :=
    fun n => by rw [Units.val_pow_eq_pow_val]; exact hD.pow n
  have hdiag : ∀ (n : ℕ) (i : Fin 3), (((D ^ n)⁻¹ * X : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) i i = (((D : Matrix (Fin 3) (Fin 3) k) i i) ^ n)⁻¹ *
        (σ ^ a.val) (((D : Matrix (Fin 3) (Fin 3) k) (Fin.rev i) (Fin.rev i))⁻¹) := by
    intro n i
    rw [Units.val_mul, mul_apply_self_of_isUpperTriangular (isUpperTriangular_inv (hDn n)) hX,
      inv_apply_self_of_upper (hDn n), hXd, Units.val_pow_eq_pow_val, pow_apply_self hD]
  have hc : ∀ i, (D : Matrix (Fin 3) (Fin 3) k) i i ^ 3 = 1 := fun i =>
    LinearFieldFour.pow_three_eq_one hk (apply_self_ne_zero hD i)
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r1 : Fin.rev (1 : Fin 3) = 1 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  have hσinv : ∀ t : k, t ^ 3 = 1 → σ t⁻¹ = t := by
    intro t h3
    rw [hσ, inv_pow]
    exact sq_inv_eq_of_cube h3
  have hx3 := hc 0
  have hy3 := hc 1
  have hz3 := hc 2
  set x := (D : Matrix (Fin 3) (Fin 3) k) 0 0 with hxdef
  set y := (D : Matrix (Fin 3) (Fin 3) k) 1 1 with hydef
  set z := (D : Matrix (Fin 3) (Fin 3) k) 2 2 with hzdef
  have h0 : ∀ n, (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 0 =
      (x ^ n)⁻¹ * (σ ^ a.val) z⁻¹ := fun n => by rw [hdiag, r0]
  have h1 : ∀ n, (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 1 1 =
      (y ^ n)⁻¹ * (σ ^ a.val) y⁻¹ := fun n => by rw [hdiag, r1]
  have h2 : ∀ n, (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2 =
      (z ^ n)⁻¹ * (σ ^ a.val) x⁻¹ := fun n => by rw [hdiag, r2]
  have fin : ∀ n, (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 0 =
      (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2 →
      (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 1 1 =
      (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2 →
      ∀ i, (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i =
        (((D ^ n)⁻¹ * X : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2 := by
    intro n e0 e1 i
    fin_cases i
    · exact e0
    · exact e1
    · rfl
  rcases cube_roots_cases hx3 hy3 hz3 hxy hyz with h | h <;>
    rcases zmod_two_cases a with rfl | rfl
  · refine ⟨1, fin 1 ?_ ?_⟩
    · rw [h0, h2]
      simp only [ZMod.val_zero, pow_zero, ringEquiv_one_apply, pow_one]
      ring
    · rw [h1, h2]
      simp only [ZMod.val_zero, pow_zero, ringEquiv_one_apply, pow_one]
      rw [inv_eq_sq_of_cube hx3, inv_eq_sq_of_cube hy3, inv_eq_sq_of_cube hz3]
      linear_combination -(x * z + y ^ 2) * h
  · refine ⟨2, fin 2 ?_ ?_⟩
    · rw [h0, h2]
      simp only [val_one_two, pow_one, hσinv _ hx3, hσinv _ hz3, sq_inv_eq_of_cube hx3,
        sq_inv_eq_of_cube hz3]
      ring
    · rw [h1, h2]
      simp only [val_one_two, pow_one, hσinv _ hx3, hσinv _ hy3, sq_inv_eq_of_cube hy3,
        sq_inv_eq_of_cube hz3]
      linear_combination -h
  · refine ⟨2, fin 2 ?_ ?_⟩
    · rw [h0, h2, ← h]
    · rw [h1, h2, ← h]
      simp only [ZMod.val_zero, pow_zero, ringEquiv_one_apply]
      rw [sq_inv_eq_of_cube hy3, sq_inv_eq_of_cube hx3, inv_eq_sq_of_cube hy3,
        inv_eq_sq_of_cube hx3]
      linear_combination hy3 - hx3
  · refine ⟨1, fin 1 ?_ ?_⟩
    · rw [h0, h2, ← h]
    · rw [h1, h2, ← h]
      simp only [val_one_two, pow_one]
      rw [hσinv _ hx3, hσinv _ hy3, inv_eq_sq_of_cube hx3, inv_eq_sq_of_cube hy3]
      linear_combination hy3 - hx3

theorem torus_b (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {E : Subgroup (MulAut (projectiveSL 3 k))} (hE9 : Nat.card E = 9)
    (hEU : ∀ e ∈ E, (projUnitriangular 3 k).map (e : MulAut (projectiveSL 3 k)).toMonoidHom =
      projUnitriangular 3 k)
    {g : MulAut (projectiveSL 3 k)}
    (hgU : (projUnitriangular 3 k).map g.toMonoidHom = projUnitriangular 3 k)
    (hgE : ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hmove : ∃ i : Fin 2, (FieldFourCover.projRad k i).map g.toMonoidHom ≠
      FieldFourCover.projRad k i)
    {τ : Subgroup (MulAut (projectiveSL 3 k))} (hτE : τ ≤ E) (hτ3 : Nat.card τ = 3)
    (hτg : τ.map (MulAut.conj g).toMonoidHom ≠ τ) :
    (∀ y ∈ Subgroup.normalizer (FieldFourCover.projRad k 0 : Set (projectiveSL 3 k)),
        ∀ e ∈ τ, (e : MulAut (projectiveSL 3 k)) y * y⁻¹ ∈ FieldFourCover.projRad k 0) ∨
      (∀ y ∈ Subgroup.normalizer (FieldFourCover.projRad k 1 : Set (projectiveSL 3 k)),
        ∀ e ∈ τ, (e : MulAut (projectiveSL 3 k)) y * y⁻¹ ∈ FieldFourCover.projRad k 1) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨A, a, b⟩, rfl⟩ := exists_nf hσ hk g
  rcases zmod_two_cases b with rfl | rfl
  · exfalso
    obtain ⟨i, hi⟩ := hmove
    exact hi (map_projRad_of_nf hk hgU i)
  have hA := isUpperTriangular_of_map_nf_one hk hσ hgU
  obtain ⟨e₀, he₀τ, he₀1⟩ : ∃ e₀ ∈ τ, e₀ ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : τ = ⊥ := (Subgroup.eq_bot_iff_forall τ).mpr h
    rw [hbot, Subgroup.card_bot] at hτ3
    norm_num at hτ3
  obtain ⟨D, hD, rfl, h3⟩ := exists_upper_of_mem hk hσ hE9 hEU (hτE he₀τ)
  have hord : orderOf (LinearFlag.conjAut 3 k D) = 3 := orderOf_eq_prime h3 he₀1
  have hτeq : τ = Subgroup.zpowers (LinearFlag.conjAut 3 k D) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he₀τ) ?_).symm
    rw [Nat.card_zpowers, hord, hτ3]
  have hfin : IsOfFinOrder (LinearFlag.conjAut 3 k D) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, h3⟩
  have hpow : ∀ e ∈ τ, ∃ n : ℕ, e = LinearFlag.conjAut 3 k (D ^ n) := by
    intro e he
    rw [hτeq] at he
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr he)
    exact ⟨n, (map_pow _ _ _).symm⟩
  have hDn : ∀ n : ℕ, ((D ^ n : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).IsUpperTriangular :=
    fun n => by rw [Units.val_pow_eq_pow_val]; exact hD.pow n
  have h3n : ∀ n : ℕ, LinearFlag.conjAut 3 k (D ^ n) ^ 3 = 1 := fun n => by
    rw [map_pow, ← pow_mul, mul_comm, pow_mul, h3, one_pow]
  by_cases hyz : (D : Matrix (Fin 3) (Fin 3) k) 1 1 = (D : Matrix (Fin 3) (Fin 3) k) 2 2
  · left
    intro w hw e he
    obtain ⟨n, rfl⟩ := hpow e he
    have h11 : ((D ^ n : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 1 1 =
        ((D ^ n : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2 := by
      rw [Units.val_pow_eq_pow_val, pow_apply_self hD, pow_apply_self hD, hyz]
    exact conjAut_mul_inv_mem_projRad_zero hk (hDn n) h11
      (apply_one_two_eq_zero (hDn n) h11 (h3n n)) hw
  by_cases hxy : (D : Matrix (Fin 3) (Fin 3) k) 0 0 = (D : Matrix (Fin 3) (Fin 3) k) 1 1
  · right
    intro w hw e he
    obtain ⟨n, rfl⟩ := hpow e he
    have h00 : ((D ^ n : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 0 =
        ((D ^ n : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 1 1 := by
      rw [Units.val_pow_eq_pow_val, pow_apply_self hD, pow_apply_self hD, hxy]
    exact conjAut_mul_inv_mem_projRad_one hk (hDn n) h00
      (apply_zero_one_eq_zero (hDn n) h00 (h3n n)) hw
  exfalso
  apply hτg
  have hconj := conj_nf_one hk hσ A D a
  obtain ⟨hXU, hXd⟩ := conj_twist_diag σ a hA hD
  obtain ⟨n, hn⟩ := exists_pow_diag_const hk hσ a hD hXU hXd hxy hyz
  have hgE0 := hgE _ (hτE he₀τ)
  have hmem : LinearFlag.conjAut 3 k ((D ^ n)⁻¹ * (A * twistF σ a (twistD 1 D) * A⁻¹)) ∈ E := by
    rw [map_mul, map_inv, ← hconj]
    exact E.mul_mem (E.inv_mem (by rw [map_pow]; exact E.pow_mem (hτE he₀τ) n)) hgE0
  have h1 := eq_one_of_mem_of_diag hk hσ hE9 hEU hmem
    ((isUpperTriangular_inv (hDn n)).mul hXU) (hn 0) (hn 1)
  rw [map_mul, map_inv, inv_mul_eq_one, ← hconj] at h1
  refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨m, rfl⟩ := hpow e he
  show nf σ A a 1 * LinearFlag.conjAut 3 k (D ^ m) * (nf σ A a 1)⁻¹ ∈ τ
  rw [map_pow, ← conj_pow, ← h1, hτeq, map_pow, ← pow_mul]
  exact Subgroup.npow_mem_zpowers _ _

theorem map_map_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X)
    (S : Subgroup X) :
    (S.map α.toMonoidHom).map e.toMonoidHom =
      (S.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  show e (α x) = e (α (e.symm (e x)))
  rw [e.symm_apply_apply]

theorem transport_cent {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {R : Subgroup X}
    {τ : Subgroup (MulAut X)}
    (h : ∀ y' ∈ Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup Y) : Set Y),
      ∀ e' ∈ τ.map (MulAut.congr e).toMonoidHom,
        (e' : MulAut Y) y' * y'⁻¹ ∈ R.map e.toMonoidHom) :
    ∀ y ∈ Subgroup.normalizer (R : Set X), ∀ ε ∈ τ, (ε : MulAut X) y * y⁻¹ ∈ R := by
  intro y hy ε hε
  have hy' : e y ∈ Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup Y) : Set Y) := by
    rw [← Subgroup.map_equiv_normalizer_eq R e]
    exact ⟨y, hy, rfl⟩
  have h1 := h (e y) hy' (MulAut.congr e ε) ⟨ε, hε, rfl⟩
  have e1 : (MulAut.congr e ε) (e y) * (e y)⁻¹ = e (ε y * y⁻¹) := by
    show e (ε (e.symm (e y))) * (e y)⁻¹ = _
    rw [e.symm_apply_apply, map_mul, map_inv]
  rw [e1] at h1
  obtain ⟨z, hz, hze⟩ := h1
  rwa [← e.injective hze]

theorem factL34Torus_holds : FactL34Torus := by
  intro X _ _ hX S₀ hS₀2 hS₀64 E hE9 hES
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card X = 20160 := Ch1Four.card_of_isPSL_three_four hX
  have hS₀syl : QuasithinUnique.IsSylowTwoOf S₀ ⊤ := by
    refine ⟨le_top, hS₀2, ?_⟩
    show ¬ 2 ∣ S₀.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := S₀.card_mul_index
    rw [hS₀64, hcard] at h
    have h315 : S₀.index = 315 := by omega
    rw [h315]
    decide
  obtain ⟨k, _, hk, e, he⟩ := H13.exists_mulEquiv_sylow_eq (L34.lieModel_of_isPSL hX) hS₀syl
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  set Φ := MulAut.congr e with hΦ
  set E' := E.map Φ.toMonoidHom with hE'
  have hE'9 : Nat.card E' = 9 := by rw [hE', Subgroup.card_map_of_injective Φ.injective, hE9]
  have hU : ∀ β : MulAut X, S₀.map β.toMonoidHom = S₀ →
      (projUnitriangular 3 k).map (Φ β).toMonoidHom = projUnitriangular 3 k := by
    intro β hβ
    rw [← he, ← map_map_congr, hβ]
  have hE'U : ∀ e' ∈ E', (projUnitriangular 3 k).map (e' : MulAut (projectiveSL 3 k)).toMonoidHom =
      projUnitriangular 3 k := by
    rintro _ ⟨ε, hε, rfl⟩
    exact hU ε (hES ε hε)
  have hrad : ∀ R : Subgroup X, R ≤ S₀ → CFSG.Open.IsElemAbelian 2 R → Nat.card R = 16 →
      R.map e.toMonoidHom = FieldFourCover.projRad k 0 ∨
        R.map e.toMonoidHom = FieldFourCover.projRad k 1 := by
    intro R hRS hRE hR16
    refine L34Br.eq_projRad_of_card hk ?_ (CFSG.SectionRank.isElemAbelian_map hRE _) ?_
    · rw [← he]
      exact Subgroup.map_mono hRS
    · rw [Subgroup.card_map_of_injective e.injective, hR16]
  have hback : ∀ (β : MulAut X) (R : Subgroup X),
      (R.map e.toMonoidHom).map (Φ β).toMonoidHom = R.map e.toMonoidHom →
        R.map β.toMonoidHom = R := by
    intro β R h
    rw [← map_map_congr] at h
    exact Subgroup.map_injective e.injective h
  refine ⟨fun α hαS hαE hunif R hRS hRE hR16 => ?_,
    fun g hgS hgE R hRS hRE hR16 hRg τ hτE hτ3 hτg => ?_⟩
  ·
    apply hback α R
    have hunif' : (∀ e' ∈ E', Φ α * e' * (Φ α)⁻¹ = e') ∨
        (∀ e' ∈ E', Φ α * e' * (Φ α)⁻¹ = e'⁻¹) := by
      rcases hunif with h | h
      · left
        rintro _ ⟨ε, hε, rfl⟩
        show Φ α * Φ ε * (Φ α)⁻¹ = Φ ε
        rw [← map_inv, ← map_mul, ← map_mul, h ε hε]
      · right
        rintro _ ⟨ε, hε, rfl⟩
        show Φ α * Φ ε * (Φ α)⁻¹ = (Φ ε)⁻¹
        rw [← map_inv, ← map_mul, ← map_mul, h ε hε, map_inv]
    rcases hrad R hRS hRE hR16 with h | h <;> rw [h] <;>
      exact torus_a hk hσ hE'9 hE'U (hU α hαS) hunif' _
  ·
    set g' := Φ g with hg'
    have hgE' : ∀ e' ∈ E', g' * e' * g'⁻¹ ∈ E' := by
      rintro _ ⟨ε, hε, rfl⟩
      refine ⟨g * ε * g⁻¹, hgE ε hε, ?_⟩
      show Φ (g * ε * g⁻¹) = _
      rw [map_mul, map_mul, map_inv]
      rfl
    have hRg' : (R.map e.toMonoidHom).map g'.toMonoidHom ≠ R.map e.toMonoidHom := fun h =>
      hRg (hback g R h)
    have hmove : ∃ i : Fin 2, (FieldFourCover.projRad k i).map g'.toMonoidHom ≠
        FieldFourCover.projRad k i := by
      rcases hrad R hRS hRE hR16 with h | h
      · exact ⟨0, by rw [← h]; exact hRg'⟩
      · exact ⟨1, by rw [← h]; exact hRg'⟩
    have hτ'3 : Nat.card (τ.map Φ.toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective Φ.injective, hτ3]
    have hτ'g : (τ.map Φ.toMonoidHom).map (MulAut.conj g').toMonoidHom ≠ τ.map Φ.toMonoidHom := by
      intro h
      apply hτg
      apply Subgroup.map_injective (f := Φ.toMonoidHom) Φ.injective
      rw [← h, Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext ε x
      show Φ (g * ε * g⁻¹) x = (g' * Φ ε * g'⁻¹) x
      rw [map_mul, map_mul, map_inv]
    have hRgS : R.map g.toMonoidHom ≤ S₀ := by
      rw [← hgS]
      exact Subgroup.map_mono hRS
    have hRgE : CFSG.Open.IsElemAbelian 2 (R.map g.toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map hRE _
    have hRg16 : Nat.card (R.map g.toMonoidHom) = 16 := by
      rw [Subgroup.card_map_of_injective g.injective, hR16]
    have hRgeq : (R.map g.toMonoidHom).map e.toMonoidHom =
        (R.map e.toMonoidHom).map g'.toMonoidHom := map_map_congr e g R
    rcases torus_b hk hσ hE'9 hE'U (hU g hgS) hgE' hmove (Subgroup.map_mono hτE) hτ'3 hτ'g with
      hC | hC
    · rcases hrad R hRS hRE hR16 with h | h
      · left
        exact transport_cent e (by rw [h]; exact hC)
      · right
        rcases hrad (R.map g.toMonoidHom) hRgS hRgE hRg16 with h' | h'
        · exact transport_cent e (by rw [h']; exact hC)
        · exfalso
          rw [hRgeq, h] at h'
          exact hRg' (by rw [h, h'])
    · rcases hrad R hRS hRE hR16 with h | h
      · right
        rcases hrad (R.map g.toMonoidHom) hRgS hRgE hRg16 with h' | h'
        · exfalso
          rw [hRgeq, h] at h'
          exact hRg' (by rw [h, h'])
        · exact transport_cent e (by rw [h']; exact hC)
      · left
        exact transport_cent e (by rw [h]; exact hC)

end CFSG.Quasithin.H13.Ch9.L34T
