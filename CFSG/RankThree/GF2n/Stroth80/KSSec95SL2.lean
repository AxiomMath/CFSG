module

public import CFSG.RankThree.GF2n.Stroth80.KSSec95Eig

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Matrix

namespace KS95

variable {K : Type} [Field K]

private def upper (a : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, a; 0, 1], by simp [det_fin_two_of]⟩

private def lower (b : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; b, 1], by simp [det_fin_two_of]⟩

private def weyl (t : K) : SpecialLinearGroup (Fin 2) K := upper t * lower t⁻¹ * upper t

@[simp] private theorem coe_upper (a : K) :
    ((upper a : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, a; 0, 1] := rfl

@[simp] private theorem coe_lower (b : K) :
    ((lower b : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; b, 1] := rfl

private theorem upper_add (a b : K) : upper (a + b) = upper a * upper b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem lower_add (a b : K) : lower (a + b) = lower a * lower b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem upper_zero : upper (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem lower_zero : lower (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem coe_weyl [CharP K 2] {t : K} (ht : t ≠ 0) :
    ((weyl t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, t; t⁻¹, 0] := by
  have h1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have h2 : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  have h3 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3]

private theorem weyl_mul_self [CharP K 2] {t : K} (ht : t ≠ 0) : weyl t * weyl t = 1 := by
  have h1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have h2 : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weyl ht, Matrix.mul_apply, Fin.sum_univ_two, h1, h2]

private theorem weyl_lower [CharP K 2] {t : K} (ht : t ≠ 0) (b : K) :
    weyl t * lower b * weyl t = upper (t ^ 2 * b) := by
  have h1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have h2 : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weyl ht, Matrix.mul_apply, Fin.sum_univ_two, h1, h2] <;> ring

private theorem weyl_upper [CharP K 2] {t : K} (ht : t ≠ 0) (a : K) :
    weyl t * upper a * weyl t = lower (t⁻¹ ^ 2 * a) := by
  have h1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have h2 : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weyl ht, Matrix.mul_apply, Fin.sum_univ_two, h1, h2] <;> ring

private theorem eq_upper (g : SpecialLinearGroup (Fin 2) K)
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1) (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1)
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    g = upper ((g : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h10]

private theorem eq_lower (g : SpecialLinearGroup (Fin 2) K)
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1) (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1)
    (h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) :
    g = lower ((g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01]

private theorem eq_upper_lower_upper (g : SpecialLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    g = upper (((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      lower ((g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      upper (((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hdet := g.det_coe
  rw [det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first
    | ring1
    | linear_combination -hdet
    | linear_combination (-2 : K) * hdet
    | linear_combination hdet
    | linear_combination (2 : K) * hdet

variable {Mm : Type} [AddCommGroup Mm] [Module K Mm]

private theorem rho_mul (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm))
    (g h : SpecialLinearGroup (Fin 2) K) (m : Mm) : ρ (g * h) m = ρ g (ρ h m) := by
  rw [map_mul]
  rfl

private theorem rho_one (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm)) (m : Mm) :
    ρ 1 m = m := by
  rw [map_one]
  rfl

private theorem fixed_of_upper_lower [CharP K 2]
    (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm)) {v : Mm}
    (hu : ∀ a, ρ (upper a) v = v) (hl : ∀ b, ρ (lower b) v = v)
    (g : SpecialLinearGroup (Fin 2) K) : ρ g v = v := by
  have key : ∀ g : SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 →
      ρ g v = v := fun g hg => by
    rw [eq_upper_lower_upper g hg, rho_mul, rho_mul, hu, hl, hu]
  by_cases h : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      intro h0
      have hdet := g.det_coe
      rw [det_fin_two, h0, h] at hdet
      simp at hdet
    have e : g = lower 1 * (lower 1 * g) := by
      rw [← mul_assoc, ← lower_add, CharTwo.add_self_eq_zero, lower_zero, one_mul]
    rw [e, rho_mul, key _ (by simp [Matrix.mul_apply, Fin.sum_univ_two, h, h00]), hl]
  · exact key g h

private def opE (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm)) (a : K) : Module.End K Mm :=
  (ρ (upper a)).toLinearMap - LinearMap.id

private def opF (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm)) (b : K) : Module.End K Mm :=
  (ρ (lower b)).toLinearMap - LinearMap.id

private def kap (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm)) (a : K) : Module.End K Mm :=
  opF ρ 1 * opE ρ a

private theorem opE_apply (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm)) (a : K) (m : Mm) :
    opE ρ a m = ρ (upper a) m - m := rfl

private theorem opF_apply (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm)) (b : K) (m : Mm) :
    opF ρ b m = ρ (lower b) m - m := rfl

private theorem kap_apply (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm)) (a : K) (m : Mm) :
    kap ρ a m = opF ρ 1 (opE ρ a m) := rfl

private theorem add_self' [CharP K 2] (m : Mm) : m + m = 0 := by
  rw [← two_smul K m, CharTwo.two_eq_zero, zero_smul]

private theorem neg' [CharP K 2] (m : Mm) : -m = m :=
  neg_eq_of_add_eq_zero_right (add_self' (K := K) m)

private theorem sub_eq_add' [CharP K 2] (m n : Mm) : m - n = m + n := by
  rw [sub_eq_add_neg, neg' (K := K)]

private structure Setup (ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm))
    (X X' : Submodule K Mm) : Prop where
  compl : IsCompl X X'
  up_mem : ∀ a m, ρ (upper a) m - m ∈ X
  up_fix : ∀ a, ∀ x ∈ X, ρ (upper a) x = x
  lo_mem : ∀ b m, ρ (lower b) m - m ∈ X'
  lo_fix : ∀ b, ∀ y ∈ X', ρ (lower b) y = y
  cent_up : ∀ m, (∀ a, ρ (upper a) m = m) → m ∈ X
  cent_lo : ∀ m, (∀ b, ρ (lower b) m = m) → m ∈ X'

variable [CharP K 2] {ρ : SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm)} {X X' : Submodule K Mm}

private theorem Setup.eq_zero (S : Setup ρ X X') {x : Mm} (hx : x ∈ X) (hx' : x ∈ X') : x = 0 :=
  (Submodule.disjoint_def.1 S.compl.disjoint) x hx hx'

private theorem Setup.opE_mem (S : Setup ρ X X') (a : K) (m : Mm) : opE ρ a m ∈ X := S.up_mem a m

private theorem Setup.opF_mem (S : Setup ρ X X') (b : K) (m : Mm) : opF ρ b m ∈ X' := S.lo_mem b m

private theorem Setup.up_apply (S : Setup ρ X X')
    (a : K) (m : Mm) : ρ (upper a) m = m + opE ρ a m := by
  rw [opE_apply, add_sub_cancel]

private theorem Setup.lo_apply (S : Setup ρ X X')
    (b : K) (m : Mm) : ρ (lower b) m = m + opF ρ b m := by
  rw [opF_apply, add_sub_cancel]

private theorem Setup.opE_add (S : Setup ρ X X')
    (a b : K) (m : Mm) : opE ρ (a + b) m = opE ρ a m + opE ρ b m := by
  rw [opE_apply, upper_add, rho_mul, S.up_apply b m, map_add, S.up_fix a _ (S.opE_mem b m),
    S.up_apply a m]
  abel

private theorem Setup.opE_zero (S : Setup ρ X X') (m : Mm) : opE ρ 0 m = 0 := by
  rw [opE_apply, upper_zero, rho_one, sub_self]

private theorem Setup.weyl_apply (S : Setup ρ X X') (t : K) (m : Mm) :
    ρ (weyl t) m = ρ (upper t) (ρ (lower t⁻¹) (ρ (upper t) m)) := by
  rw [weyl, rho_mul, rho_mul]

private theorem Setup.weyl_weyl (S : Setup ρ X X')
    {t : K} (ht : t ≠ 0) (m : Mm) : ρ (weyl t) (ρ (weyl t) m) = m := by
  rw [← rho_mul, weyl_mul_self ht, rho_one]

private theorem Setup.weyl_mem_X (S : Setup ρ X X')
    {t : K} (ht : t ≠ 0) {y : Mm} (hy : y ∈ X') : ρ (weyl t) y ∈ X := by
  refine S.cent_up _ fun a => ?_
  have e : upper a = weyl t * lower (t⁻¹ ^ 2 * a) * weyl t := by
    rw [weyl_lower ht]
    congr 1
    field_simp
  rw [e, rho_mul, rho_mul, weyl_weyl S ht, S.lo_fix _ y hy]

private theorem Setup.weyl_mem_X' (S : Setup ρ X X')
    {t : K} (ht : t ≠ 0) {x : Mm} (hx : x ∈ X) : ρ (weyl t) x ∈ X' := by
  refine S.cent_lo _ fun b => ?_
  have e : lower b = weyl t * upper (t ^ 2 * b) * weyl t := by
    rw [weyl_upper ht]
    congr 1
    field_simp
  rw [e, rho_mul, rho_mul, weyl_weyl S ht, S.up_fix _ x hx]

private theorem Setup.weyl_X' (S : Setup ρ X X') {t : K} (ht : t ≠ 0) {y : Mm} (hy : y ∈ X') :
    ρ (weyl t) y = opE ρ t y ∧ opF ρ t⁻¹ (opE ρ t y) = y := by
  have hE : opE ρ t y ∈ X := S.opE_mem t y
  have hFE : opF ρ t⁻¹ (opE ρ t y) ∈ X' := S.opF_mem _ _
  have hEFE : opE ρ t (opF ρ t⁻¹ (opE ρ t y)) ∈ X := S.opE_mem _ _
  have e : ρ (weyl t) y =
      (y + opF ρ t⁻¹ (opE ρ t y)) + opE ρ t (opF ρ t⁻¹ (opE ρ t y)) := by
    rw [S.weyl_apply, S.up_apply t y, map_add, S.lo_fix _ y hy, S.lo_apply _ (opE ρ t y), map_add,
      map_add, S.up_apply t y, S.up_fix t _ hE, S.up_apply t (opF ρ t⁻¹ (opE ρ t y))]
    rw [show ∀ p q r s : Mm, p + q + (q + (r + s)) = p + r + s + (q + q) from
      fun p q r s => by abel, add_self' (K := K), add_zero]
  have hz : y + opF ρ t⁻¹ (opE ρ t y) = 0 := by
    refine S.eq_zero ?_ (X'.add_mem hy hFE)
    have h := X.sub_mem (S.weyl_mem_X ht hy) hEFE
    rwa [e, add_sub_cancel_right] at h
  have hFE' : opF ρ t⁻¹ (opE ρ t y) = y :=
    (neg_eq_of_add_eq_zero_right hz).symm.trans (neg' (K := K) y)
  refine ⟨?_, hFE'⟩
  rw [e, hz, zero_add, hFE']

private theorem Setup.weyl_X (S : Setup ρ X X') {t : K} (ht : t ≠ 0) {x : Mm} (hx : x ∈ X) :
    ρ (weyl t) x = opF ρ t⁻¹ x ∧ opE ρ t (opF ρ t⁻¹ x) = x := by
  have hF : opF ρ t⁻¹ x ∈ X' := S.opF_mem _ _
  have hEF : opE ρ t (opF ρ t⁻¹ x) ∈ X := S.opE_mem _ _
  have e : ρ (weyl t) x = opF ρ t⁻¹ x + (x + opE ρ t (opF ρ t⁻¹ x)) := by
    rw [S.weyl_apply, S.up_fix t x hx, S.lo_apply t⁻¹ x, map_add, S.up_fix t x hx,
      S.up_apply t (opF ρ t⁻¹ x)]
    abel
  have hz : x + opE ρ t (opF ρ t⁻¹ x) = 0 := by
    refine S.eq_zero (X.add_mem hx hEF) ?_
    have h := X'.sub_mem (S.weyl_mem_X' ht hx) hF
    rwa [e, add_sub_cancel_left] at h
  refine ⟨?_, (neg_eq_of_add_eq_zero_right hz).symm.trans (neg' (K := K) x)⟩
  rw [e, hz, add_zero]

private theorem Setup.opF_opE_one (S : Setup ρ X X')
    {y : Mm} (hy : y ∈ X') : opF ρ 1 (opE ρ 1 y) = y := by
  simpa using (S.weyl_X' one_ne_zero hy).2

private theorem Setup.opE_opF_one (S : Setup ρ X X')
    {x : Mm} (hx : x ∈ X) : opE ρ 1 (opF ρ 1 x) = x := by
  simpa using (S.weyl_X one_ne_zero hx).2

private theorem Setup.opE_sq_mul (S : Setup ρ X X')
    {t : K} (ht : t ≠ 0) {y : Mm} (hy : y ∈ X') (b : K) :
    opE ρ (t ^ 2 * b) y = opE ρ t (opF ρ b (opE ρ t y)) := by
  have hE : opE ρ t y ∈ X := S.opE_mem _ _
  have hFb : opF ρ b (opE ρ t y) ∈ X' := S.opF_mem _ _
  rw [opE_apply, ← weyl_lower ht b, rho_mul, rho_mul, (S.weyl_X' ht hy).1,
    S.lo_apply b (opE ρ t y), map_add, (S.weyl_X ht hE).1, (S.weyl_X' ht hy).2,
    (S.weyl_X' ht hFb).1, add_sub_cancel_left]

private theorem Setup.opE_eq (S : Setup ρ X X')
    {y : Mm} (hy : y ∈ X') (a : K) : opE ρ a y = opE ρ 1 (kap ρ a y) :=
  (S.opE_opF_one (S.opE_mem a y)).symm

private theorem Setup.opF_opE (S : Setup ρ X X')
    {y : Mm} (hy : y ∈ X') (b : K) : opF ρ b (opE ρ 1 y) = kap ρ b y := by
  have h := S.opE_sq_mul one_ne_zero hy b
  rw [one_pow, one_mul] at h
  rw [kap_apply, h, S.opF_opE_one (S.opF_mem _ _)]

private theorem Setup.opF_X (S : Setup ρ X X')
    {x : Mm} (hx : x ∈ X) (b : K) : opF ρ b x = kap ρ b (opF ρ 1 x) := by
  conv_lhs => rw [← S.opE_opF_one hx]
  exact S.opF_opE (S.opF_mem 1 x) b

private theorem Setup.kap_mem (S : Setup ρ X X') (a : K) (m : Mm) : kap ρ a m ∈ X' := S.opF_mem _ _

private theorem Setup.kap_add (S : Setup ρ X X')
    (a b : K) (m : Mm) : kap ρ (a + b) m = kap ρ a m + kap ρ b m := by
  rw [kap_apply, S.opE_add, map_add]
  rfl

private theorem Setup.kap_one (S : Setup ρ X X')
    {y : Mm} (hy : y ∈ X') : kap ρ 1 y = y := S.opF_opE_one hy

private theorem Setup.kap_sq_mul (S : Setup ρ X X') {y : Mm} (hy : y ∈ X') (t b : K) :
    kap ρ (t ^ 2 * b) y = kap ρ t (kap ρ b (kap ρ t y)) := by
  by_cases ht : t = 0
  · subst ht
    simp [kap_apply, S.opE_zero]
  · rw [kap_apply, S.opE_sq_mul ht hy b, S.opF_X (S.opE_mem t y) b]
    rfl

private theorem Setup.kap_sq (S : Setup ρ X X')
    {z : Mm} (hz : z ∈ X') (u : K) : kap ρ (u ^ 2) z = kap ρ u (kap ρ u z) := by
  have h := S.kap_sq_mul hz u 1
  rwa [mul_one, S.kap_one (S.kap_mem _ _)] at h

private theorem Setup.kap_comm (S : Setup ρ X X') {y : Mm} (hy : y ∈ X') (t s : K) :
    kap ρ t (kap ρ s y) = kap ρ s (kap ρ t y) := by
  have h1 := S.kap_sq hy (t + s)
  rw [CharTwo.add_sq, S.kap_add, S.kap_sq hy t, S.kap_sq hy s, S.kap_add, S.kap_add, map_add,
    map_add] at h1
  have h2 : kap ρ t (kap ρ s y) + kap ρ s (kap ρ t y) = 0 := by
    have : ∀ A B C D : Mm, A + D = A + B + (C + D) → B + C = 0 := fun A B C D h => by
      calc B + C = A + B + (C + D) - (A + D) := by abel
        _ = 0 := by rw [← h, sub_self]
    exact this _ _ _ _ h1
  exact sub_eq_zero.1 (by rw [sub_eq_add' (K := K)]; exact h2)

private theorem Setup.kap_mul [Finite K] (S : Setup ρ X X') {y : Mm} (hy : y ∈ X') (a b : K) :
    kap ρ (a * b) y = kap ρ a (kap ρ b y) := by
  obtain ⟨r, rfl⟩ := isSquare_of_charTwo' a
  rw [← pow_two, S.kap_sq_mul hy r b, S.kap_comm hy b r, S.kap_sq (S.kap_mem _ _) r]


end KS95

namespace HS9

open KS95

theorem sl2_twist_of_cent (K : Type) [Field K] [Finite K] [CharP K 2] (Mm : Type) [AddCommGroup Mm]
    [Module K Mm] [FiniteDimensional K Mm]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm))
    (X X' : Submodule K Mm) (hXX' : IsCompl X X')
    (hU : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 →
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
        (∀ m, ρ g m - m ∈ X) ∧ ∀ x ∈ X, ρ g x = x)
    (hL : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 →
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 →
        (∀ m, ρ g m - m ∈ X') ∧ ∀ x ∈ X', ρ g x = x)
    (hCU : ∀ m : Mm, (∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 →
        (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 → ρ g m = m) → m ∈ X)
    (hCL : ∀ m : Mm, (∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 →
        (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 → ρ g m = m) → m ∈ X')
    (g₁ : Matrix.SpecialLinearGroup (Fin 2) K) (h₁₀₀ : (g₁ : Matrix (Fin 2) (Fin 2) K) 0 0 = 1)
    (h₁₁₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1)
    (h₁₁₀ : (g₁ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h₁₀₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) 0 1 = 1) :
    ∃ Y : (K ≃+* K) → Submodule K Mm,
      (∀ σ, Y σ ≤ X') ∧ iSupIndep Y ∧ ⨆ σ, Y σ = X' ∧
      ∀ σ, ∀ y ∈ Y σ, ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
        (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 →
        ((g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
          ρ g y - y = σ ((g : Matrix (Fin 2) (Fin 2) K) 0 1) • (ρ g₁ y - y)) ∧
        ((g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 →
          ρ g (ρ g₁ y - y) - (ρ g₁ y - y) = σ ((g : Matrix (Fin 2) (Fin 2) K) 1 0) • y) := by
  have hUa : ∀ a : K, (∀ m, ρ (upper a) m - m ∈ X) ∧ ∀ x ∈ X, ρ (upper a) x = x := fun a =>
    hU (upper a) (by simp) (by simp) (by simp)
  have hLb : ∀ b : K, (∀ m, ρ (lower b) m - m ∈ X') ∧ ∀ x ∈ X', ρ (lower b) x = x := fun b =>
    hL (lower b) (by simp) (by simp) (by simp)
  have S : Setup ρ X X' :=
    { compl := hXX'
      up_mem := fun a => (hUa a).1
      up_fix := fun a => (hUa a).2
      lo_mem := fun b => (hLb b).1
      lo_fix := fun b => (hLb b).2
      cent_up := fun m hm => hCU m fun g h00 h11 h10 => by
        rw [eq_upper g h00 h11 h10]
        exact hm _
      cent_lo := fun m hm => hCL m fun g h00 h11 h01 => by
        rw [eq_lower g h00 h11 h01]
        exact hm _ }
  obtain ⟨hind, hsup⟩ := iSupIndep_and_iSup_eq_of_ringHom X' (kap ρ) (fun a m _ => S.kap_mem a m)
    (fun a b m _ => S.kap_add a b m) (fun a b y hy => S.kap_mul hy a b) (fun y hy => S.kap_one hy)
  refine ⟨fun σ => X' ⊓ ⨅ a, (kap ρ a).eigenspace (σ a), fun σ => inf_le_left, hind, hsup, ?_⟩
  intro σ y hy g h00 h11
  have hyX' : y ∈ X' := (Submodule.mem_inf.1 hy).1
  have hyk : ∀ a, kap ρ a y = σ a • y := fun a =>
    Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 (Submodule.mem_inf.1 hy).2 a)
  have hg₁ : ρ g₁ y - y = opE ρ 1 y := by
    rw [opE_apply, ← h₁₀₁, ← eq_upper g₁ h₁₀₀ h₁₁₁ h₁₁₀]
  rw [hg₁]
  refine ⟨fun h10 => ?_, fun h01 => ?_⟩
  · rw [show ρ g y - y = opE ρ ((g : Matrix (Fin 2) (Fin 2) K) 0 1) y by
      rw [opE_apply, ← eq_upper g h00 h11 h10], S.opE_eq hyX', hyk, map_smul]
  · rw [show ρ g (opE ρ 1 y) - opE ρ 1 y = opF ρ ((g : Matrix (Fin 2) (Fin 2) K) 1 0) (opE ρ 1 y) by
      rw [opF_apply, ← eq_lower g h00 h11 h01], S.opF_opE hyX', hyk]

theorem sl2_twist (K : Type) [Field K] [Finite K] [CharP K 2] (Mm : Type) [AddCommGroup Mm]
    [Module K Mm] [FiniteDimensional K Mm]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* (Mm ≃ₗ[K] Mm))
    (X X' : Submodule K Mm) (hXX' : IsCompl X X')
    (hU : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 →
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
        (∀ m, ρ g m - m ∈ X) ∧ ∀ x ∈ X, ρ g x = x)
    (hL : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 →
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 →
        (∀ m, ρ g m - m ∈ X') ∧ ∀ x ∈ X', ρ g x = x)
    (hC : ∀ m : Mm, (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ρ g m = m) → m = 0)
    (g₁ : Matrix.SpecialLinearGroup (Fin 2) K) (h₁₀₀ : (g₁ : Matrix (Fin 2) (Fin 2) K) 0 0 = 1)
    (h₁₁₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1)
    (h₁₁₀ : (g₁ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h₁₀₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) 0 1 = 1) :
    ∃ Y : (K ≃+* K) → Submodule K Mm,
      (∀ σ, Y σ ≤ X') ∧ iSupIndep Y ∧ ⨆ σ, Y σ = X' ∧
      ∀ σ, ∀ y ∈ Y σ, ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
        (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 →
        ((g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
          ρ g y - y = σ ((g : Matrix (Fin 2) (Fin 2) K) 0 1) • (ρ g₁ y - y)) ∧
        ((g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 →
          ρ g (ρ g₁ y - y) - (ρ g₁ y - y) = σ ((g : Matrix (Fin 2) (Fin 2) K) 1 0) • y) := by
  have hUa : ∀ a : K, ∀ x ∈ X, ρ (upper a) x = x := fun a =>
    (hU (upper a) (by simp) (by simp) (by simp)).2
  have hLb : ∀ b : K, ∀ x ∈ X', ρ (lower b) x = x := fun b =>
    (hL (lower b) (by simp) (by simp) (by simp)).2
  have hm : ∀ m : Mm, ∃ x ∈ X, ∃ y ∈ X', x + y = m := fun m =>
    Submodule.mem_sup.1 (hXX'.sup_eq_top ▸ Submodule.mem_top)
  refine sl2_twist_of_cent K Mm ρ X X' hXX' hU hL ?_ ?_ g₁ h₁₀₀ h₁₁₁ h₁₁₀ h₁₀₁
  · intro m hfix
    obtain ⟨x, hx, y, hy, rfl⟩ := hm m
    have hyU : ∀ a, ρ (upper a) y = y := fun a => by
      have h := hfix (upper a) (by simp) (by simp) (by simp)
      rw [map_add, hUa a x hx] at h
      exact add_left_cancel h
    rw [hC y (fixed_of_upper_lower ρ hyU fun b => hLb b y hy), add_zero]
    exact hx
  · intro m hfix
    obtain ⟨x, hx, y, hy, rfl⟩ := hm m
    have hxL : ∀ b, ρ (lower b) x = x := fun b => by
      have h := hfix (lower b) (by simp) (by simp) (by simp)
      rw [map_add, hLb b y hy] at h
      exact add_right_cancel h
    rw [hC x (fixed_of_upper_lower ρ (fun a => hUa a x hx) hxL), zero_add]
    exact hy

end HS9

end CFSG.RankThree.GF2n.Stroth80

end
