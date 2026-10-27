module

public import CFSG.GH74.QTGen4.Recog.G23.HLettersF
public import CFSG.GH74.QTGen4.Recog.G23.HLettersI
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.G23Type.Ctx

open scoped MatrixGroups

variable {X : Type*} [Group X]

@[expose] def zS : SL(2, ZMod 3) := ⟨-1, by decide +kernel⟩

theorem sl_fin_unique_invol : ∀ A : SL(2, ZMod 3), A * A = 1 → A ≠ 1 → A = zS := by
  decide +kernel

theorem sl_fin_pow4_mul : ∀ A B : SL(2, ZMod 3), A ^ 4 = 1 → B ^ 4 = 1 → (A * B) ^ 4 = 1 := by
  decide +kernel

theorem sl_fin_pow12 : ∀ A : SL(2, ZMod 3), (A ^ 3) ^ 4 = 1 := by
  decide +kernel

theorem sl_fin_centralizer :
    ∀ A : SL(2, ZMod 3), (∀ Q : SL(2, ZMod 3), Q ^ 4 = 1 → A * Q = Q * A) → A = 1 ∨ A = zS := by
  decide +kernel

theorem sl_fin_exists_comm :
    ∃ S T : SL(2, ZMod 3), S ^ 4 = 1 ∧ T ^ 4 = 1 ∧ S * T * S⁻¹ * T⁻¹ = zS := by
  decide +kernel

theorem sl_fin_exists_order_three : ∃ A : SL(2, ZMod 3), A ^ 3 = 1 ∧ A ≠ 1 := by
  decide +kernel

theorem sl_fin_order_three_fpf :
    ∀ A : SL(2, ZMod 3), A ^ 3 = 1 → A ≠ 1 → ∀ Q : SL(2, ZMod 3), Q ^ 4 = 1 → Q ≠ 1 → Q ≠ zS →
      A * Q * A⁻¹ ≠ Q ∧ A * Q * A⁻¹ ≠ Q * zS := by
  decide +kernel

theorem sl_fin_not_inner_swap :
    ∀ A : SL(2, ZMod 3), A ^ 4 = 1 → A ≠ 1 → A ≠ zS →
      ∀ B : SL(2, ZMod 3), B ^ 4 = 1 → B ≠ 1 → B ≠ zS → A ≠ B → A ≠ B * zS →
      ∀ S : SL(2, ZMod 3), (S * A * S⁻¹ = B ∨ S * A * S⁻¹ = B * zS) →
        (S * B * S⁻¹ = A ∨ S * B * S⁻¹ = A * zS) → False := by
  decide +kernel

theorem e_z_eq_zS (e : X ≃* SL(2, ZMod 3)) {z : X} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    e z = zS := by
  apply sl_fin_unique_invol (e z)
  · rw [← map_mul, ← pow_two, hz2, map_one]
  · intro h
    apply hz1
    apply e.injective
    rw [h, map_one]

theorem sl23_unique_invol (hX : Nonempty (X ≃* SL(2, ZMod 3))) {z : X} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) : ∀ x : X, x ^ 2 = 1 → x = 1 ∨ x = z := by
  obtain ⟨e⟩ := hX
  intro x hx
  by_cases h1 : e x = 1
  · exact Or.inl (e.injective (by rw [h1, map_one]))
  · refine Or.inr (e.injective ?_)
    rw [e_z_eq_zS e hz2 hz1]
    apply sl_fin_unique_invol (e x)
    · rw [← map_mul, ← pow_two, hx, map_one]
    · exact h1

theorem sl23_pow4_mul (hX : Nonempty (X ≃* SL(2, ZMod 3))) :
    ∀ x y : X, x ^ 4 = 1 → y ^ 4 = 1 → (x * y) ^ 4 = 1 := by
  obtain ⟨e⟩ := hX
  intro x y hx hy
  apply e.injective
  rw [map_pow, map_mul, map_one]
  exact sl_fin_pow4_mul (e x) (e y) (by rw [← map_pow, hx, map_one])
    (by rw [← map_pow, hy, map_one])

theorem sl23_pow12 (hX : Nonempty (X ≃* SL(2, ZMod 3))) : ∀ x : X, (x ^ 3) ^ 4 = 1 := by
  obtain ⟨e⟩ := hX
  intro x
  apply e.injective
  rw [map_pow, map_pow, map_one]
  exact sl_fin_pow12 (e x)

theorem sl23_centralizer_pow4 (hX : Nonempty (X ≃* SL(2, ZMod 3))) {z : X} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) : ∀ x : X, (∀ q : X, q ^ 4 = 1 → x * q = q * x) → x = 1 ∨ x = z := by
  obtain ⟨e⟩ := hX
  intro x hx
  have hC : ∀ Q : SL(2, ZMod 3), Q ^ 4 = 1 → e x * Q = Q * e x := by
    intro Q hQ
    have h4 : (e.symm Q) ^ 4 = 1 := by rw [← map_pow, hQ, map_one]
    have h := congrArg e (hx (e.symm Q) h4)
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  rcases sl_fin_centralizer (e x) hC with h | h
  · exact Or.inl (e.injective (by rw [h, map_one]))
  · exact Or.inr (e.injective (by rw [h, e_z_eq_zS e hz2 hz1]))

theorem sl23_exists_comm (hX : Nonempty (X ≃* SL(2, ZMod 3))) {z : X} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) : ∃ s t : X, s ^ 4 = 1 ∧ t ^ 4 = 1 ∧ s * t * s⁻¹ * t⁻¹ = z := by
  obtain ⟨e⟩ := hX
  obtain ⟨S, T, hS, hT, hST⟩ := sl_fin_exists_comm
  refine ⟨e.symm S, e.symm T, ?_, ?_, ?_⟩
  · rw [← map_pow, hS, map_one]
  · rw [← map_pow, hT, map_one]
  · apply e.injective
    rw [e_z_eq_zS e hz2 hz1]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hST

theorem sl23_exists_order_three (hX : Nonempty (X ≃* SL(2, ZMod 3))) :
    ∃ a : X, a ^ 3 = 1 ∧ a ≠ 1 := by
  obtain ⟨e⟩ := hX
  obtain ⟨A, hA3, hA1⟩ := sl_fin_exists_order_three
  refine ⟨e.symm A, ?_, ?_⟩
  · rw [← map_pow, hA3, map_one]
  · intro h
    apply hA1
    have h' := congrArg e h
    rwa [MulEquiv.apply_symm_apply, map_one] at h'

theorem sl23_order_three_fpf (hX : Nonempty (X ≃* SL(2, ZMod 3))) {z : X} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) : ∀ a : X, a ^ 3 = 1 → a ≠ 1 → ∀ q : X, q ^ 4 = 1 → q ≠ 1 → q ≠ z →
      a * q * a⁻¹ ≠ q ∧ a * q * a⁻¹ ≠ q * z := by
  obtain ⟨e⟩ := hX
  intro a ha3 ha1 q hq4 hq1 hqz
  have hz := e_z_eq_zS e hz2 hz1
  have ha3' : (e a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have ha1' : e a ≠ 1 := fun h => ha1 (e.injective (by rw [h, map_one]))
  have hq4' : (e q) ^ 4 = 1 := by rw [← map_pow, hq4, map_one]
  have hq1' : e q ≠ 1 := fun h => hq1 (e.injective (by rw [h, map_one]))
  have hqz' : e q ≠ zS := fun h => hqz (e.injective (by rw [h, hz]))
  obtain ⟨k1, k2⟩ := sl_fin_order_three_fpf (e a) ha3' ha1' (e q) hq4' hq1' hqz'
  constructor
  · intro h
    apply k1
    have h' := congrArg e h
    simpa only [map_mul, map_inv] using h'
  · intro h
    apply k2
    have h' := congrArg e h
    simpa only [map_mul, map_inv, hz] using h'

theorem sl23_not_inner_swap (hX : Nonempty (X ≃* SL(2, ZMod 3))) {z : X} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) : ∀ s a b : X, a ^ 4 = 1 → b ^ 4 = 1 → a ≠ 1 → a ≠ z → b ≠ 1 → b ≠ z →
      a ≠ b → a ≠ b * z → (s * a * s⁻¹ = b ∨ s * a * s⁻¹ = b * z) →
      (s * b * s⁻¹ = a ∨ s * b * s⁻¹ = a * z) → False := by
  obtain ⟨e⟩ := hX
  intro s a b ha4 hb4 ha1 haz hb1 hbz hab habz h1 h2
  have hz := e_z_eq_zS e hz2 hz1
  have ha4' : (e a) ^ 4 = 1 := by rw [← map_pow, ha4, map_one]
  have hb4' : (e b) ^ 4 = 1 := by rw [← map_pow, hb4, map_one]
  have ha1' : e a ≠ 1 := fun h => ha1 (e.injective (by rw [h, map_one]))
  have hb1' : e b ≠ 1 := fun h => hb1 (e.injective (by rw [h, map_one]))
  have haz' : e a ≠ zS := fun h => haz (e.injective (by rw [h, hz]))
  have hbz' : e b ≠ zS := fun h => hbz (e.injective (by rw [h, hz]))
  have hab' : e a ≠ e b := fun h => hab (e.injective h)
  have habz' : e a ≠ e b * zS := fun h => habz (e.injective (by rw [h, map_mul, hz]))
  have h1' : e s * e a * (e s)⁻¹ = e b ∨ e s * e a * (e s)⁻¹ = e b * zS := by
    rcases h1 with h | h
    · left
      have h' := congrArg e h
      simpa only [map_mul, map_inv] using h'
    · right
      have h' := congrArg e h
      simpa only [map_mul, map_inv, hz] using h'
  have h2' : e s * e b * (e s)⁻¹ = e a ∨ e s * e b * (e s)⁻¹ = e a * zS := by
    rcases h2 with h | h
    · left
      have h' := congrArg e h
      simpa only [map_mul, map_inv] using h'
    · right
      have h' := congrArg e h
      simpa only [map_mul, map_inv, hz] using h'
  exact sl_fin_not_inner_swap (e a) ha4' ha1' haz' (e b) hb4' hb1' hbz' hab' habz' (e s) h1' h2'

section AutPart

open CFSG.GH74.QTGen4.Recog.G23

theorem m1_ne_one_M2 : (-1 : M2) ≠ 1 := by decide +kernel

theorem m1_mul_m1 : (-1 : M2) * -1 = 1 := by decide +kernel

def inv2 (g : M2) : M2 := !![-g 1 1, g 0 1; g 1 0, -g 0 0]

theorem inv2_mul : ∀ g : M2, g.det = -1 → g * inv2 g = 1 := by
  decide +kernel

theorem outer_pow_fin : ∀ g : M2, g.det = -1 → ∀ A : M2, A.det = 1 →
    (g * A * inv2 g * A) ^ 4 = 1 := by
  decide +kernel

theorem outer_moves_fin : ∀ g : M2, g.det = -1 →
    ∃ q : M2, q.det = 1 ∧ q ^ 4 = 1 ∧ g * q ≠ q * g := by
  decide +kernel

theorem inner_fin : ∀ B C : M2, B.det = 1 → B * C = 1 →
    (B * !![1, 1; 0, 1] * C * !![1, 1; 0, 1]) ^ 4 ≠ 1 := by
  decide +kernel

@[expose] def conjHomSL {g g' : M2} (h1 : g * g' = 1) (h2 : g' * g = 1) :
    SL(2, ZMod 3) →* SL(2, ZMod 3) where
  toFun M := ⟨g * M.1 * g', by rw [gap2_det_conj h1]; exact M.2⟩
  map_one' := Subtype.ext (by
    show g * (1 : SL(2, ZMod 3)).1 * g' = (1 : SL(2, ZMod 3)).1
    rw [Matrix.SpecialLinearGroup.coe_one, mul_one, h1])
  map_mul' M N := Subtype.ext (by
    show g * (M.1 * N.1) * g' = (g * M.1 * g') * (g * N.1 * g')
    calc g * (M.1 * N.1) * g' = g * M.1 * (g' * g) * N.1 * g' := by
          rw [h2]; simp only [mul_one, mul_assoc]
      _ = (g * M.1 * g') * (g * N.1 * g') := by simp only [mul_assoc])

theorem aut_form (ψ : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) :
    ∃ g g' : M2, g * g' = 1 ∧ g' * g = 1 ∧ ∀ A : SL(2, ZMod 3), (ψ A).1 = g * A.1 * g' := by
  obtain ⟨rX3, rY3, rC, -⟩ := sl_letter_rels
  have hX3 : ψ slX * ψ slX * ψ slX = 1 := by
    rw [← map_mul, ← map_mul, rX3, map_one]
  have hY3 : ψ slY * ψ slY * ψ slY = 1 := by
    rw [← map_mul, ← map_mul, rY3, map_one]
  have hXi : (ψ slX)⁻¹ = ψ slX * ψ slX :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hX3)
  have hYi : (ψ slY)⁻¹ = ψ slY * ψ slY :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hY3)
  have hC : ψ slY * ψ slY * (ψ slX * ψ slX) * ψ slY * (ψ slX * ψ slX) * (ψ slY * ψ slY) *
      ψ slX = 1 := by
    have h := congrArg ψ rC
    simp only [map_mul, map_inv, map_one] at h
    rw [hXi, hYi] at h
    exact h
  have hX3' : (ψ slX).1 * (ψ slX).1 * (ψ slX).1 = 1 := by
    have h := congrArg Subtype.val hX3
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hY3' : (ψ slY).1 * (ψ slY).1 * (ψ slY).1 = 1 := by
    have h := congrArg Subtype.val hY3
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hC' : (ψ slY).1 * (ψ slY).1 * ((ψ slX).1 * (ψ slX).1) * (ψ slY).1 *
      ((ψ slX).1 * (ψ slX).1) * ((ψ slY).1 * (ψ slY).1) * (ψ slX).1 = 1 := by
    have h := congrArg Subtype.val hC
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  obtain ⟨Z, hZ⟩ : ∃ Z : SL(2, ZMod 3), Z = slX * slY * (slX * slY) := ⟨_, rfl⟩
  have hZ1 : Z.1 = -1 := by
    rw [hZ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, slX_val, slY_val]
    exact sl_xy_sq
  have hZZ : Z * Z = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hZ1, Matrix.SpecialLinearGroup.coe_one, m1_mul_m1]
  have hZne : Z ≠ 1 := by
    intro h
    apply m1_ne_one_M2
    rw [← hZ1, h, Matrix.SpecialLinearGroup.coe_one]
  have hψZ2 : ψ Z * ψ Z = 1 := by rw [← map_mul, hZZ, map_one]
  have hψZne : ψ Z ≠ 1 := fun h => hZne (ψ.injective (h.trans (map_one ψ).symm))
  have hψZ1 : (ψ Z).1 = -1 := by
    apply sl_unique_invol (ψ Z).1 (ψ Z).2
    · have h := congrArg Subtype.val hψZ2
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
    · intro h
      exact hψZne (Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm))
  have hψZ_eq : (ψ Z).1 = (ψ slX).1 * (ψ slY).1 * ((ψ slX).1 * (ψ slY).1) := by
    rw [hZ]
    simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hXY : (ψ slX).1 * (ψ slY).1 * ((ψ slX).1 * (ψ slY).1) = -1 := by
    rw [← hψZ_eq]
    exact hψZ1
  obtain ⟨g, hgdet, hgx, hgy⟩ := gap2_conj_exists _ _ hX3' hY3' hC' hXY
  obtain ⟨g', hgg', hg'g⟩ := gap2_inv_exists g hgdet
  refine ⟨g, g', hgg', hg'g, ?_⟩
  have hon : Set.EqOn ψ.toMonoidHom (conjHomSL hgg' hg'g) ({slX, slY} : Set SL(2, ZMod 3)) := by
    rintro A (rfl | rfl)
    · apply Subtype.ext
      show (ψ slX).1 = g * slX.1 * g'
      rw [slX_val, hgx, mul_assoc, hgg', mul_one]
    · apply Subtype.ext
      show (ψ slY).1 = g * slY.1 * g'
      rw [slY_val, hgy, mul_assoc, hgg', mul_one]
  have hfun : ψ.toMonoidHom = conjHomSL hgg' hg'g := MonoidHom.eq_of_eqOn_dense sl_closure_top hon
  intro A
  exact congrArg Subtype.val (DFunLike.congr_fun hfun A)

theorem inner_fin_SL (A : SL(2, ZMod 3)) : (A * slX * A⁻¹ * slX) ^ 4 ≠ 1 := by
  intro h
  have hA : A.1 * (A⁻¹).1 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h4 := congrArg Subtype.val h
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one, slX_val] at h4
  rw [mx_eq] at h4
  exact inner_fin A.1 (A⁻¹).1 A.2 hA h4

theorem sl23_aut_dichotomy (hX : Nonempty (X ≃* SL(2, ZMod 3))) (φ : X ≃* X) :
    (∃ s : X, ∀ x, φ x = s * x * s⁻¹) ∨
      ((∀ x, (φ x * x) ^ 4 = 1) ∧ ∃ q : X, q ^ 4 = 1 ∧ φ q ≠ q) := by
  obtain ⟨e⟩ := hX
  obtain ⟨ψ, hψe⟩ : ∃ ψ : SL(2, ZMod 3) ≃* SL(2, ZMod 3), ∀ x : X, ψ (e x) = e (φ x) :=
    ⟨e.symm.trans (φ.trans e), fun x => by
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]⟩
  obtain ⟨g, g', hgg', hg'g, hform⟩ := aut_form ψ
  have hdg : g.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hgg'
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h
    exact zero_ne_one h
  rcases gap2_det_pm _ hdg with h1 | h1
  ·
    left
    obtain ⟨S, hS⟩ : ∃ S : SL(2, ZMod 3), S.1 = g := ⟨⟨g, h1⟩, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : SL(2, ZMod 3), T.1 = g' := by
      refine ⟨⟨g', ?_⟩, rfl⟩
      have h := congrArg Matrix.det hgg'
      rw [Matrix.det_mul, Matrix.det_one, h1, one_mul] at h
      exact h
    have hST : S * T = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hS, hT]
      exact hgg'
    have hSinv : S⁻¹ = T := inv_eq_of_mul_eq_one_right hST
    have hψS : ∀ A : SL(2, ZMod 3), ψ A = S * A * T := by
      intro A
      apply Subtype.ext
      rw [hform A, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hS, hT]
    refine ⟨e.symm S, fun x => ?_⟩
    apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, hSinv, ← hψe x, hψS (e x)]
  ·
    right
    have hg'eq : g' = inv2 g := by
      calc g' = g' * (g * inv2 g) := by rw [inv2_mul g h1, mul_one]
        _ = g' * g * inv2 g := (mul_assoc _ _ _).symm
        _ = inv2 g := by rw [hg'g, one_mul]
    subst hg'eq
    refine ⟨fun x => ?_, ?_⟩
    · have key : (ψ (e x) * e x) ^ 4 = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, hform (e x),
          Matrix.SpecialLinearGroup.coe_one]
        exact outer_pow_fin g h1 (e x).1 (e x).2
      have hx : φ x * x = e.symm (ψ (e x) * e x) := by
        rw [map_mul, hψe x, e.symm_apply_apply, e.symm_apply_apply]
      rw [hx, ← map_pow, key, map_one]
    · obtain ⟨q₀, hq₀det, hq₀4, hq₀ne⟩ := outer_moves_fin g h1
      obtain ⟨Q, hQ⟩ : ∃ Q : SL(2, ZMod 3), Q.1 = q₀ := ⟨⟨q₀, hq₀det⟩, rfl⟩
      have hQ4 : Q ^ 4 = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hQ]
        exact hq₀4
      refine ⟨e.symm Q, ?_, ?_⟩
      · rw [← map_pow, hQ4, map_one]
      · intro hfix
        have hψQ : ψ Q = Q := by
          have h := hψe (e.symm Q)
          rw [e.apply_symm_apply, hfix, e.apply_symm_apply] at h
          exact h
        have hm : g * q₀ * inv2 g = q₀ := by
          have h := congrArg Subtype.val hψQ
          rw [hform Q, hQ] at h
          exact h
        apply hq₀ne
        have h2 : g * q₀ = g * q₀ * inv2 g * g := by
          simp only [mul_assoc, hg'g, mul_one]
        rw [h2, hm]

theorem sl23_inner_not_inverts (hX : Nonempty (X ≃* SL(2, ZMod 3))) (s : X) :
    ∃ x : X, (s * x * s⁻¹ * x) ^ 4 ≠ 1 := by
  obtain ⟨e⟩ := hX
  refine ⟨e.symm slX, fun h => ?_⟩
  have h' := congrArg e h
  rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_one, e.apply_symm_apply] at h'
  exact inner_fin_SL (e s) h'

end AutPart

end CFSG.Quasithin.G23Type.Ctx
