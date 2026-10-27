module

public import CFSG.Certificates.CosetFacts

public section

namespace CFSG.Monster.GMS.R433Cover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

variable {E : Type*} [Group E]

@[expose] def IsZ (z x : E) : Prop := x = 1 ∨ x = z

@[expose] def cm (a x : E) : E := a * x * a⁻¹ * x⁻¹

section Z

variable {z : E} (hzc : ∀ g : E, g * z = z * g) (hz2 : z * z = 1)
include hzc hz2

theorem IsZ.comm {x : E} (hx : IsZ z x) (g : E) : g * x = x * g := by
  rcases hx with rfl | rfl
  · simp
  · exact hzc g

theorem IsZ.mul_self {x : E} (hx : IsZ z x) : x * x = 1 := by
  rcases hx with rfl | rfl
  · simp
  · exact hz2

theorem IsZ.inv_eq {x : E} (hx : IsZ z x) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (IsZ.mul_self hzc hz2 hx)

theorem IsZ.mul {x y : E} (hx : IsZ z x) (hy : IsZ z y) : IsZ z (x * y) := by
  rcases hx with rfl | rfl
  · simpa using hy
  · rcases hy with rfl | rfl
    · right; simp
    · left; exact hz2

theorem IsZ.pow_odd {x : E} (hx : IsZ z x) {n : ℕ} (hn : n % 2 = 1) : x ^ n = x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  rw [pow_succ, pow_mul, sq, IsZ.mul_self hzc hz2 hx, one_pow, one_mul]

end Z

theorem core_sq_cube {a b A B X : E} (hA : a * a = A) (hB : b * b = B) (hX : (a * b) ^ 3 = X)
    (cA : ∀ g : E, g * A = A * g) (cB : ∀ g : E, g * B = B * g) (cX : ∀ g : E, g * X = X * g)
    (sA : A * A = 1) (sB : B * B = 1) (sX : X * X = 1) : A * B = 1 := by
  have ainv : a⁻¹ = a * A := by
    have h : a⁻¹ = a * A⁻¹ := by
      rw [← hA]; group
    rw [h, inv_eq_of_mul_eq_one_right sA]
  have binv : b⁻¹ = b * B := by
    have h : b⁻¹ = b * B⁻¹ := by
      rw [← hB]; group
    rw [h, inv_eq_of_mul_eq_one_right sB]
  have cAB : ∀ g : E, g * (A * B) = (A * B) * g := by
    intro g
    calc g * (A * B) = (g * A) * B := by group
      _ = (A * g) * B := by rw [cA g]
      _ = A * (g * B) := by group
      _ = A * (B * g) := by rw [cB g]
      _ = (A * B) * g := by group
  have sAB : (A * B) * (A * B) = 1 := by
    calc (A * B) * (A * B) = A * (B * A) * B := by group
      _ = A * (A * B) * B := by rw [cA B]
      _ = (A * A) * (B * B) := by group
      _ = 1 := by rw [sA, sB, one_mul]
  have h1 : b * (a * b) * b⁻¹ = (a * b)⁻¹ * (A * B) := by
    have e : (a * b)⁻¹ * (A * B) = b * (a * (A * A) * (B * B)) * 1 := by
      rw [mul_inv_rev, binv, ainv]
      calc b * B * (a * A) * (A * B) = b * (B * (a * A * (A * B))) := by group
        _ = b * ((a * A * (A * B)) * B) := by rw [cB (a * A * (A * B))]
        _ = b * (a * (A * A) * (B * B)) * 1 := by group
    rw [e, sA, sB]; group
  have h2 : (b * (a * b) * b⁻¹) ^ 3 = X := by
    rw [conj_pow, hX]
    rw [cX b]; group
  have h3 : ((a * b)⁻¹ * (A * B)) ^ 3 = ((a * b)⁻¹) ^ 3 * (A * B) := by
    have hc : Commute ((a * b)⁻¹) (A * B) := cAB _
    rw [hc.mul_pow]
    have hsq : (A * B) ^ 3 = A * B := by
      calc (A * B) ^ 3 = (A * B) * (A * B) * (A * B) := pow_three' _
        _ = A * B := by rw [sAB, one_mul]
    rw [hsq]
  have h4 : X = ((a * b)⁻¹) ^ 3 * (A * B) := by rw [← h2, h1, h3]
  have h5 : X * X = A * B := by
    calc X * X = (a * b) ^ 3 * (((a * b)⁻¹) ^ 3 * (A * B)) := by rw [hX, ← h4]
      _ = A * B := by rw [inv_pow, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← h5, sX]

theorem sq_eq_of_cube {z : E} (hzc : ∀ g : E, g * z = z * g) (hz2 : z * z = 1) {a b : E}
    (ha : IsZ z (a * a)) (hb : IsZ z (b * b)) (hx : IsZ z ((a * b) ^ 3)) : a * a = b * b := by
  have h := core_sq_cube (A := a * a) (B := b * b) (X := (a * b) ^ 3) rfl rfl rfl
    (IsZ.comm hzc hz2 ha) (IsZ.comm hzc hz2 hb) (IsZ.comm hzc hz2 hx)
    (IsZ.mul_self hzc hz2 ha) (IsZ.mul_self hzc hz2 hb) (IsZ.mul_self hzc hz2 hx)
  rw [eq_inv_of_mul_eq_one_left h, IsZ.inv_eq hzc hz2 hb]

theorem cm_mul (a x y : E) : cm a (x * y) = cm a x * (x * cm a y * x⁻¹) := by
  unfold cm; group

theorem cm_mul_of_central {a x y : E} (hy : ∀ g : E, g * cm a y = cm a y * g) :
    cm a (x * y) = cm a x * cm a y := by
  rw [cm_mul, hy x]; group

theorem cm_inv_of_central {a x : E} (hx : ∀ g : E, g * cm a x = cm a x * g) :
    cm a x⁻¹ = (cm a x)⁻¹ := by
  have h : cm a x⁻¹ = x⁻¹ * (cm a x)⁻¹ * x := by unfold cm; group
  rw [h]
  have hc : Commute x⁻¹ (cm a x)⁻¹ := Commute.inv_right (hx x⁻¹)
  rw [hc.eq]; group

theorem cm_swap {z a b : E} (hzc : ∀ g : E, g * z = z * g) (hz2 : z * z = 1)
    (h : IsZ z (cm a b)) : cm b a = cm a b := by
  have : cm b a = (cm a b)⁻¹ := by unfold cm; group
  rw [this, IsZ.inv_eq hzc hz2 h]

theorem cube_swap {s t : E} (h : (s * t) ^ 3 = 1) : (t * s) ^ 3 = 1 := by
  have e : t * s = s⁻¹ * (s * t) * s⁻¹⁻¹ := by group
  rw [e, conj_pow, h]; group

theorem cm_slide {z : E} (hzc : ∀ g : E, g * z = z * g) (hz2 : z * z = 1) {a b c : E}
    (hb : IsZ z (cm a b)) (hc : IsZ z (cm a c)) (h3 : (b * c) ^ 3 = 1) : cm a b = cm a c := by
  have hbc : b * c * b = (c * b * c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have : (b * c) ^ 3 = b * c * b * (c * b * c) := by rw [pow_three']; group
    rw [← this]; exact h3
  have cb := IsZ.comm hzc hz2 hb
  have cc := IsZ.comm hzc hz2 hc
  have e1 : cm a (b * c * b) = cm a b * cm a c * cm a b := by
    rw [cm_mul_of_central cb, cm_mul_of_central cc]
  have e2 : cm a (c * b * c) = cm a c * cm a b * cm a c := by
    rw [cm_mul_of_central cc, cm_mul_of_central cb]
  have hcen : ∀ g : E, g * cm a (c * b * c) = cm a (c * b * c) * g := by
    rw [e2]
    exact IsZ.comm hzc hz2 (IsZ.mul hzc hz2 (IsZ.mul hzc hz2 hc hb) hc)
  have e3 : cm a (b * c * b) = (cm a (c * b * c))⁻¹ := by
    rw [hbc, cm_inv_of_central hcen]
  rw [e1, e2] at e3
  rcases hb with h | h <;> rcases hc with h' | h' <;> rw [h, h'] at e3 ⊢ <;>
    first | rfl | (simp [hz2] at e3; first | exact e3 | exact e3.symm)

theorem cm_evalWord {a : E} {g : ℕ → E} {k : E} (hk : ∀ x : E, x * k = k * x) {w : List ℕ}
    (h : ∀ c ∈ w, cm a (g c) = k) : cm a (evalWord g w) = k ^ w.length := by
  induction w with
  | nil => simp [cm]
  | cons c w ih =>
    rw [evalWord_cons, List.length_cons]
    have hc : cm a (g c) = k := h c (by simp)
    have ih' := ih (fun c' hc' => h c' (by simp [hc']))
    have hcen : ∀ x : E, x * cm a (evalWord g w) = cm a (evalWord g w) * x := by
      rw [ih']; intro x; exact Commute.pow_right (hk x) _
    rw [cm_mul_of_central hcen, hc, ih', pow_succ']

theorem cm_pow_of_central {a u : E} (hu : ∀ g : E, g * cm a u = cm a u * g) (n : ℕ) :
    cm a (u ^ n) = (cm a u) ^ n := by
  induction n with
  | zero => simp [cm]
  | succ n ih => rw [pow_succ, cm_mul_of_central hu, ih, pow_succ]

theorem kappa_zero {z : E} (hzc : ∀ g : E, g * z = z * g) (hz2 : z * z = 1) {a : E}
    {g : ℕ → E} {w : List ℕ} {k : E} (hkZ : IsZ z k) (h : ∀ c ∈ w, cm a (g c) = k)
    (hw : w.length % 2 = 1) (hF : IsZ z ((evalWord g w) ^ 9)) : k = 1 := by
  have hk := IsZ.comm hzc hz2 hkZ
  have h1 := cm_evalWord hk h
  rw [IsZ.pow_odd hzc hz2 hkZ hw] at h1
  have h2 := cm_pow_of_central (a := a) (u := evalWord g w) (by rw [h1]; exact hk) 9
  rw [h1, IsZ.pow_odd hzc hz2 hkZ (by norm_num)] at h2
  have hF' := IsZ.comm hzc hz2 hF a
  have h3 : cm a (evalWord g w ^ 9) = 1 := by unfold cm; rw [hF']; group
  rw [h3] at h2
  exact h2.symm

theorem sq_prod3 {a b c : E} (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * b * c) ^ 2 = a ^ 2 * b ^ 2 * c ^ 2 := by
  have h1 : Commute a b := hab
  have h2 : Commute a c := hac
  have h3 : Commute b c := hbc
  rw [(h2.mul_left h3).mul_pow, h1.mul_pow]

theorem sq_prod4 {a b c d : E} (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a)
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c) :
    (a * b * c * d) ^ 2 = a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 := by
  have h3 : Commute a d := had
  have h5 : Commute b d := hbd
  have h6 : Commute c d := hcd
  rw [((h3.mul_left h5).mul_left h6).mul_pow, sq_prod3 hab hac hbc]

theorem eps_zero {z : E} (hzc : ∀ g : E, g * z = z * g) (hz2 : z * z = 1)
    {a b c a' b' c' d' y A : E}
    (hA : IsZ z A) (ha : a * a = A) (hb : b * b = A) (hc : c * c = A)
    (ha' : a' * a' = A) (hb' : b' * b' = A) (hc' : c' * c' = A) (hd' : d' * d' = A)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (hab' : a' * b' = b' * a') (hac' : a' * c' = c' * a') (had' : a' * d' = d' * a')
    (hbc' : b' * c' = c' * b') (hbd' : b' * d' = d' * b') (hcd' : c' * d' = d' * c')
    (hy : IsZ z (y⁻¹ * (a * b * c) * y * (a' * b' * c' * d')⁻¹)) : A = 1 := by
  have cA := IsZ.comm hzc hz2 hA
  have sA := IsZ.mul_self hzc hz2 hA
  have e3 : (a * b * c) ^ 2 = A := by
    rw [sq_prod3 hab hac hbc, sq, sq, sq, ha, hb, hc, sA, one_mul]
  have e4 : (a' * b' * c' * d') ^ 2 = 1 := by
    rw [sq_prod4 hab' hac' had' hbc' hbd' hcd', sq, sq, sq, sq, ha', hb', hc', hd', sA, one_mul,
      sA]
  have ck := IsZ.comm hzc hz2 hy
  have sk := IsZ.mul_self hzc hz2 hy
  have hk' : y⁻¹ * (a * b * c) * y =
      (y⁻¹ * (a * b * c) * y * (a' * b' * c' * d')⁻¹) * (a' * b' * c' * d') := by group
  have h1 : (y⁻¹ * (a * b * c) * y) ^ 2 = A := by
    have : y⁻¹ * (a * b * c) * y = y⁻¹ * (a * b * c) * y⁻¹⁻¹ := by group
    rw [this, conj_pow, e3, inv_inv, cA y⁻¹]
    group
  have h2 : (y⁻¹ * (a * b * c) * y) ^ 2 = 1 := by
    rw [hk']
    have hc : Commute (y⁻¹ * (a * b * c) * y * (a' * b' * c' * d')⁻¹) (a' * b' * c' * d') :=
      ck _ |>.symm
    rw [hc.mul_pow, e4, mul_one, sq, sk]
  rw [← h1, h2]

section Words

variable {G : Type*} [Group G]

theorem evalWord_mul_central {z : E} (hzc : ∀ x : E, x * z = z * x) (gh : ℕ → E) (w : List ℕ) :
    evalWord (fun c => gh c * z) w = evalWord gh w * z ^ w.length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [evalWord_cons, ih, evalWord_cons, List.length_cons, pow_succ']
    calc gh c * z * (evalWord gh w * z ^ w.length)
        = gh c * (z * evalWord gh w) * z ^ w.length := by simp only [mul_assoc]
      _ = gh c * (evalWord gh w * z) * z ^ w.length := by rw [← hzc (evalWord gh w)]
      _ = gh c * evalWord gh w * (z * z ^ w.length) := by simp only [mul_assoc]

theorem map_evalWord_of_forall (π : E →* G) (gh : ℕ → E) (g : ℕ → G) (w : List ℕ)
    (h : ∀ c ∈ w, π (gh c) = g c) : π (evalWord gh w) = evalWord g w := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [evalWord_cons, map_mul, h c (by simp), ih (fun c' hc' => h c' (by simp [hc'])),
      evalWord_cons]

theorem commute_of_sq {x y : G} (hx : x * x = 1) (hy : y * y = 1) (h : (x * y) ^ 2 = 1) :
    x * y = y * x := by
  have h1 : x * y * (x * y) = 1 := by rw [← sq]; exact h
  rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hx,
    inv_eq_of_mul_eq_one_right hy]

theorem evalWord_reverse_inv {g : ℕ → G} (hinv : ∀ c, g c * g c = 1) (w : List ℕ) :
    evalWord g w.reverse = (evalWord g w)⁻¹ := by
  induction w with
  | nil => simp
  | cons c w ih =>
    have h1 : evalWord g (c :: w) = g c * evalWord g w := evalWord_cons g c w
    rw [List.reverse_cons, evalWord_append, ih, h1, mul_inv_rev]
    simp only [evalWord_cons, evalWord_nil, mul_one]
    rw [inv_eq_of_mul_eq_one_right (hinv c)]

end Words

end CFSG.Monster.GMS.R433Cover
