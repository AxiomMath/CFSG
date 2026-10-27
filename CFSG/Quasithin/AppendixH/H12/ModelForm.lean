module

public import CFSG.Quasithin.AppendixH.H12.ModelCore
public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import CFSG.Quasithin.AppendixH.H12.Basic

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin.H13.Mat8Cert (b2z)
open CFSG.ASVolI.ChH (IsIsoPoint IsQuadFormOn IsUnitaryForm kLine kSmul)
open CFSG.Quasithin.H13.L1442M
open Matrix

@[expose] def Qcols : List ℕ := [1, 3, 6, 13, 19, 50, 97, 211, 492, 920, 1051, 3126]

theorem Qcols_valid : ValidN 12 Qcols := by
  constructor <;> decide

private theorem gmv_zU_eq (x : ℕ) : gmv zU x = mvN z12 x := by
  rw [gmv, zU_val, colsN_decN validN_z12]

private theorem glHom_zU_dc (c : ℕ) : glHom zU (dc c) = dc (mvN z12 c) := by
  rw [glHom_dc, zU_val, colsN_decN validN_z12]

private theorem gmv_gU_eq (i c : ℕ) : gmv (gU i) c = mvN (gG.getD i one12) c := by
  rw [gmv, gU_val, colsN_decN (validN_getD validN_gG i)]

private theorem quadN_gU0 (c : ℕ) (hc : c < 4096) :
    quadN 12 Qcols (mvN (gG.getD 0 one12) c) = quadN 12 Qcols c := by
  have h : (List.range 4096).all
      (fun c => quadN 12 Qcols (mvN (gG.getD 0 one12) c) == quadN 12 Qcols c) = true := by
    decide +kernel
  have := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simpa using this

private theorem quadN_gU1 (c : ℕ) (hc : c < 4096) :
    quadN 12 Qcols (mvN (gG.getD 1 one12) c) = quadN 12 Qcols c := by
  have h : (List.range 4096).all
      (fun c => quadN 12 Qcols (mvN (gG.getD 1 one12) c) == quadN 12 Qcols c) = true := by
    decide +kernel
  have := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simpa using this

private theorem quadN_gU (i : ℕ) (hi : i < 2) (c : ℕ) (hc : c < 4096) :
    quadN 12 Qcols (mvN (gG.getD i one12) c) = quadN 12 Qcols c := by
  interval_cases i
  · exact quadN_gU0 c hc
  · exact quadN_gU1 c hc

theorem quadN_gmv {g : Γ12} (hg : g ∈ G0) {c : ℕ} (hc : c < 4096) :
    quadN 12 Qcols (gmv g c) = quadN 12 Qcols c := by
  let P : Γ12 → Prop := fun g => ∀ c < 4096, quadN 12 Qcols (gmv g c) = quadN 12 Qcols c
  have h1 : P 1 := by
    intro c hc
    rw [gmv_one hc]
  have hstep : ∀ i < 2, ∀ y, P y → P (gU i * y) := by
    intro i hi y hy c hc
    rw [gmv_mul, gmv_gU_eq]
    rw [quadN_gU i hi (gmv y c) (gmv_lt y c)]
    exact hy c hc
  exact G_induction (p := P) h1 hstep hg c hc

theorem polN_gmv {g : Γ12} (hg : g ∈ G0) {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols (gmv g a) (gmv g b) = polN 12 Qcols a b := by
  simp only [polN, ← gmv_xor]
  rw [quadN_gmv hg (Nat.xor_lt_two_pow (n := 12) ha hb), quadN_gmv hg ha, quadN_gmv hg hb]

private theorem polN_omega {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols (mvN z12 a) (mvN z12 b) = polN 12 Qcols a b := by
  have h := polN_gmv (g := zU) zU_mem (a := a) (b := b) ha hb
  rwa [gmv_zU_eq, gmv_zU_eq] at h

private theorem quadOf_polar {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (v w : Fin n → ZMod 2) :
    quadOf Q (v + w) + quadOf Q v + quadOf Q w = v ⬝ᵥ (Q *ᵥ w) + w ⬝ᵥ (Q *ᵥ v) := by
  rw [quadOf, quadOf, quadOf, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  linear_combination (norm := ring_nf) 0
  rw [mul_two, mul_two, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

private theorem polV_add_left {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (u u' w : Fin n → ZMod 2) : polV Q (u + u') w = polV Q u w + polV Q u' w := by
  simp only [polV]
  rw [quadOf_polar, quadOf_polar, quadOf_polar, mulVec_add, dotProduct_add, add_dotProduct]
  linear_combination (norm := ring_nf) 0

private theorem polV_isQuadForm {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (x x' y : Fin n → ZMod 2) :
    quadOf Q (x + x' + y) + quadOf Q (x + x') + quadOf Q y =
      (quadOf Q (x + y) + quadOf Q x + quadOf Q y) +
        (quadOf Q (x' + y) + quadOf Q x' + quadOf Q y) := by
  show polV Q (x + x') y = polV Q x y + polV Q x' y
  exact polV_add_left Q x x' y

theorem polN_nondeg {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) :
    ∃ j < 12, polN 12 Qcols c (2 ^ j) = true := by
  have h : (List.range 4096).all
      (fun c => c == 0 || (List.range 12).any (fun j => polN 12 Qcols c (2 ^ j))) = true := by
    decide +kernel
  have hc' := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simp only [Bool.or_eq_true, beq_iff_eq] at hc'
  rcases hc' with h0 | hany
  · omega
  · obtain ⟨j, hjmem, hj⟩ := List.any_eq_true.mp hany
    exact ⟨j, List.mem_range.mp hjmem, hj⟩

theorem polN_symm (a b : ℕ) : polN 12 Qcols a b = polN 12 Qcols b a := by
  simp only [polN]
  rw [Nat.xor_comm a b]
  rw [Bool.xor_assoc, Bool.xor_assoc,
    Bool.xor_comm (quadN 12 Qcols a) (quadN 12 Qcols b)]

theorem polN_add_left {a a' b : ℕ} (ha : a < 4096) (ha' : a' < 4096) (hb : b < 4096) :
    polN 12 Qcols (a ^^^ a') b = (polN 12 Qcols a b ^^ polN 12 Qcols a' b) := by
  apply CFSG.Quasithin.H13.Mat8Cert.b2z_inj
  rw [CFSG.Quasithin.H13.Mat8Cert.b2z_xor]
  rw [polN_spec Qcols_valid.1, polN_spec Qcols_valid.1, polN_spec Qcols_valid.1, vecN_xor]
  exact polV_add_left (decN 12 Qcols) (vecN 12 a) (vecN 12 a') (vecN 12 b)

private theorem polN_add_right {x a a' : ℕ} (ha : a < 4096) (ha' : a' < 4096)
    (hx : x < 4096) :
    polN 12 Qcols x (a ^^^ a') = (polN 12 Qcols x a ^^ polN 12 Qcols x a') := by
  rw [polN_symm x (a ^^^ a'), polN_symm x a, polN_symm x a']
  exact polN_add_left ha ha' hx

theorem polN_self (a : ℕ) : polN 12 Qcols a a = false := by
  simp only [polN, Nat.xor_self]
  have h0 : quadN 12 Qcols 0 = false := by decide
  rw [h0]
  simp

@[expose] def q0 (v : Vec12) : ZMod 2 :=
  CFSG.Quasithin.H13.L1442M.quadOf (decN 12 Qcols) (Multiplicative.toAdd v)

theorem q0_dc {c : ℕ} (hc : c < 4096) : q0 (dc c) = b2z (quadN 12 Qcols c) := by
  show quadOf (decN 12 Qcols) (vecN 12 c) = b2z (quadN 12 Qcols c)
  exact (quadN_spec Qcols_valid.1 c).symm

theorem isQuadFormOn_q0 : IsQuadFormOn q0 := by
  constructor
  · show quadOf (decN 12 Qcols) (Multiplicative.toAdd (1 : Vec12)) = 0
    rw [show (1 : Vec12) = Multiplicative.ofAdd (0 : Fin 12 → ZMod 2) from rfl, toAdd_ofAdd]
    simp [quadOf]
  · intro x x' y
    show quadOf (decN 12 Qcols) (Multiplicative.toAdd (x * x' * y)) +
        quadOf (decN 12 Qcols) (Multiplicative.toAdd (x * x')) +
        quadOf (decN 12 Qcols) (Multiplicative.toAdd y) =
      (quadOf (decN 12 Qcols) (Multiplicative.toAdd (x * y)) +
          quadOf (decN 12 Qcols) (Multiplicative.toAdd x) +
          quadOf (decN 12 Qcols) (Multiplicative.toAdd y)) +
        (quadOf (decN 12 Qcols) (Multiplicative.toAdd (x' * y)) +
          quadOf (decN 12 Qcols) (Multiplicative.toAdd x') +
          quadOf (decN 12 Qcols) (Multiplicative.toAdd y))
    exact polV_isQuadForm (decN 12 Qcols) (Multiplicative.toAdd x)
      (Multiplicative.toAdd x') (Multiplicative.toAdd y)

private theorem mul_self_vec12 (v : Vec12) : v * v = 1 := by
  rw [← dc_cd v, ← dc_xor, Nat.xor_self, dc_zero]

private theorem sq_mul (v w : Vec12) : v * (v * w) = w := by
  rw [← mul_assoc, mul_self_vec12, one_mul]

private theorem zU_sq_apply (v : Vec12) : glHom zU (glHom zU v) = v * glHom zU v := by
  rw [← dc_cd v, glHom_zU_dc, glHom_zU_dc, omega_sq (cd_lt v), dc_xor]

private theorem f4_add_re (x y : FieldFour) : (x + y).re = (x.re ^^ y.re) := rfl

private theorem f4_add_im (x y : FieldFour) : (x + y).im = (x.im ^^ y.im) := rfl

private theorem f4_mul_re (x y : FieldFour) :
    (x * y).re = ((x.re && y.re) ^^ (x.im && y.im)) := rfl

private theorem f4_mul_im (x y : FieldFour) :
    (x * y).im = (((x.re && y.im) ^^ (x.im && y.re)) ^^ (x.im && y.im)) := rfl

@[expose] def smulV (c : FieldFour) (v : Vec12) : Vec12 :=
  (if c.re then v else 1) * (if c.im then glHom zU v else 1)

private theorem smulV_one_vec (c : FieldFour) : smulV c 1 = 1 := by
  simp [smulV, map_one]

private theorem smulV_dc (c : FieldFour) (a : ℕ) :
    smulV c (dc a) =
      (if c.re then dc a else 1) * (if c.im then dc (mvN z12 a) else 1) := by
  simp only [smulV, glHom_zU_dc]

theorem smulV_one (v : Vec12) : smulV 1 v = v := by
  simp [smulV]

theorem smulV_zero (v : Vec12) : smulV 0 v = 1 := by
  simp [smulV]

theorem smulV_add (c d : FieldFour) (v : Vec12) : smulV (c + d) v = smulV c v * smulV d v := by
  rcases c with ⟨cr, ci⟩
  rcases d with ⟨dr, di⟩
  cases cr <;> cases ci <;> cases dr <;> cases di <;>
    simp only [smulV, f4_add_re, f4_add_im, if_true, if_false, one_mul, mul_one, mul_self_vec12]
  all_goals simp [mul_self_vec12, sq_mul, mul_comm, mul_assoc, mul_left_comm]

theorem smulV_mul (c d : FieldFour) (v : Vec12) : smulV (c * d) v = smulV c (smulV d v) := by
  rcases c with ⟨cr, ci⟩
  rcases d with ⟨dr, di⟩
  cases cr <;> cases ci <;> cases dr <;> cases di <;>
    simp only [smulV, f4_mul_re, f4_mul_im, zU_sq_apply, map_mul, mul_self_vec12, if_true,
      if_false, one_mul, mul_one]
  all_goals simp [mul_self_vec12, sq_mul, mul_comm, mul_assoc, mul_left_comm]

theorem smulV_mul_vec (c : FieldFour) (u v : Vec12) : smulV c (u * v) = smulV c u * smulV c v := by
  rcases c with ⟨cr, ci⟩
  cases cr <;> cases ci <;>
    simp only [smulV, map_mul, if_true, if_false, one_mul, mul_one]
  all_goals simp [mul_self_vec12, sq_mul, mul_comm, mul_assoc, mul_left_comm]

@[expose] def ι0 : FieldFour →+* AddMonoid.End (Additive Vec12) where
  toFun c :=
    { toFun := fun x => Additive.ofMul (smulV c (Additive.toMul x))
      map_zero' := by
        show Additive.ofMul (smulV c (Additive.toMul (0 : Additive Vec12))) = 0
        rw [show Additive.toMul (0 : Additive Vec12) = (1 : Vec12) from rfl, smulV_one_vec]
        rfl
      map_add' := by
        intro a b
        show Additive.ofMul (smulV c (Additive.toMul (a + b))) =
          Additive.ofMul (smulV c (Additive.toMul a)) +
            Additive.ofMul (smulV c (Additive.toMul b))
        rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl]
        rw [show Additive.ofMul (smulV c (Additive.toMul a)) +
              Additive.ofMul (smulV c (Additive.toMul b)) =
            Additive.ofMul (smulV c (Additive.toMul a) * smulV c (Additive.toMul b)) from rfl]
        rw [← smulV_mul_vec] }
  map_one' := AddMonoidHom.ext fun x => by
    show Additive.ofMul (smulV 1 (Additive.toMul x)) = x
    rw [smulV_one]
    rfl
  map_mul' := by
    intro c d
    apply AddMonoidHom.ext
    intro x
    change Additive.ofMul (smulV (c * d) (Additive.toMul x)) =
      Additive.ofMul (smulV c (smulV d (Additive.toMul x)))
    rw [smulV_mul]
  map_zero' := AddMonoidHom.ext fun x => by
    show Additive.ofMul (smulV 0 (Additive.toMul x)) = 0
    rw [smulV_zero]
    rfl
  map_add' := by
    intro c d
    apply AddMonoidHom.ext
    intro x
    show Additive.ofMul (smulV (c + d) (Additive.toMul x)) =
      Additive.ofMul (smulV c (Additive.toMul x)) +
        Additive.ofMul (smulV d (Additive.toMul x))
    rw [smulV_add]
    rfl

theorem kSmul_ι0 (c : FieldFour) (v : Vec12) : kSmul ι0 c v = smulV c v := rfl

@[expose] def f0 (u v : Vec12) : FieldFour :=
  ⟨decide (q0 (glHom zU (glHom zU u) * v) + q0 (glHom zU (glHom zU u)) + q0 v = 1),
    decide (q0 (u * v) + q0 u + q0 v = 1)⟩

private theorem decide_b2z_eq_one (q : Bool) : decide (b2z q = 1) = q := by
  cases q <;> rfl

private theorem quadN_zU {c : ℕ} (hc : c < 4096) :
    quadN 12 Qcols (mvN z12 c) = quadN 12 Qcols c := by
  rw [← gmv_zU_eq c]
  exact quadN_gmv zU_mem hc

private theorem smulV_omega_dc (a : ℕ) : smulV FieldFour.ω (dc a) = dc (mvN z12 a) := by
  rw [smulV_dc]
  simp [FieldFour.ω, Bool.false_eq_true]

theorem f0_dc {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    f0 (dc a) (dc b) =
      ⟨polN 12 Qcols (mvN z12 (mvN z12 a)) b, polN 12 Qcols a b⟩ := by
  apply FieldFour.ext
  · show decide (q0 (glHom zU (glHom zU (dc a)) * dc b) +
        q0 (glHom zU (glHom zU (dc a))) + q0 (dc b) = 1) =
      polN 12 Qcols (mvN z12 (mvN z12 a)) b
    rw [glHom_zU_dc, glHom_zU_dc, ← dc_xor,
      q0_dc (Nat.xor_lt_two_pow (n := 12) (z12_lt (mvN z12 a)) hb),
      q0_dc (z12_lt (mvN z12 a)), q0_dc hb]
    rw [← CFSG.Quasithin.H13.Mat8Cert.b2z_xor, ← CFSG.Quasithin.H13.Mat8Cert.b2z_xor, polN]
    exact decide_b2z_eq_one _
  · show decide (q0 (dc a * dc b) + q0 (dc a) + q0 (dc b) = 1) = polN 12 Qcols a b
    rw [← dc_xor, q0_dc (Nat.xor_lt_two_pow (n := 12) ha hb), q0_dc ha, q0_dc hb,
      ← CFSG.Quasithin.H13.Mat8Cert.b2z_xor, ← CFSG.Quasithin.H13.Mat8Cert.b2z_xor, polN]
    exact decide_b2z_eq_one _

theorem f0_self_dc {c : ℕ} (hc : c < 4096) :
    f0 (dc c) (dc c) = ⟨quadN 12 Qcols c, false⟩ := by
  rw [f0_dc hc hc, polN_self]
  congr 1
  rw [polN]
  have h2 : mvN z12 (mvN z12 c) ^^^ c = mvN z12 c := by
    rw [omega_sq hc]
    simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
  rw [h2, quadN_zU (z12_lt c), quadN_zU hc]
  simp

private theorem f4_sq (x y : Bool) : (⟨x, y⟩ : FieldFour) ^ 2 = ⟨x ^^ y, y⟩ := by
  cases x <;> cases y <;> decide

private theorem quadN_Qcols_zero : quadN 12 Qcols 0 = false := by decide

private theorem polN_zero_left (b : ℕ) : polN 12 Qcols 0 b = false := by
  simp only [polN, Nat.zero_xor, quadN_Qcols_zero, Bool.false_xor]
  cases quadN 12 Qcols b <;> rfl

private theorem polN_zero_right (a : ℕ) : polN 12 Qcols a 0 = false := by
  simp only [polN, Nat.xor_zero, quadN_Qcols_zero, Bool.xor_false]
  cases quadN 12 Qcols a <;> rfl

private theorem polN_omega2 {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols (mvN z12 (mvN z12 a)) (mvN z12 (mvN z12 b)) = polN 12 Qcols a b := by
  have h1 := polN_omega (a := a) (b := b) ha hb
  have h2 := polN_omega (a := mvN z12 a) (b := mvN z12 b) (z12_lt a) (z12_lt b)
  rw [h2, h1]

private theorem key2 {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols a (mvN z12 b) = polN 12 Qcols (mvN z12 (mvN z12 a)) b := by
  nth_rewrite 1 [← omega_cube ha]
  rw [polN_omega (a := mvN z12 (mvN z12 a)) (b := b) (z12_lt (mvN z12 a)) hb]

private theorem keyω {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols (mvN z12 a) b =
      (polN 12 Qcols (mvN z12 (mvN z12 a)) b ^^ polN 12 Qcols a b) := by
  rw [omega_sq ha, polN_add_left ha (z12_lt a) hb]
  cases polN 12 Qcols a b <;> cases polN 12 Qcols (mvN z12 a) b <;> rfl

private theorem key_a_omega2 {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols a (mvN z12 (mvN z12 b)) =
      (polN 12 Qcols (mvN z12 (mvN z12 a)) b ^^ polN 12 Qcols a b) := by
  rw [omega_sq hb, polN_add_right hb (z12_lt b) ha, key2 ha hb]
  cases polN 12 Qcols a b <;> cases polN 12 Qcols (mvN z12 (mvN z12 a)) b <;> rfl

private theorem omega_mul_lit (x y : Bool) :
    (⟨false, true⟩ : FieldFour) * ⟨x, y⟩ = ⟨y, x ^^ y⟩ := by
  cases x <;> cases y <;> decide

private theorem omega2_mul_lit (x y : Bool) :
    (⟨true, true⟩ : FieldFour) * ⟨x, y⟩ = ⟨x ^^ y, x⟩ := by
  cases x <;> cases y <;> decide

private theorem smulV_00_dc (a : ℕ) : smulV (⟨false, false⟩ : FieldFour) (dc a) = 1 := by
  simp [smulV]

private theorem smulV_10_dc (a : ℕ) : smulV (⟨true, false⟩ : FieldFour) (dc a) = dc a := by
  rw [smulV_dc]
  simp

private theorem smulV_01_dc (a : ℕ) :
    smulV (⟨false, true⟩ : FieldFour) (dc a) = dc (mvN z12 a) := by
  rw [smulV_dc]
  simp [glHom_zU_dc]

private theorem smulV_11_dc {a : ℕ} (ha : a < 4096) :
    smulV (⟨true, true⟩ : FieldFour) (dc a) = dc (mvN z12 (mvN z12 a)) := by
  rw [smulV_dc]
  simp only [if_true, one_mul, mul_one, glHom_zU_dc]
  rw [← dc_xor, omega_sq ha]

private abbrev f0c (a b : ℕ) : FieldFour :=
  ⟨polN 12 Qcols (mvN z12 (mvN z12 a)) b, polN 12 Qcols a b⟩

private theorem f0_dc' {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    f0 (dc a) (dc b) = f0c a b := f0_dc ha hb

private theorem gmv_omega2 {g : Γ12} (hg : g ∈ G0) {a : ℕ} (ha : a < 4096) :
    mvN z12 (mvN z12 (gmv g a)) = gmv g (mvN z12 (mvN z12 a)) := by
  rw [← gmv_omega hg ha, ← gmv_omega hg (z12_lt a)]

private theorem f0c_eq (a b : ℕ) :
    f0c a b = ⟨polN 12 Qcols (mvN z12 (mvN z12 a)) b, polN 12 Qcols a b⟩ := rfl

private theorem f0c_gmv {g : Γ12} (hg : g ∈ G0) (a b : ℕ) (ha : a < 4096) (hb : b < 4096) :
    f0c (gmv g a) (gmv g b) = f0c a b := by
  apply FieldFour.ext
  · show polN 12 Qcols (mvN z12 (mvN z12 (gmv g a))) (gmv g b) =
      polN 12 Qcols (mvN z12 (mvN z12 a)) b
    rw [gmv_omega2 hg ha, polN_gmv hg (z12_lt (mvN z12 a)) hb]
  · show polN 12 Qcols (gmv g a) (gmv g b) = polN 12 Qcols a b
    rw [polN_gmv hg ha hb]

private theorem f0c_zero_left (b : ℕ) : f0c 0 b = 0 := by
  simp only [f0c, mvN_zero, polN_zero_left]
  rfl

private theorem f0c_zero_right (a : ℕ) : f0c a 0 = 0 := by
  simp only [f0c, polN_zero_right]
  rfl

private theorem f0c_add_left (a a' b : ℕ) (ha : a < 4096) (ha' : a' < 4096)
    (hb : b < 4096) : f0c (a ^^^ a') b = f0c a b + f0c a' b := by
  apply FieldFour.ext
  · show polN 12 Qcols (mvN z12 (mvN z12 (a ^^^ a'))) b =
      (polN 12 Qcols (mvN z12 (mvN z12 a)) b ^^ polN 12 Qcols (mvN z12 (mvN z12 a')) b)
    rw [mvN_xor, mvN_xor,
      polN_add_left (z12_lt (mvN z12 a)) (z12_lt (mvN z12 a')) hb]
  · show polN 12 Qcols (a ^^^ a') b = (polN 12 Qcols a b ^^ polN 12 Qcols a' b)
    rw [polN_add_left ha ha' hb]

private theorem f0c_add_right (a b b' : ℕ) (ha : a < 4096) (hb : b < 4096)
    (hb' : b' < 4096) : f0c a (b ^^^ b') = f0c a b + f0c a b' := by
  apply FieldFour.ext
  · show polN 12 Qcols (mvN z12 (mvN z12 a)) (b ^^^ b') =
      (polN 12 Qcols (mvN z12 (mvN z12 a)) b ^^ polN 12 Qcols (mvN z12 (mvN z12 a)) b')
    rw [polN_add_right hb hb' (z12_lt (mvN z12 a))]
  · show polN 12 Qcols a (b ^^^ b') = (polN 12 Qcols a b ^^ polN 12 Qcols a b')
    rw [polN_add_right hb hb' ha]

private theorem f0_add_left (u u' v : Vec12) : f0 (u * u') v = f0 u v + f0 u' v := by
  rw [← dc_cd u, ← dc_cd u', ← dc_cd v, ← dc_xor,
    f0_dc' (Nat.xor_lt_two_pow (n := 12) (cd_lt u) (cd_lt u')) (cd_lt v),
    f0_dc' (cd_lt u) (cd_lt v), f0_dc' (cd_lt u') (cd_lt v)]
  exact f0c_add_left (cd u) (cd u') (cd v) (cd_lt u) (cd_lt u') (cd_lt v)

private theorem f0_add_right (u v v' : Vec12) : f0 u (v * v') = f0 u v + f0 u v' := by
  rw [← dc_cd u, ← dc_cd v, ← dc_cd v', ← dc_xor,
    f0_dc' (cd_lt u) (Nat.xor_lt_two_pow (n := 12) (cd_lt v) (cd_lt v')),
    f0_dc' (cd_lt u) (cd_lt v), f0_dc' (cd_lt u) (cd_lt v')]
  exact f0c_add_right (cd u) (cd v) (cd v') (cd_lt u) (cd_lt v) (cd_lt v')

private theorem f0_smul_left_zero (u v : Vec12) :
    f0 (kSmul ι0 (⟨false, false⟩ : FieldFour) u) v =
      (⟨false, false⟩ : FieldFour) * f0 u v := by
  rw [kSmul_ι0, ← dc_cd u, ← dc_cd v, smulV_00_dc,
    show (1 : Vec12) = dc 0 from dc_zero.symm,
    f0_dc' (by norm_num) (cd_lt v), f0_dc' (cd_lt u) (cd_lt v), f0c_zero_left]
  rw [show (⟨false, false⟩ : FieldFour) = 0 from rfl, zero_mul]

private theorem f0_smul_left_one (u v : Vec12) :
    f0 (kSmul ι0 (⟨true, false⟩ : FieldFour) u) v =
      (⟨true, false⟩ : FieldFour) * f0 u v := by
  rw [kSmul_ι0, ← dc_cd u, ← dc_cd v, smulV_10_dc, f0_dc' (cd_lt u) (cd_lt v)]
  change f0c (cd u) (cd v) = (1 : FieldFour) * f0c (cd u) (cd v)
  rw [one_mul]

private theorem f0_smul_left_omega (u v : Vec12) :
    f0 (kSmul ι0 (⟨false, true⟩ : FieldFour) u) v =
      (⟨false, true⟩ : FieldFour) * f0 u v := by
  rw [kSmul_ι0, ← dc_cd u, ← dc_cd v, smulV_01_dc,
    f0_dc' (z12_lt (cd u)) (cd_lt v), f0_dc' (cd_lt u) (cd_lt v)]
  rw [f0c_eq, f0c_eq, omega_mul_lit]
  apply FieldFour.ext
  · show polN 12 Qcols (mvN z12 (mvN z12 (mvN z12 (cd u)))) (cd v) =
      polN 12 Qcols (cd u) (cd v)
    rw [omega_cube (cd_lt u)]
  · show polN 12 Qcols (mvN z12 (cd u)) (cd v) =
      (polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (cd v) ^^ polN 12 Qcols (cd u) (cd v))
    rw [keyω (cd_lt u) (cd_lt v)]

private theorem f0_smul_left_omega2 (u v : Vec12) :
    f0 (kSmul ι0 (⟨true, true⟩ : FieldFour) u) v =
      (⟨true, true⟩ : FieldFour) * f0 u v := by
  rw [kSmul_ι0, ← dc_cd u, ← dc_cd v, smulV_11_dc (cd_lt u),
    f0_dc' (z12_lt (mvN z12 (cd u))) (cd_lt v), f0_dc' (cd_lt u) (cd_lt v)]
  rw [f0c_eq, f0c_eq, omega2_mul_lit]
  apply FieldFour.ext
  · show polN 12 Qcols (mvN z12 (mvN z12 (mvN z12 (mvN z12 (cd u))))) (cd v) =
      (polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (cd v) ^^ polN 12 Qcols (cd u) (cd v))
    rw [omega_cube (z12_lt (cd u)), keyω (cd_lt u) (cd_lt v)]
  · show polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (cd v) =
      polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (cd v)
    rfl

private theorem f0_smul_left (c : FieldFour) (u v : Vec12) :
    f0 (kSmul ι0 c u) v = c * f0 u v := by
  rcases c with ⟨re, im⟩
  cases re <;> cases im
  · exact f0_smul_left_zero u v
  · exact f0_smul_left_omega u v
  · exact f0_smul_left_one u v
  · exact f0_smul_left_omega2 u v

private theorem f0_smul_right_zero (u v : Vec12) :
    f0 u (kSmul ι0 (⟨false, false⟩ : FieldFour) v) =
      (⟨false, false⟩ : FieldFour) ^ 2 * f0 u v := by
  rw [kSmul_ι0, ← dc_cd u, ← dc_cd v, smulV_00_dc,
    show (1 : Vec12) = dc 0 from dc_zero.symm,
    f0_dc' (cd_lt u) (by norm_num), f0_dc' (cd_lt u) (cd_lt v), f0c_zero_right,
    show (⟨false, false⟩ : FieldFour) = 0 from rfl, pow_two, zero_mul, zero_mul]

private theorem f0_smul_right_one (u v : Vec12) :
    f0 u (kSmul ι0 (⟨true, false⟩ : FieldFour) v) =
      (⟨true, false⟩ : FieldFour) ^ 2 * f0 u v := by
  rw [kSmul_ι0, ← dc_cd u, ← dc_cd v, smulV_10_dc, f0_dc' (cd_lt u) (cd_lt v),
    show (⟨true, false⟩ : FieldFour) ^ 2 = 1 from by decide, one_mul]

private theorem f0_smul_right_omega (u v : Vec12) :
    f0 u (kSmul ι0 (⟨false, true⟩ : FieldFour) v) =
      (⟨false, true⟩ : FieldFour) ^ 2 * f0 u v := by
  rw [kSmul_ι0, ← dc_cd u, ← dc_cd v, smulV_01_dc,
    f0_dc' (cd_lt u) (z12_lt (cd v)), f0_dc' (cd_lt u) (cd_lt v),
    show (⟨false, true⟩ : FieldFour) ^ 2 = ⟨true, true⟩ from by decide]
  rw [f0c_eq, f0c_eq, omega2_mul_lit]
  apply FieldFour.ext
  · show polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (mvN z12 (cd v)) =
      (polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (cd v) ^^ polN 12 Qcols (cd u) (cd v))
    rw [polN_omega (z12_lt (cd u)) (cd_lt v), keyω (cd_lt u) (cd_lt v)]
  · show polN 12 Qcols (cd u) (mvN z12 (cd v)) =
      polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (cd v)
    rw [key2 (cd_lt u) (cd_lt v)]

private theorem f0_smul_right_omega2 (u v : Vec12) :
    f0 u (kSmul ι0 (⟨true, true⟩ : FieldFour) v) =
      (⟨true, true⟩ : FieldFour) ^ 2 * f0 u v := by
  rw [kSmul_ι0, ← dc_cd u, ← dc_cd v, smulV_11_dc (cd_lt v),
    f0_dc' (cd_lt u) (z12_lt (mvN z12 (cd v))), f0_dc' (cd_lt u) (cd_lt v),
    show (⟨true, true⟩ : FieldFour) ^ 2 = ⟨false, true⟩ from by decide]
  rw [f0c_eq, f0c_eq, omega_mul_lit]
  apply FieldFour.ext
  · show polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (mvN z12 (mvN z12 (cd v))) =
      polN 12 Qcols (cd u) (cd v)
    rw [polN_omega2 (cd_lt u) (cd_lt v)]
  · show polN 12 Qcols (cd u) (mvN z12 (mvN z12 (cd v))) =
      (polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (cd v) ^^ polN 12 Qcols (cd u) (cd v))
    rw [key_a_omega2 (cd_lt u) (cd_lt v)]

private theorem f0_smul_right (c : FieldFour) (u v : Vec12) :
    f0 u (kSmul ι0 c v) = c ^ 2 * f0 u v := by
  rcases c with ⟨re, im⟩
  cases re <;> cases im
  · exact f0_smul_right_zero u v
  · exact f0_smul_right_omega u v
  · exact f0_smul_right_one u v
  · exact f0_smul_right_omega2 u v

private theorem f0_herm (u v : Vec12) : f0 v u = f0 u v ^ 2 := by
  rw [← dc_cd u, ← dc_cd v, f0_dc' (cd_lt v) (cd_lt u), f0_dc' (cd_lt u) (cd_lt v),
    f0c_eq, f4_sq]
  apply FieldFour.ext
  · show polN 12 Qcols (mvN z12 (mvN z12 (cd v))) (cd u) =
      (polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (cd v) ^^ polN 12 Qcols (cd u) (cd v))
    rw [polN_symm (mvN z12 (mvN z12 (cd v))) (cd u), key_a_omega2 (cd_lt u) (cd_lt v)]
  · show polN 12 Qcols (cd v) (cd u) = polN 12 Qcols (cd u) (cd v)
    rw [polN_symm (cd v) (cd u)]

private theorem f0_nondeg (u : Vec12) (hu : u ≠ 1) : ∃ v : Vec12, f0 u v ≠ 0 := by
  rw [← dc_cd u] at hu ⊢
  have hc : cd u < 4096 := cd_lt u
  have hc0 : 0 < cd u := by
    by_contra h
    have h0 : cd u = 0 := Nat.eq_zero_of_not_pos h
    exact hu (by rw [h0, dc_zero])
  obtain ⟨j, hj, hp⟩ := polN_nondeg hc0 hc
  have hj' : 2 ^ j < 4096 := by
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hj
    simpa using this
  refine ⟨dc (2 ^ j), ?_⟩
  rw [f0_dc hc hj', hp]
  intro h
  have him := congrArg FieldFour.im h
  simp at him

theorem isUnitaryForm_f0 : IsUnitaryForm ι0 f0 :=
  ⟨f0_add_left, f0_add_right, f0_smul_left, f0_smul_right, f0_herm, f0_nondeg⟩

private theorem glHom_comm_zU {g : Γ12} (hg : g ∈ G0) (v : Vec12) :
    glHom g (glHom zU v) = glHom zU (glHom g v) := by
  have h1 : glHom (g * zU) v = glHom g (glHom zU v) := by
    rw [map_mul, MulAut.mul_apply]
  have h2 : glHom (zU * g) v = glHom zU (glHom g v) := by
    rw [map_mul, MulAut.mul_apply]
  rw [← h1, zU_comm hg, h2]

theorem formClause_G0 : FormClause glHom G0 ι0 f0 := by
  refine ⟨isUnitaryForm_f0, ?_, ?_⟩
  · intro g hg
    refine ⟨?_, ?_⟩
    · intro c v
      rw [kSmul_ι0, kSmul_ι0]
      rcases c with ⟨re, im⟩
      cases re <;> cases im
      · exact map_one (glHom g)
      · simp only [smulV, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, one_mul]
        exact glHom_comm_zU hg v
      · simp only [smulV, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false,
          mul_one]
      · simp only [smulV, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false,
          one_mul, mul_one]
        calc glHom g (v * glHom zU v)
            = glHom g v * glHom g (glHom zU v) := map_mul (glHom g) v (glHom zU v)
          _ = glHom g v * glHom zU (glHom g v) :=
              congrArg (fun w => glHom g v * w) (glHom_comm_zU hg v)
    · intro u v
      rw [← dc_cd u, ← dc_cd v]
      have h : f0 (glHom g (dc (cd u))) (glHom g (dc (cd v))) =
          f0 (dc (gmv g (cd u))) (dc (gmv g (cd v))) :=
        congrArg₂ f0 (glHom_dc g (cd u)) (glHom_dc g (cd v))
      refine h.trans ?_
      rw [f0_dc (gmv_lt g (cd u)) (gmv_lt g (cd v)), f0_dc (cd_lt u) (cd_lt v)]
      exact f0c_gmv hg (cd u) (cd v) (cd_lt u) (cd_lt v)
  · refine ⟨q0, isQuadFormOn_q0, ?_, ?_, ?_⟩
    · intro u
      rw [← dc_cd u, f0_self_dc (cd_lt u)]
      cases quadN 12 Qcols (cd u) <;> decide
    · intro u
      rw [← dc_cd u, q0_dc (cd_lt u), f0_self_dc (cd_lt u)]
      cases quadN 12 Qcols (cd u) <;> decide
    · intro g hg u
      rw [← dc_cd u]
      have h : q0 (glHom g (dc (cd u))) = q0 (dc (gmv g (cd u))) :=
        congrArg q0 (glHom_dc g (cd u))
      refine h.trans ?_
      rw [q0_dc (gmv_lt g (cd u)), q0_dc (cd_lt u), quadN_gmv hg (cd_lt u)]

theorem kLine_dc (c : ℕ) : kLine ι0 (dc c) = ptSub c := by
  apply le_antisymm
  · change Subgroup.closure {x | ∃ c', x = kSmul ι0 c' (dc c)} ≤ ptSub c
    rw [Subgroup.closure_le]
    rintro x ⟨c', rfl⟩
    rw [kSmul_ι0, smulV_dc, ptSub, spanSub]
    rcases c' with ⟨re, im⟩
    cases re <;> cases im <;> simp only [smulV, glHom_zU_dc, Bool.false_eq_true,
      Bool.true_eq_false, if_true, if_false, one_mul, mul_one]
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨mvN z12 c, by simp, rfl⟩
    · exact Subgroup.subset_closure ⟨c, by simp, rfl⟩
    · exact Subgroup.mul_mem _
        (Subgroup.subset_closure ⟨c, by simp, rfl⟩)
        (Subgroup.subset_closure ⟨mvN z12 c, by simp, rfl⟩)
  · change ptSub c ≤ Subgroup.closure {x | ∃ c', x = kSmul ι0 c' (dc c)}
    rw [ptSub, spanSub, Subgroup.closure_le]
    rintro x ⟨d, hd, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact Subgroup.subset_closure ⟨1, by rw [kSmul_ι0, smulV_one]⟩
    · exact Subgroup.subset_closure ⟨FieldFour.ω, by rw [kSmul_ι0]; exact (smulV_omega_dc c).symm⟩

theorem isIsoPoint_iff (P : Subgroup Vec12) :
    IsIsoPoint ι0 f0 P ↔
      ∃ c : ℕ, 0 < c ∧ c < 4096 ∧ quadN 12 Qcols c = false ∧ P = ptSub c := by
  constructor
  · rintro ⟨v, hv, hf, hP⟩
    refine ⟨cd v, ?_, cd_lt v, ?_, ?_⟩
    · by_contra hlt
      have h0 : cd v = 0 := Nat.eq_zero_of_not_pos hlt
      exact hv (by rw [← dc_cd v, h0, dc_zero]; rfl)
    · rw [← dc_cd v] at hf
      rw [f0_self_dc (cd_lt v)] at hf
      exact congrArg FieldFour.re hf
    · rw [hP]
      exact (congrArg (fun w => kLine ι0 w) (dc_cd v)).symm.trans (kLine_dc (cd v))
  · rintro ⟨c, hc0, hc, hq, rfl⟩
    refine ⟨dc c, ?_, ?_, (kLine_dc c).symm⟩
    · intro h
      have h' : dc c = dc 0 := h.trans dc_zero.symm
      exact absurd (dc_inj hc (by norm_num) h') (ne_of_gt hc0)
    · rw [f0_self_dc hc, hq]
      rfl

theorem isIsoPoint_ptSub {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) (hq : quadN 12 Qcols c = false) :
    IsIsoPoint ι0 f0 (ptSub c) :=
  (isIsoPoint_iff _).mpr ⟨c, hc0, hc, hq, rfl⟩

end CFSG.Quasithin.AppendixH.H12.Model
