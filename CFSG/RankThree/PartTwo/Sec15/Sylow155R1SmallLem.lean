module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.Permutation.AlternatingAutomorphism.Conjugation

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

private theorem zmod_seven_eq_one_of_pow_eq_one {u : ZMod 7} (hu : u ≠ 0) {n : ℕ}
    (hn : Nat.Coprime n 6) (h : u ^ n = 1) : u = 1 := by
  have h6 : ∀ v : ZMod 7, v ≠ 0 → v ^ 6 = 1 := by decide +kernel
  have hd := (pow_gcd_eq_one (a := u) (m := n) (n := 6)).2 ⟨h, h6 u hu⟩
  rwa [hn, pow_one] at hd

private theorem pow_eq_self_of_orbit {Y : Type} [Group Y] {α : MulAut Y} {x : Y}
    (hx : orderOf x = 7) {j : ℕ} (hj : j < 7) (hj0 : j ≠ 0) (hαx : α x = x ^ j)
    (hα : Nat.Coprime (orderOf α) 6) : α x = x := by
  have hpow : ∀ n : ℕ, (α ^ n) x = x ^ (j ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hαx, map_pow, ih, ← pow_mul, pow_succ]
  have h1 : x ^ (j ^ orderOf α) = x ^ 1 := by
    rw [← hpow, pow_orderOf_eq_one, MulAut.one_apply, pow_one]
  rw [pow_eq_pow_iff_modEq, hx] at h1
  have h2 : ((j : ℕ) : ZMod 7) ^ orderOf α = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
    simpa using this
  have hu : ((j : ℕ) : ZMod 7) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hj0 (Nat.eq_zero_of_dvd_of_lt h hj)
  have h3 := zmod_seven_eq_one_of_pow_eq_one hu hα h2
  have h4 : j = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (h3.trans (Nat.cast_one).symm)
    rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by norm_num)] at this
  rw [hαx, h4, pow_one]

private theorem eq_one_of_fix_frame {Y : Type} [Group Y] {α : MulAut Y} {y x₁ x₂ : Y}
    (hα : Nat.Coprime (orderOf α) 6) (hαy : α y = y)
    (hx₁ : orderOf x₁ = 7) (hx₂ : orderOf x₂ = 7)
    (h₁ : y * x₁ = x₁ ^ 2 * y) (h₂ : y * x₂ = x₂ ^ 4 * y)
    (u₁ : ∀ q : Y, orderOf q = 7 → y * q = q ^ 2 * y → ∃ j < 7, q = x₁ ^ j)
    (u₂ : ∀ q : Y, orderOf q = 7 → y * q = q ^ 4 * y → ∃ j < 7, q = x₂ ^ j)
    (hgen : Subgroup.closure ({x₁, x₂} : Set Y) = ⊤) : α = 1 := by
  have key : ∀ (x : Y) (e : ℕ), orderOf x = 7 → y * x = x ^ e * y →
      (∀ q : Y, orderOf q = 7 → y * q = q ^ e * y → ∃ j < 7, q = x ^ j) → α x = x := by
    intro x e hx hxe u
    have hq7 : orderOf (α x) = 7 := by rw [MulEquiv.orderOf_eq]; exact hx
    have hqe : y * α x = (α x) ^ e * y := by
      have := congrArg α hxe
      simpa [map_mul, map_pow, hαy] using this
    obtain ⟨j, hj, hjx⟩ := u (α x) hq7 hqe
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hjx
      rw [hjx, orderOf_one] at hq7
      omega
    exact pow_eq_self_of_orbit hx hj hj0 hjx hα
  have hf1 := key x₁ 2 hx₁ h₁ u₁
  have hf2 := key x₂ 4 hx₂ h₂ u₂
  have hle : Subgroup.closure ({x₁, x₂} : Set Y) ≤
      MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y) := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hf1
    · exact hf2
  rw [hgen] at hle
  exact MulEquiv.ext fun g => hle (Subgroup.mem_top g)

section Alt5

open Equiv Equiv.Perm

private theorem perm5_eq_one_of_commute_even : ∀ σ : Perm (Fin 5),
    (∀ g : Perm (Fin 5), Perm.sign g = 1 → σ * g = g * σ) → σ = 1 := by
  decide +kernel

private theorem perm5_pow_six_of_commute : ∀ σ y : Perm (Fin 5),
    y ^ 3 = 1 → y ≠ 1 → σ * y = y * σ → σ ^ 6 = 1 := by
  decide +kernel

theorem alt5_aut_eq_one (α : MulAut (alternatingGroup (Fin 5))) (y : alternatingGroup (Fin 5))
    (hy : orderOf y = 3) (hα : Nat.Coprime (orderOf α) 6) (hαy : α y = y) : α = 1 := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (n := 5) (Or.inl rfl) α
  have hpow : ∀ (n : ℕ) (g : alternatingGroup (Fin 5)),
      (((α ^ n) g : alternatingGroup (Fin 5)) : Perm (Fin 5)) = σ ^ n * g * (σ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ, MulAut.mul_apply, ih, hσ]
      group
  have hk : σ ^ orderOf α = 1 := by
    apply perm5_eq_one_of_commute_even
    intro g hg
    have h := hpow (orderOf α) ⟨g, (Equiv.Perm.mem_alternatingGroup).2 hg⟩
    rw [pow_orderOf_eq_one] at h
    simp only [MulAut.one_apply] at h
    have h' : (g : Perm (Fin 5)) = σ ^ orderOf α * g * (σ ^ orderOf α)⁻¹ := h
    calc σ ^ orderOf α * g = (σ ^ orderOf α * g * (σ ^ orderOf α)⁻¹) * σ ^ orderOf α := by group
      _ = g * σ ^ orderOf α := by rw [← h']
  have hy3 : (y : Perm (Fin 5)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    simpa using congrArg Subtype.val this
  have hy1 : (y : Perm (Fin 5)) ≠ 1 := by
    intro h
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy
    omega
  have hcomm : σ * (y : Perm (Fin 5)) = (y : Perm (Fin 5)) * σ := by
    have h := hσ y
    rw [hαy] at h
    calc σ * (y : Perm (Fin 5)) = (σ * y * σ⁻¹) * σ := by group
      _ = y * σ := by rw [← h]
  have h6 := perm5_pow_six_of_commute σ y hy3 hy1 hcomm
  have hσ1 : σ = 1 := by
    have := (pow_gcd_eq_one (a := σ) (m := 6) (n := orderOf α)).2 ⟨h6, hk⟩
    rwa [Nat.gcd_comm, hα, pow_one] at this
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [hσ, hσ1]
  simp

end Alt5

section SL3

open Matrix

private abbrev M3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)
private abbrev S3 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

private def z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem z_xor : ∀ p q : Bool, z (xor p q) = z p + z q := by decide +kernel
private theorem z_and : ∀ p q : Bool, z (p && q) = z p * z q := by decide +kernel

private structure B9 where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool
  g : Bool
  h : Bool
  i : Bool
  deriving DecidableEq

private def B9.toM (x : B9) : M3 :=
  !![z x.a, z x.b, z x.c; z x.d, z x.e, z x.f; z x.g, z x.h, z x.i]

private def B9.mul (x y : B9) : B9 :=
  ⟨xor (xor (x.a && y.a) (x.b && y.d)) (x.c && y.g),
   xor (xor (x.a && y.b) (x.b && y.e)) (x.c && y.h),
   xor (xor (x.a && y.c) (x.b && y.f)) (x.c && y.i),
   xor (xor (x.d && y.a) (x.e && y.d)) (x.f && y.g),
   xor (xor (x.d && y.b) (x.e && y.e)) (x.f && y.h),
   xor (xor (x.d && y.c) (x.e && y.f)) (x.f && y.i),
   xor (xor (x.g && y.a) (x.h && y.d)) (x.i && y.g),
   xor (xor (x.g && y.b) (x.h && y.e)) (x.i && y.h),
   xor (xor (x.g && y.c) (x.h && y.f)) (x.i && y.i)⟩

private def B9.one : B9 := ⟨true, false, false, false, true, false, false, false, true⟩

private def B9.pow (x : B9) : ℕ → B9
  | 0 => B9.one
  | n + 1 => (x.pow n).mul x

private def B9.det (x : B9) : Bool :=
  xor (xor (xor (xor (xor (x.a && x.e && x.i) (x.a && x.f && x.h)) (x.b && x.d && x.i))
    (x.b && x.f && x.g)) (x.c && x.d && x.h)) (x.c && x.e && x.g)

private theorem toM_mul (x y : B9) : (x.mul y).toM = x.toM * y.toM := by
  simp only [B9.toM, Matrix.mul_fin_three, B9.mul, z_xor, z_and]

private theorem toM_one : B9.one.toM = 1 := by
  simp [B9.toM, B9.one, z, Matrix.one_fin_three]

private theorem toM_pow (x : B9) (n : ℕ) : (x.pow n).toM = x.toM ^ n := by
  induction n with
  | zero => simp [B9.pow, toM_one]
  | succ n ih => rw [B9.pow, toM_mul, ih, pow_succ]

private theorem det_toM (x : B9) : x.toM.det = z x.det := by
  rw [B9.toM, Matrix.det_fin_three]
  simp [B9.det, z_xor, z_and, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  ring

private def ofZ (t : ZMod 2) : Bool := decide (t = 1)

private theorem ofZ_z : ∀ b : Bool, ofZ (z b) = b := by decide +kernel
private theorem z_ofZ : ∀ t : ZMod 2, z (ofZ t) = t := by decide +kernel

private def ofM (A : M3) : B9 :=
  ⟨ofZ (A 0 0), ofZ (A 0 1), ofZ (A 0 2), ofZ (A 1 0), ofZ (A 1 1), ofZ (A 1 2), ofZ (A 2 0),
    ofZ (A 2 1), ofZ (A 2 2)⟩

private theorem toM_ofM (A : M3) : (ofM A).toM = A := by
  simp only [ofM, B9.toM, z_ofZ]
  exact (Matrix.eta_fin_three A).symm

private theorem ofM_toM (x : B9) : ofM x.toM = x := by
  cases x
  simp [ofM, B9.toM, ofZ_z]

private theorem toM_inj {x y : B9} (h : x.toM = y.toM) : x = y := by
  rw [← ofM_toM x, h, ofM_toM]

private theorem b9_induction {P : B9 → Prop}
    (h : ∀ a b c d e f g h i : Bool, P ⟨a, b, c, d, e, f, g, h, i⟩) (x : B9) : P x := by
  cases x
  exact h _ _ _ _ _ _ _ _ _

private def y0b : B9 := ⟨false, false, true, true, false, false, false, true, false⟩
private def x1b : B9 := ⟨false, false, true, false, true, true, true, true, true⟩
private def x2b : B9 := ⟨false, false, true, false, true, true, true, true, false⟩

private theorem data_okB : y0b.pow 3 = B9.one ∧ y0b ≠ B9.one ∧ x1b.pow 7 = B9.one ∧
    x1b ≠ B9.one ∧ x2b.pow 7 = B9.one ∧ x2b ≠ B9.one ∧ y0b.mul x1b = (x1b.pow 2).mul y0b ∧
    y0b.mul x2b = (x2b.pow 4).mul y0b ∧ y0b.det = true ∧ x1b.det = true ∧ x2b.det = true := by
  decide +kernel

private theorem uniqB₁ (q : B9) : y0b.mul q = (q.pow 2).mul y0b → q.pow 7 = B9.one →
    q ≠ B9.one → ∃ j < 7, q = x1b.pow j := by
  refine b9_induction (P := fun q => y0b.mul q = (q.pow 2).mul y0b → q.pow 7 = B9.one →
    q ≠ B9.one → ∃ j < 7, q = x1b.pow j) ?_ q
  decide +kernel

private theorem uniqB₂ (q : B9) : y0b.mul q = (q.pow 4).mul y0b → q.pow 7 = B9.one →
    q ≠ B9.one → ∃ j < 7, q = x2b.pow j := by
  refine b9_induction (P := fun q => y0b.mul q = (q.pow 4).mul y0b → q.pow 7 = B9.one →
    q ≠ B9.one → ∃ j < 7, q = x2b.pow j) ?_ q
  decide +kernel

private def tlistB : List B9 :=
  (List.range 7).flatMap fun u => (List.range 7).map fun v => (x2b.pow u).mul (x1b.pow v)

private theorem genB (q : B9) : q.det = true →
    ∃ p < 7, ∃ s < 7, ((x1b.pow (7 - p)).mul q).mul (x2b.pow (7 - s)) ∈ tlistB := by
  refine b9_induction (P := fun q => q.det = true →
    ∃ p < 7, ∃ s < 7, ((x1b.pow (7 - p)).mul q).mul (x2b.pow (7 - s)) ∈ tlistB) ?_ q
  decide +kernel

private theorem conjB (q : B9) : q.pow 3 = B9.one → q ≠ B9.one →
    ∃ a b c d e f g h i : Bool, (B9.mk a b c d e f g h i).det = true ∧
      (B9.mk a b c d e f g h i).mul y0b = q.mul (B9.mk a b c d e f g h i) := by
  refine b9_induction (P := fun q => q.pow 3 = B9.one → q ≠ B9.one →
    ∃ a b c d e f g h i : Bool, (B9.mk a b c d e f g h i).det = true ∧
      (B9.mk a b c d e f g h i).mul y0b = q.mul (B9.mk a b c d e f g h i)) ?_ q
  decide +kernel

private def Φ (g : S3) : B9 := ofM g.1

private theorem toM_Φ (g : S3) : (Φ g).toM = g.1 := toM_ofM g.1

private theorem Φ_mul (g h : S3) : Φ (g * h) = (Φ g).mul (Φ h) := by
  apply toM_inj
  rw [toM_mul, toM_Φ, toM_Φ, toM_Φ, Matrix.SpecialLinearGroup.coe_mul]

private theorem Φ_pow (g : S3) (n : ℕ) : Φ (g ^ n) = (Φ g).pow n := by
  apply toM_inj
  rw [toM_pow, toM_Φ, toM_Φ, Matrix.SpecialLinearGroup.coe_pow]

private theorem Φ_one : Φ (1 : S3) = B9.one := by
  apply toM_inj
  rw [toM_one, toM_Φ, Matrix.SpecialLinearGroup.coe_one]

private theorem Φ_inj : Function.Injective Φ := by
  intro g h e
  apply Subtype.ext
  rw [← toM_Φ g, ← toM_Φ h, e]

private theorem det_Φ (g : S3) : (Φ g).det = true := by
  have h := g.2
  rw [← toM_Φ, det_toM] at h
  cases hd : (Φ g).det
  · rw [hd] at h
    exact absurd h (by decide)
  · rfl

private def B9.toS3 (x : B9) (h : x.det = true) : S3 :=
  ⟨x.toM, by rw [det_toM, h]; rfl⟩

private theorem Φ_toS3 (x : B9) (h : x.det = true) : Φ (x.toS3 h) = x := ofM_toM x

private def y0 : S3 := y0b.toS3 (by decide +kernel)
private def x1 : S3 := x1b.toS3 (by decide +kernel)
private def x2 : S3 := x2b.toS3 (by decide +kernel)

private theorem Φ_y0 : Φ y0 = y0b := Φ_toS3 _ _
private theorem Φ_x1 : Φ x1 = x1b := Φ_toS3 _ _
private theorem Φ_x2 : Φ x2 = x2b := Φ_toS3 _ _

private theorem y0_x1 : y0 * x1 = x1 ^ 2 * y0 := by
  apply Φ_inj
  rw [Φ_mul, Φ_mul, Φ_pow, Φ_y0, Φ_x1]
  exact data_okB.2.2.2.2.2.2.1

private theorem y0_x2 : y0 * x2 = x2 ^ 4 * y0 := by
  apply Φ_inj
  rw [Φ_mul, Φ_mul, Φ_pow, Φ_y0, Φ_x2]
  exact data_okB.2.2.2.2.2.2.2.1

private theorem x1_pow_seven : x1 ^ 7 = 1 := by
  apply Φ_inj
  rw [Φ_pow, Φ_x1, Φ_one]
  exact data_okB.2.2.1

private theorem x2_pow_seven : x2 ^ 7 = 1 := by
  apply Φ_inj
  rw [Φ_pow, Φ_x2, Φ_one]
  exact data_okB.2.2.2.2.1

private theorem x1_ne_one : x1 ≠ 1 := by
  intro h
  apply data_okB.2.2.2.1
  rw [← Φ_x1, h, Φ_one]

private theorem x2_ne_one : x2 ≠ 1 := by
  intro h
  apply data_okB.2.2.2.2.2.1
  rw [← Φ_x2, h, Φ_one]

private theorem sl3_fix_frame (α : MulAut S3) (hα : Nat.Coprime (orderOf α) 6)
    (hαy : α y0 = y0) : α = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine eq_one_of_fix_frame hα hαy (orderOf_eq_prime x1_pow_seven x1_ne_one)
    (orderOf_eq_prime x2_pow_seven x2_ne_one) y0_x1 y0_x2 ?_ ?_ ?_
  · intro q hq hc
    have hq7 : q ^ 7 = 1 := by
      have := pow_orderOf_eq_one q
      rwa [hq] at this
    have h7 : (Φ q).pow 7 = B9.one := by rw [← Φ_pow, hq7, Φ_one]
    have h1 : Φ q ≠ B9.one := by
      intro h
      have : q = 1 := Φ_inj (h.trans Φ_one.symm)
      rw [this, orderOf_one] at hq
      omega
    have hc' := congrArg Φ hc
    rw [Φ_mul, Φ_mul, Φ_pow, Φ_y0] at hc'
    obtain ⟨j, hj, hjq⟩ := uniqB₁ (Φ q) hc' h7 h1
    exact ⟨j, hj, Φ_inj (by rw [hjq, Φ_pow, Φ_x1])⟩
  · intro q hq hc
    have hq7 : q ^ 7 = 1 := by
      have := pow_orderOf_eq_one q
      rwa [hq] at this
    have h7 : (Φ q).pow 7 = B9.one := by rw [← Φ_pow, hq7, Φ_one]
    have h1 : Φ q ≠ B9.one := by
      intro h
      have : q = 1 := Φ_inj (h.trans Φ_one.symm)
      rw [this, orderOf_one] at hq
      omega
    have hc' := congrArg Φ hc
    rw [Φ_mul, Φ_mul, Φ_pow, Φ_y0] at hc'
    obtain ⟨j, hj, hjq⟩ := uniqB₂ (Φ q) hc' h7 h1
    exact ⟨j, hj, Φ_inj (by rw [hjq, Φ_pow, Φ_x2])⟩
  · rw [eq_top_iff]
    intro g _
    obtain ⟨p, hp, s, hs, hmem⟩ := genB (Φ g) (det_Φ g)
    simp only [tlistB, List.mem_flatMap, List.mem_map, List.mem_range] at hmem
    obtain ⟨u, hu, v, hv, huv⟩ := hmem
    have hS : x1 ^ (7 - p) * g * x2 ^ (7 - s) = x2 ^ u * x1 ^ v := by
      apply Φ_inj
      simp only [Φ_mul, Φ_pow, Φ_x1, Φ_x2]
      exact huv.symm
    have e1 : x1 ^ p * x1 ^ (7 - p) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hp.le, x1_pow_seven]
    have e2 : x2 ^ (7 - s) * x2 ^ s = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hs.le, x2_pow_seven]
    have hg : g = x1 ^ p * (x2 ^ u * x1 ^ v) * x2 ^ s := by
      rw [← hS]
      calc g = (x1 ^ p * x1 ^ (7 - p)) * g * (x2 ^ (7 - s) * x2 ^ s) := by
            rw [e1, e2, one_mul, mul_one]
        _ = x1 ^ p * (x1 ^ (7 - p) * g * x2 ^ (7 - s)) * x2 ^ s := by simp only [mul_assoc]
    rw [hg]
    have h1 : x1 ∈ Subgroup.closure ({x1, x2} : Set S3) := Subgroup.subset_closure (by simp)
    have h2 : x2 ∈ Subgroup.closure ({x1, x2} : Set S3) := Subgroup.subset_closure (by simp)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ h1 _)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ h2 _) (Subgroup.pow_mem _ h1 _)))
      (Subgroup.pow_mem _ h2 _)

theorem sl3_two_aut_eq_one (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (y : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hy : orderOf y = 3)
    (hα : Nat.Coprime (orderOf α) 6) (hαy : α y = y) : α = 1 := by
  have hy3 : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    omega
  obtain ⟨a, b, c, d, e, f, g, h, i, hdet, hcomm⟩ := conjB (Φ y)
    (by rw [← Φ_pow, hy3, Φ_one]) (fun h => hy1 (Φ_inj (h.trans Φ_one.symm)))
  obtain ⟨P, hΦP⟩ : ∃ P : S3, Φ P = B9.mk a b c d e f g h i := ⟨_, Φ_toS3 _ hdet⟩
  have hPy : P * y0 = y * P := by
    apply Φ_inj
    rw [Φ_mul, Φ_mul, hΦP, Φ_y0]
    exact hcomm
  have hcy : MulAut.conj P y0 = y := by
    rw [MulAut.conj_apply, hPy, mul_inv_cancel_right]
  obtain ⟨β, hβ⟩ : ∃ β : MulAut S3, β = (MulAut.conj P)⁻¹ * α * MulAut.conj P := ⟨_, rfl⟩
  have hβy : β y0 = y0 := by
    rw [hβ, MulAut.mul_apply, MulAut.mul_apply, hcy, hαy, ← hcy, MulAut.inv_apply_self]
  have hβo : orderOf β = orderOf α := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj (MulAut.conj P)⁻¹) α, MulAut.conj_apply, hβ, inv_inv]
  have hβ1 : β = 1 := sl3_fix_frame β (by rwa [hβo]) hβy
  calc α = MulAut.conj P * β * (MulAut.conj P)⁻¹ := by rw [hβ]; group
    _ = 1 := by rw [hβ1]; group

end SL3

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
