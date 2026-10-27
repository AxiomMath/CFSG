module

public import CFSG.Quasithin.Background.SmithB42D4Rel
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.Quasithin.B42D4

open scoped commutatorElement

theorem ofNat_char2 {R : Type*} [AddGroupWithOne R] [CharP R 2] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : R) = ((n % 2 : ℕ) : R) := by
  rw [← Nat.cast_ofNat, CharP.natCast_eq_natCast R 2]
  exact (Nat.mod_modEq _ _).symm

macro "ring2" : tactic =>
  `(tactic| ((try simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]) <;> ring_nf <;>
    (try simp only [ofNat_char2, Nat.reduceMod, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero,
      one_mul, zero_mul, add_zero, zero_add, neg_zero])))

section Abstract

variable {G : Type*} [Group G]

theorem swap_of_commute {x y : G} (h : Commute x y) (r : G) : x * (y * r) = y * (x * r) :=
  h.left_comm r

theorem swap_of_rel {x y z : G} (h : x * y = y * x * z) (r : G) :
    x * (y * r) = y * (x * (z * r)) := by
  rw [← mul_assoc, h, mul_assoc, mul_assoc]

theorem conj_eq_of_comm_left {a x W Y : G} (h : ⁅a, x⁆ = W) (hY : W * Y = a) :
    x * a * x⁻¹ = Y := by
  rw [commutatorElement_def] at h
  have hY' : Y = W⁻¹ * a := by rw [← hY]; group
  rw [hY', ← h]; group

theorem conj_eq_of_comm_right {a x Z Y : G} (h : ⁅x, a⁆ = Z) (hY : Z * a = Y) :
    x * a * x⁻¹ = Y := by
  rw [commutatorElement_def] at h
  rw [← hY, ← h]; group

theorem qprod_abstract {B C : Type*} [AddCommGroup B] [AddCommGroup C] [Mul B]
    (x₂ x₅ x₆ : B → G) (x₃ x₄ : C → G) (τ : C → C → B)
    (h₂ : ∀ a b, x₂ (a + b) = x₂ a * x₂ b) (h₃ : ∀ a b, x₃ (a + b) = x₃ a * x₃ b)
    (h₄ : ∀ a b, x₄ (a + b) = x₄ a * x₄ b) (h₅ : ∀ a b, x₅ (a + b) = x₅ a * x₅ b)
    (h₆ : ∀ a b, x₆ (a + b) = x₆ a * x₆ b)
    (r52 : ∀ e b, x₅ e * x₂ b = x₂ b * x₅ e * x₆ (e * b))
    (r43 : ∀ d c, x₄ d * x₃ c = x₃ c * x₄ d * x₆ (τ d c))
    (c23 : ∀ a b, Commute (x₂ a) (x₃ b)) (c24 : ∀ a b, Commute (x₂ a) (x₄ b))
    (c26 : ∀ a b, Commute (x₂ a) (x₆ b)) (c35 : ∀ a b, Commute (x₃ a) (x₅ b))
    (c36 : ∀ a b, Commute (x₃ a) (x₆ b)) (c45 : ∀ a b, Commute (x₄ a) (x₅ b))
    (c46 : ∀ a b, Commute (x₄ a) (x₆ b)) (c56 : ∀ a b, Commute (x₅ a) (x₆ b))
    (b c d e f b' c' d' e' f' : _) :
    x₂ b * x₃ c * x₄ d * x₅ e * x₆ f * (x₂ b' * x₃ c' * x₄ d' * x₅ e' * x₆ f') =
      x₂ (b + b') * x₃ (c + c') * x₄ (d + d') * x₅ (e + e') *
        x₆ (τ d c' + e * b' + f + f') := by
  simp only [mul_assoc]
  rw [swap_of_commute ((c26 b' f).symm), swap_of_rel (r52 e b'),
    swap_of_commute ((c24 b' d).symm), swap_of_commute ((c23 b' c).symm), ← mul_assoc (x₂ b),
    ← h₂]
  rw [swap_of_commute ((c36 c' f).symm), swap_of_commute ((c36 c' (e * b')).symm),
    swap_of_commute (c35 c' e).symm, swap_of_rel (r43 d c'), ← mul_assoc (x₃ c), ← h₃]
  rw [swap_of_commute ((c46 d' f).symm), swap_of_commute ((c46 d' (e * b')).symm),
    swap_of_commute (c45 d' e).symm, swap_of_commute ((c46 d' (τ d c')).symm),
    ← mul_assoc (x₄ d), ← h₄]
  rw [swap_of_commute ((c56 e' f).symm), swap_of_commute ((c56 e' (e * b')).symm),
    ← mul_assoc (x₅ e), ← h₅, swap_of_commute ((c56 (e + e') (τ d c')).symm)]
  rw [← h₆ f, ← h₆ (e * b'), ← h₆ (τ d c')]
  simp only [add_assoc]

end Abstract

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

section Defs

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def tr (x : K) : K := x + σ x + σ (σ x)

@[expose] def nK (s : K) : K := s * σ s * σ (σ s)

@[expose] def bF (s c : K) : K := σ s * σ (σ c) + σ (σ s) * σ c

@[expose] def e5F (s c : K) : K := tr σ (s * σ s * σ (σ c))

@[expose] def e6F (s c : K) : K := tr σ (s * σ c * σ (σ c))

@[expose] noncomputable def qE (b c d e f : K) : ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K d4C b * ox₃ σ c * ox₄ σ d * pinnedX TwistTag.D4.tag K d4P e *
    pinnedX TwistTag.D4.tag K d4H f

end Defs

section Fixed

variable {K : Type} [Field K] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

include hσ3 in
theorem sigma_tr (x : K) : σ (tr σ x) = tr σ x := by
  simp only [tr, map_add, sigma_sigma_sigma σ hσ3]; ring

include hσ3 in
theorem sigma_nK (s : K) : σ (nK σ s) = nK σ s := by
  simp only [nK, map_mul, sigma_sigma_sigma σ hσ3]; ring

include hσ3 in
theorem sigma_e5F (s c : K) : σ (e5F σ s c) = e5F σ s c := sigma_tr σ hσ3 _

include hσ3 in
theorem sigma_e6F (s c : K) : σ (e6F σ s c) = e6F σ s c := sigma_tr σ hσ3 _

end Fixed

section Inv

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem Xr_mul_self (α : Fin TwistTag.D4.tag.rank → ℤ) (a : K) : Xr α a * Xr α a = 1 := by
  rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem Xr_inv (α : Fin TwistTag.D4.tag.rank → ℤ) (a : K) : (Xr α a)⁻¹ = Xr α a :=
  inv_eq_of_mul_eq_one_right (Xr_mul_self α a)

end Inv

section Singles

variable {K : Type} [Field K] (σ : K ≃+* K)

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem ox₃_zero' : ox₃ σ 0 = 1 := by rw [coe_ox₃_eq]; simp [pinnedX_zero]

theorem ox₄_zero' : ox₄ σ 0 = 1 := by rw [coe_ox₄_eq]; simp [pinnedX_zero]

theorem qE_C (b : K) : Xr d4C b = qE σ b 0 0 0 0 := by
  simp only [qE, pinnedX_zero, ox₃_zero', ox₄_zero', mul_one]

theorem qE_ox₃ (c : K) : ox₃ σ c = qE σ 0 c 0 0 0 := by
  simp only [qE, pinnedX_zero, ox₄_zero', mul_one, one_mul]

theorem qE_ox₄ (d : K) : ox₄ σ d = qE σ 0 0 d 0 0 := by
  simp only [qE, pinnedX_zero, ox₃_zero', mul_one, one_mul]

theorem qE_P (e : K) : Xr d4P e = qE σ 0 0 0 e 0 := by
  simp only [qE, pinnedX_zero, ox₃_zero', ox₄_zero', mul_one, one_mul]

theorem qE_H (f : K) : Xr d4H f = qE σ 0 0 0 0 f := by
  simp only [qE, pinnedX_zero, ox₃_zero', ox₄_zero', mul_one, one_mul]

theorem qE_congr {b c d e f b' c' d' e' f' : K} (h₁ : b = b') (h₂ : c = c') (h₃ : d = d')
    (h₄ : e = e') (h₅ : f = f') : qE σ b c d e f = qE σ b' c' d' e' f' := by
  subst h₁ h₂ h₃ h₄ h₅; rfl

theorem qE_eq_ox (b : trialityFixedField K σ.toRingHom) (c d : K)
    (e f : trialityFixedField K σ.toRingHom) :
    qE σ b c d e f = ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f := by
  rw [qE, coe_ox₂_eq, coe_ox₅_eq, coe_ox₆_eq]

theorem qE_last_inj {b c d e f f' : K} (h : qE σ b c d e f = qE σ b c d e f') : f = f' := by
  simp only [qE] at h
  exact pinnedX_injective TwistTag.D4.tag K d4H (mul_left_cancel h)

end Singles

section CoordU

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom

include hσ3 in
theorem ox₁_mul_self (s : K) : ox₁ σ s * ox₁ σ s = 1 := by
  rw [← ox₁_add σ hσ3, CharTwo.add_self_eq_zero, ox₁_zero σ hσ3]

include hσ3 in
theorem ox₁_inv (s : K) : (ox₁ σ s)⁻¹ = ox₁ σ s :=
  inv_eq_of_mul_eq_one_right (ox₁_mul_self σ hσ3 s)

include hσ3 in
theorem mem_U_iff {g : ModGL TwistTag.D4.tag K} :
    g ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ ↔
      ∃ (a : K) (b : trialityFixedField K τ₀) (c d : K) (e f : trialityFixedField K τ₀),
        g = ox₁ σ a * qE σ b c d e f := by
  constructor
  · intro hg
    obtain ⟨a, b, c, d, e, f, rfl⟩ := coord_exists σ hσ3 hg
    exact ⟨a, b, c, d, e, f, by rw [qE_eq_ox]; simp only [mul_assoc]⟩
  · rintro ⟨a, b, c, d, e, f, rfl⟩
    obtain ⟨-, ⟨h1, h2, h3, h4, h5, h6⟩, -⟩ := ox_data σ hσ3
    rw [qE_eq_ox]
    have m := fun x y (hx : x ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀)
      (hy : y ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) => mul_mem hx hy
    exact m _ _ (h1 a) (m _ _ (m _ _ (m _ _ (m _ _ (h2 b) (h3 c)) (h4 d)) (h5 e)) (h6 f))

include hσ3 in
theorem uE_inj {a a' : K} {b b' : trialityFixedField K τ₀} {c c' d d' : K}
    {e e' f f' : trialityFixedField K τ₀}
    (h : ox₁ σ a * qE σ b c d e f = ox₁ σ a' * qE σ b' c' d' e' f') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
  rw [qE_eq_ox, qE_eq_ox] at h
  simp only [← mul_assoc] at h
  exact coord_unique σ hσ3 h

include hσ3 in
theorem qE_inj {b b' : trialityFixedField K τ₀} {c c' d d' : K}
    {e e' f f' : trialityFixedField K τ₀} (h : qE σ b c d e f = qE σ b' c' d' e' f') :
    b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' :=
  (uE_inj σ hσ3 (a := 0) (a' := 0) (by rw [h])).2

include hσ3 in
theorem mem_Q0_iff' {g : ModGL TwistTag.D4.tag K} :
    g ∈ Q0 σ ↔ ∃ (b : trialityFixedField K τ₀) (c d : K) (e f : trialityFixedField K τ₀),
      g = qE σ b c d e f := by
  rw [mem_radical_a0_iff σ hσ3]
  constructor
  · rintro ⟨b, c, d, e, f, rfl⟩
    exact ⟨b, c, d, e, f, (qE_eq_ox σ b c d e f).symm⟩
  · rintro ⟨b, c, d, e, f, rfl⟩
    exact ⟨b, c, d, e, f, qE_eq_ox σ b c d e f⟩

include hσ3 in
theorem qE_mem_Q0 (b : trialityFixedField K τ₀) (c d : K) (e f : trialityFixedField K τ₀) :
    qE σ b c d e f ∈ Q0 σ :=
  (mem_Q0_iff' σ hσ3).2 ⟨b, c, d, e, f, rfl⟩

include hσ3 in
theorem Q0_le_U : Q0 σ ≤ graphFixedPosUnipotent TwistTag.D4 K τ₀ := fun g hg => by
  obtain ⟨b, c, d, e, f, rfl⟩ := (mem_Q0_iff' σ hσ3).1 hg
  exact (mem_U_iff σ hσ3).2 ⟨0, b, c, d, e, f, by rw [ox₁_zero σ hσ3, one_mul]⟩

end CoordU


section Relations

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem commute_Xr_prod3 {α β₀ β₁ β₃ : Fin TwistTag.D4.tag.rank → ℤ} (h₀ : d4CommB α β₀ = true)
    (h₁ : d4CommB α β₁ = true) (h₃ : d4CommB α β₃ = true) (a s₀ s₁ s₃ : K) :
    Commute (Xr α a) (Xr β₀ s₀ * Xr β₁ s₁ * Xr β₃ s₃) :=
  ((commute_of_d4CommB h₀ a s₀).mul_right (commute_of_d4CommB h₁ a s₁)).mul_right
    (commute_of_d4CommB h₃ a s₃)

theorem rel_P_C (e b : K) : Xr d4P e * Xr d4C b = Xr d4C b * Xr d4P e * Xr d4H (e * b) := by
  have h := commutator_of_d4SumB (α := d4C) (β := d4P) (γ := d4H) (by decide +kernel) b e
  have hcH : Commute (Xr d4C b) (Xr d4H (b * e)) := commute_of_d4CommB (by decide +kernel) _ _
  have hPH : Commute (Xr d4P e) (Xr d4H (b * e)) := commute_of_d4CommB (by decide +kernel) _ _
  rw [commutatorElement_def] at h
  have h' : Xr d4C b * Xr d4P e = Xr d4H (b * e) * (Xr d4P e * Xr d4C b) := by
    rw [← h]; group
  have h'' : Xr d4P e * Xr d4C b = Xr d4H (b * e) * (Xr d4C b * Xr d4P e) := by
    rw [h', ← mul_assoc, Xr_mul_self, one_mul]
  rw [mul_comm e b, h'', ← mul_assoc, ← hcH.eq, mul_assoc, ← hPH.eq, mul_assoc]

theorem commute_C_ox₃ (a b : K) (σ : K ≃+* K) : Commute (Xr d4C a) (ox₃ σ b) := by
  rw [coe_ox₃_eq]; exact commute_Xr_prod3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ _ _

theorem commute_C_ox₄ (a b : K) (σ : K ≃+* K) : Commute (Xr d4C a) (ox₄ σ b) := by
  rw [coe_ox₄_eq]; exact commute_Xr_prod3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ _ _

theorem commute_P_ox₃ (a b : K) (σ : K ≃+* K) : Commute (Xr d4P a) (ox₃ σ b) := by
  rw [coe_ox₃_eq]; exact commute_Xr_prod3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ _ _

theorem commute_P_ox₄ (a b : K) (σ : K ≃+* K) : Commute (Xr d4P a) (ox₄ σ b) := by
  rw [coe_ox₄_eq]; exact commute_Xr_prod3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ _ _

theorem commute_H_ox₃ (a b : K) (σ : K ≃+* K) : Commute (Xr d4H a) (ox₃ σ b) := by
  rw [coe_ox₃_eq]; exact commute_Xr_prod3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ _ _

theorem commute_H_ox₄ (a b : K) (σ : K ≃+* K) : Commute (Xr d4H a) (ox₄ σ b) := by
  rw [coe_ox₄_eq]; exact commute_Xr_prod3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ _ _

theorem commute_H_ox₁ (a b : K) (σ : K ≃+* K) : Commute (Xr d4H a) (ox₁ σ b) := by
  rw [coe_ox₁_eq]; exact commute_Xr_prod3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ _ _

theorem commute_P_ox₁ (a b : K) (σ : K ≃+* K) : Commute (Xr d4P a) (ox₁ σ b) := by
  rw [coe_ox₁_eq]; exact commute_Xr_prod3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ _ _

end Relations

section Product

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K

omit [Finite K] in
include hσ3 in
theorem rel_ox₄_ox₃ (d c : K) : ox₄ σ d * ox₃ σ c = ox₃ σ c * ox₄ σ d * Xr d4H (tr σ (d * c)) := by
  have h := rel34 σ hσ3 c d
  rw [coe_ox₆_eq, coe_trialityTrace, commutatorElement_def] at h
  change _ = Xr d4H (c * d + σ (c * d) + σ (σ (c * d))) at h
  have hz : tr σ (d * c) = c * d + σ (c * d) + σ (σ (c * d)) := by rw [tr, mul_comm d c]
  rw [hz]
  set z := Xr d4H (c * d + σ (c * d) + σ (σ (c * d)))
  have h' : ox₃ σ c * ox₄ σ d = z * (ox₄ σ d * ox₃ σ c) := by rw [← h]; group
  have h'' : ox₄ σ d * ox₃ σ c = z * (ox₃ σ c * ox₄ σ d) := by
    rw [h', ← mul_assoc, Xr_mul_self, one_mul]
  rw [h'', ← mul_assoc, (commute_H_ox₃ _ c σ).eq, mul_assoc, (commute_H_ox₄ _ d σ).eq,
    mul_assoc]

include hσ3 in
theorem qE_mul (b c d e f b' c' d' e' f' : K) :
    qE σ b c d e f * qE σ b' c' d' e' f' =
      qE σ (b + b') (c + c') (d + d') (e + e') (tr σ (d * c') + e * b' + f + f') :=
  qprod_abstract (Xr d4C) (Xr d4P) (Xr d4H) (ox₃ σ) (ox₄ σ) (fun d c => tr σ (d * c))
    (pinnedX_add _ _ _) (ox₃_add σ hσ3) (ox₄_add σ hσ3) (pinnedX_add _ _ _) (pinnedX_add _ _ _)
    rel_P_C (rel_ox₄_ox₃ σ hσ3) (fun a b => commute_C_ox₃ a b σ) (fun a b => commute_C_ox₄ a b σ)
    (fun a b => commute_of_d4CommB (by decide +kernel) a b)
    (fun a b => (commute_P_ox₃ b a σ).symm) (fun a b => (commute_H_ox₃ b a σ).symm)
    (fun a b => (commute_P_ox₄ b a σ).symm) (fun a b => (commute_H_ox₄ b a σ).symm)
    (fun a b => commute_of_d4CommB (by decide +kernel) a b) b c d e f b' c' d' e' f'

include hσ3 in
theorem conj_ox₁_C {b : K} (hb : σ b = b) (s : K) :
    ox₁ σ s * Xr d4C b * (ox₁ σ s)⁻¹ =
      qE σ b (b * s) (b * (σ s * σ (σ s))) (b * nK σ s) (b * b * nK σ s) := by
  have h3 := sigma_sigma_sigma σ hσ3
  have h := ox₂_comm_ox₁_gen σ hσ3 ⟨b, hb⟩ s
  rw [coe_ox₂_eq, coe_ox₅_eq, coe_ox₆_eq] at h
  simp only [Subfield.coe_mul, coe_nrm] at h
  refine conj_eq_of_comm_left h ?_
  rw [qE_ox₃, qE_ox₄, qE_P, qE_H, qE_mul σ hσ3, qE_mul σ hσ3, qE_mul σ hσ3, qE_mul σ hσ3,
    qE_C σ]
  refine qE_congr σ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [nK, tr, map_mul, map_zero, hb, h3, mul_zero, add_zero, zero_add] <;> ring2

include hσ3 in
theorem conj_ox₁_ox₃ (s c : K) :
    ox₁ σ s * ox₃ σ c * (ox₁ σ s)⁻¹ = qE σ 0 c (bF σ s c) (e5F σ s c) (e6F σ s c) := by
  have h3 := sigma_sigma_sigma σ hσ3
  have h := ox₁_comm_ox₃ σ hσ3 s c
  rw [coe_ox₅_eq, coe_ox₆_eq, coe_trialityTrace, coe_trialityTrace] at h
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h
  refine conj_eq_of_comm_right h ?_
  rw [qE_ox₄, qE_P, qE_H, qE_ox₃, qE_mul σ hσ3, qE_mul σ hσ3, qE_mul σ hσ3]
  refine qE_congr σ ?_ ?_ ?_ ?_ ?_ <;>
    (simp only [bF, e5F, e6F, tr, map_mul, map_add, map_zero, h3, mul_zero, add_zero,
      zero_add]; try ring2)

include hσ3 in
theorem conj_ox₁_ox₄ (s d : K) :
    ox₁ σ s * ox₄ σ d * (ox₁ σ s)⁻¹ = qE σ 0 0 d (tr σ (s * d)) 0 := by
  have h := rel14 σ hσ3 s d
  rw [coe_ox₅_eq, coe_trialityTrace] at h
  refine conj_eq_of_comm_right h ?_
  rw [qE_P, qE_ox₄, qE_mul σ hσ3]
  refine qE_congr σ ?_ ?_ ?_ ?_ ?_ <;> simp [tr]

include hσ3 in
theorem conj_ox₁_qE {b : K} (hb : σ b = b) (s c d e f : K) :
    ox₁ σ s * qE σ b c d e f * (ox₁ σ s)⁻¹ =
      qE σ b (c + s * b) (d + b * (σ s * σ (σ s)) + bF σ s c)
        (e + b * nK σ s + e5F σ s c + tr σ (s * d))
        (f + b * b * nK σ s + e6F σ s c + b * e5F σ s c) := by
  have h3 := sigma_sigma_sigma σ hσ3
  have conj5 : ∀ g x₁ x₂ x₃ x₄ x₅ : ModGL TwistTag.D4.tag K,
      g * (x₁ * x₂ * x₃ * x₄ * x₅) * g⁻¹ = (g * x₁ * g⁻¹) * (g * x₂ * g⁻¹) * (g * x₃ * g⁻¹) *
        (g * x₄ * g⁻¹) * (g * x₅ * g⁻¹) := fun g x₁ x₂ x₃ x₄ x₅ => by group
  rw [qE, conj5, conj_ox₁_C σ hσ3 hb, conj_ox₁_ox₃ σ hσ3, conj_ox₁_ox₄ σ hσ3,
    (commute_P_ox₁ e s σ).symm.eq, mul_inv_cancel_right, (commute_H_ox₁ f s σ).symm.eq,
    mul_inv_cancel_right, qE_P, qE_H, qE_mul σ hσ3, qE_mul σ hσ3, qE_mul σ hσ3, qE_mul σ hσ3]
  refine qE_congr σ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · simp only [add_zero]; ring
  · simp only [nK, tr, e5F, e6F, map_mul, map_zero, hb, h3, mul_zero, add_zero, zero_add]
    ring2

include hσ3 in
theorem qE_inv (b c d e f : K) :
    (qE σ b c d e f)⁻¹ = qE σ b c d e (f + tr σ (d * c) + e * b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [qE_mul σ hσ3, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero]
  have hz : tr σ (d * c) + e * b + f + (f + tr σ (d * c) + e * b) = 0 := by ring2
  rw [hz, ← qE_H, pinnedX_zero]

include hσ3 in
theorem qE_commute_iff (b c d e f b' c' d' e' f' : K) :
    qE σ b c d e f * qE σ b' c' d' e' f' = qE σ b' c' d' e' f' * qE σ b c d e f ↔
      tr σ (d * c') + e * b' = tr σ (d' * c) + e' * b := by
  rw [qE_mul σ hσ3, qE_mul σ hσ3, add_comm b', add_comm c', add_comm d', add_comm e']
  constructor
  · intro h
    have h2 := qE_last_inj σ h
    linear_combination h2
  · intro h
    congr 1
    linear_combination h

include hσ3 in
theorem qE_conj_qE (b₀ c₀ d₀ e₀ f₀ b c d e f : K) :
    qE σ b₀ c₀ d₀ e₀ f₀ * qE σ b c d e f * (qE σ b₀ c₀ d₀ e₀ f₀)⁻¹ =
      qE σ b c d e (f + tr σ (d * c₀) + e * b₀ + tr σ (d₀ * c) + e₀ * b) := by
  rw [qE_inv σ hσ3, qE_mul σ hσ3, qE_mul σ hσ3]
  refine qE_congr σ ?_ ?_ ?_ ?_ ?_
  · ring2
  · ring2
  · ring2
  · ring2
  · simp only [tr, map_add, map_mul]; ring2

include hσ3 in
theorem commute_ox₁_conds {s : K} (hs : s ≠ 0) (b₀ : trialityFixedField K τ₀) (c₀ d₀ : K)
    (e₀ f₀ b : trialityFixedField K τ₀) (c d : K) (e f : trialityFixedField K τ₀)
    (h : ox₁ σ s * qE σ b₀ c₀ d₀ e₀ f₀ * qE σ b c d e f =
      qE σ b c d e f * (ox₁ σ s * qE σ b₀ c₀ d₀ e₀ f₀)) :
    (b : K) = 0 ∧ bF σ s c = 0 ∧ e5F σ s c + tr σ (s * d) = 0 := by
  have hb : σ (b : K) = b := b.2
  have he : σ (e : K) = e := e.2
  have hf : σ (f : K) = f := f.2
  have hb₀ : σ (b₀ : K) = b₀ := b₀.2
  have he₀ : σ (e₀ : K) = e₀ := e₀.2
  have hconj : ox₁ σ s * (qE σ b₀ c₀ d₀ e₀ f₀ * qE σ b c d e f * (qE σ b₀ c₀ d₀ e₀ f₀)⁻¹) *
      (ox₁ σ s)⁻¹ = qE σ b c d e f := by
    have : ox₁ σ s * qE σ b₀ c₀ d₀ e₀ f₀ * qE σ b c d e f *
        (ox₁ σ s * qE σ b₀ c₀ d₀ e₀ f₀)⁻¹ = qE σ b c d e f := by
      rw [h]; group
    calc ox₁ σ s * (qE σ b₀ c₀ d₀ e₀ f₀ * qE σ b c d e f * (qE σ b₀ c₀ d₀ e₀ f₀)⁻¹) *
          (ox₁ σ s)⁻¹ = ox₁ σ s * qE σ b₀ c₀ d₀ e₀ f₀ * qE σ b c d e f *
          (ox₁ σ s * qE σ b₀ c₀ d₀ e₀ f₀)⁻¹ := by group
      _ = qE σ b c d e f := this
  rw [qE_conj_qE σ hσ3, conj_ox₁_qE σ hσ3 hb] at hconj
  set Y := (e : K) + b * nK σ s + e5F σ s c + tr σ (s * d) with hY
  have hYk : σ Y = Y := by
    rw [hY, map_add, map_add, map_add, map_mul, he, hb, sigma_nK σ hσ3, sigma_e5F σ hσ3,
      sigma_tr σ hσ3]
  set Z := (f : K) + tr σ (d * c₀) + e * b₀ + tr σ (d₀ * c) + e₀ * b + b * b * nK σ s +
    e6F σ s c + b * e5F σ s c with hZ
  have hZk : σ Z = Z := by
    rw [hZ]
    simp only [map_add, map_mul, hb, he, hf, hb₀, he₀, sigma_nK σ hσ3, sigma_e5F σ hσ3,
      sigma_e6F σ hσ3, sigma_tr σ hσ3]
  have hconj' : qE σ (b : K) (c + s * b) (d + b * (σ s * σ (σ s)) + bF σ s c)
      ((⟨Y, hYk⟩ : trialityFixedField K τ₀) : K) ((⟨Z, hZk⟩ : trialityFixedField K τ₀) : K) =
      qE σ b c d e f := by
    rw [← hconj]
  obtain ⟨-, h2, h3, h4, -⟩ := qE_inj σ hσ3 hconj'
  have hsb : s * b = 0 := by linear_combination h2
  have hb0 : (b : K) = 0 := (mul_eq_zero.1 hsb).resolve_left hs
  refine ⟨hb0, ?_, ?_⟩
  · rw [hb0, zero_mul, add_zero] at h3
    linear_combination h3
  · have h4' := congrArg Subtype.val h4
    simp only at h4'
    rw [hY, hb0, zero_mul, add_zero] at h4'
    linear_combination h4'

include hσ3 in
theorem qE_mul_self (b c d e f : K) :
    qE σ b c d e f * qE σ b c d e f = Xr d4H (tr σ (d * c) + e * b) := by
  rw [qE_mul σ hσ3, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, qE_H]
  refine qE_congr σ rfl rfl rfl rfl ?_
  ring2

include hσ3 in
theorem qE_mul_self_eq_one_iff (b c d e f : K) :
    qE σ b c d e f * qE σ b c d e f = 1 ↔ tr σ (d * c) + e * b = 0 := by
  rw [qE_mul_self σ hσ3, ← pinnedX_zero TwistTag.D4.tag K d4H]
  exact (pinnedX_injective TwistTag.D4.tag K d4H).eq_iff

include hσ3 in
theorem conj_ox₁_mem_Q0 (s : K) {g : ModGL TwistTag.D4.tag K} (hg : g ∈ Q0 σ) :
    ox₁ σ s * g * (ox₁ σ s)⁻¹ ∈ Q0 σ := by
  obtain ⟨b, c, d, e, f, rfl⟩ := (mem_Q0_iff' σ hσ3).1 hg
  have hb : σ (b : K) = b := b.2
  have he : σ (e : K) = e := e.2
  have hf : σ (f : K) = f := f.2
  rw [conj_ox₁_qE σ hσ3 hb]
  have hY : σ ((e : K) + b * nK σ s + e5F σ s c + tr σ (s * d)) =
      (e : K) + b * nK σ s + e5F σ s c + tr σ (s * d) := by
    rw [map_add, map_add, map_add, map_mul, he, hb, sigma_nK σ hσ3, sigma_e5F σ hσ3,
      sigma_tr σ hσ3]
  have hZ : σ ((f : K) + b * b * nK σ s + e6F σ s c + b * e5F σ s c) =
      (f : K) + b * b * nK σ s + e6F σ s c + b * e5F σ s c := by
    simp only [map_add, map_mul, hb, hf, sigma_nK σ hσ3, sigma_e5F σ hσ3, sigma_e6F σ hσ3]
  exact qE_mem_Q0 σ hσ3 b _ _ ⟨_, hY⟩ ⟨_, hZ⟩

end Product

end CFSG.Quasithin.B42D4
