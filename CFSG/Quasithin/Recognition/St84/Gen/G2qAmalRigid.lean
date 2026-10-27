module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalRoots

public noncomputable section

namespace CFSG.Quasithin.F112R.St84.G2q

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 (i0 i1 coords_one mem_one)

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

set_option quotPrecheck false in
local notation "Qr" => ↥(parabolicRadical Tag.G2 K {i1})

section Units

private theorem exists_unit_pow_three_ne_one_of_card [Finite K] (hK : 8 ≤ Nat.card K) :
    ∃ l : Kˣ, l ^ 3 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨g, fun h => ?_⟩
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

private theorem eq_zero_of_val_mul_eq {u : Kˣ} (hu : u ≠ 1) {x : K} (h : (u : K) * x = x) :
    x = 0 := by
  have h' : ((u : K) - 1) * x = 0 := by linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 fun e => hu (Units.val_eq_one.1 e))

variable [CharP K 2]

private theorem eq_one_of_sq_eq_one_unit {u : Kˣ} (h : u ^ 2 = 1) : u = 1 :=
  Units.ext (eq_one_of_mul_self_eq_one_two (by simpa [sq] using congrArg Units.val h))

private theorem zpow_ne_one_of {l : Kˣ} (h3 : l ^ 3 ≠ 1) {k : ℤ}
    (hk : k = 2 ∨ k = -2 ∨ k = 4 ∨ k = -4 ∨ k = 6 ∨ k = -6) : l ^ k ≠ 1 := by
  have h1 : l ≠ 1 := fun h => h3 (by rw [h, one_pow])
  have h2 : l ^ 2 ≠ 1 := fun h => h1 (eq_one_of_sq_eq_one_unit h)
  have h4 : l ^ 4 ≠ 1 := fun h => h2 (eq_one_of_sq_eq_one_unit (by rw [← pow_mul]; exact h))
  have h6 : l ^ 6 ≠ 1 := fun h => h3 (eq_one_of_sq_eq_one_unit (by rw [← pow_mul]; exact h))
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using h2
  · simpa using h2
  · simpa using h4
  · simpa using h4
  · simpa using h6
  · simpa using h6

end Units

section Elements

private def xqA (x : K) : Qr := ⟨X g2a x, mem_one (Or.inl rfl) x⟩

private def xqU (x : K) : Qr := ⟨X g2u x, mem_one (Or.inr (Or.inl rfl)) x⟩

private def xqV (x : K) : Qr := ⟨X g2v x, mem_one (Or.inr (Or.inr (Or.inl rfl))) x⟩

private def xqB (x : K) : Qr := ⟨X g2b x, mem_one (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) x⟩

private def xqC (x : K) : Qr := ⟨X g2c x, mem_one (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) x⟩

private theorem xqA_coe (x : K) : (xqA x : ModGL Tag.G2 K) = X g2a x := rfl
private theorem xqU_coe (x : K) : (xqU x : ModGL Tag.G2 K) = X g2u x := rfl
private theorem xqV_coe (x : K) : (xqV x : ModGL Tag.G2 K) = X g2v x := rfl
private theorem xqB_coe (x : K) : (xqB x : ModGL Tag.G2 K) = X g2b x := rfl
private theorem xqA_zero : xqA (0 : K) = 1 := Subtype.ext (pinnedX_zero Tag.G2 K g2a)
private theorem xqU_zero : xqU (0 : K) = 1 := Subtype.ext (pinnedX_zero Tag.G2 K g2u)
private theorem xqV_zero : xqV (0 : K) = 1 := Subtype.ext (pinnedX_zero Tag.G2 K g2v)
private theorem xqB_zero : xqB (0 : K) = 1 := Subtype.ext (pinnedX_zero Tag.G2 K g2b)

private theorem conj_xqA (s : Kˣ) (c : K) :
    (xqA ((s : K) * c) : ModGL Tag.G2 K) = dT s 1 * (xqA c : ModGL Tag.G2 K) * (dT s 1)⁻¹ :=
  (dT_conj_a s 1 c).symm

private theorem conj_xqU (s : Kˣ) (c : K) :
    (xqU ((s : K) * c) : ModGL Tag.G2 K) = dT s 1 * (xqU c : ModGL Tag.G2 K) * (dT s 1)⁻¹ := by
  rw [xqU_coe, xqU_coe, dT_conj_u]
  simp only [Units.val_one, mul_one]

private theorem conj_xqV (s : Kˣ) (c : K) :
    (xqV ((s : K) * c) : ModGL Tag.G2 K) = dT s 1 * (xqV c : ModGL Tag.G2 K) * (dT s 1)⁻¹ := by
  rw [xqV_coe, xqV_coe, dT_conj_v]
  simp only [Units.val_one, one_pow, mul_one]

private theorem conj_xqB (s : Kˣ) (c : K) :
    (xqB ((s : K) * c) : ModGL Tag.G2 K) = dT s 1 * (xqB c : ModGL Tag.G2 K) * (dT s 1)⁻¹ := by
  rw [xqB_coe, xqB_coe, dT_conj_b]
  simp only [Units.val_one, one_pow, mul_one]

private structure RigidShape (Ψ : Qr →* Qr) (κa κu κv κb : K) : Prop where
  a : ∀ x, Ψ (xqA x) = xqB (κa * x)
  u : ∀ x, Ψ (xqU x) = xqV (κu * x)
  v : ∀ x, Ψ (xqV x) = xqU (κv * x)
  b : ∀ x, Ψ (xqB x) = xqA (κb * x)
  c : ∀ x, Ψ (xqC x) = xqC x

private theorem eq_prod_of_coe {x : Qr} {B C D E F : K}
    (hx : (x : ModGL Tag.G2 K) = g2N 0 B C D E F) :
    x = xqA B * xqU C * xqV D * xqB E * xqC F := by
  apply Subtype.ext
  rw [hx]
  simp only [g2N, pinnedX_zero, one_mul]
  rfl

end Elements

section Torus

private theorem exists_g2N (x : Qr) :
    ∃ B C D E F : K, (x : ModGL Tag.G2 K) = g2N 0 B C D E F := by
  obtain ⟨t₁, t₂, t₃, t₄, t₅, ht⟩ := coords_one x.2
  refine ⟨t₁, t₂, t₃, t₄, t₅, ?_⟩
  rw [ht]
  simp only [g2N, pinnedX_zero, one_mul, mul_assoc]
  rfl

private theorem vanish_of_fixed {s t : Kˣ} {B C D E F : K}
    (h : dT s t * g2N 0 B C D E F * (dT s t)⁻¹ = g2N 0 B C D E F) :
    (s ≠ 1 → B = 0) ∧ (s * t ≠ 1 → C = 0) ∧ (s * t ^ 2 ≠ 1 → D = 0) ∧
      (s * t ^ 3 ≠ 1 → E = 0) ∧ (s ^ 2 * t ^ 3 ≠ 1 → F = 0) := by
  rw [dT_conj_g2N] at h
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := g2N_injective h
  refine ⟨fun hs => eq_zero_of_val_mul_eq hs h2, fun hs => eq_zero_of_val_mul_eq hs ?_,
    fun hs => eq_zero_of_val_mul_eq hs ?_, fun hs => eq_zero_of_val_mul_eq hs ?_,
    fun hs => eq_zero_of_val_mul_eq hs ?_⟩
  · rw [Units.val_mul]; exact h3
  · rw [Units.val_mul, Units.val_pow_eq_pow_val]; exact h4
  · rw [Units.val_mul, Units.val_pow_eq_pow_val]; exact h5
  · rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]; exact h6

private theorem vanish_of_fixed_zpow (l : Kˣ) {a b : ℤ} {B C D E F : K}
    (h : dT (l ^ a) (l ^ b) * g2N 0 B C D E F * (dT (l ^ a) (l ^ b))⁻¹ = g2N 0 B C D E F) :
    (l ^ a ≠ 1 → B = 0) ∧ (l ^ (a + b) ≠ 1 → C = 0) ∧ (l ^ (a + 2 * b) ≠ 1 → D = 0) ∧
      (l ^ (a + 3 * b) ≠ 1 → E = 0) ∧ (l ^ (2 * a + 3 * b) ≠ 1 → F = 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := vanish_of_fixed h
  refine ⟨h1, fun hs => h2 ?_, fun hs => h3 ?_, fun hs => h4 ?_, fun hs => h5 ?_⟩
  · rwa [zpow_add] at hs
  · rwa [show l ^ (a + 2 * b) = l ^ a * (l ^ b) ^ 2 by group] at hs
  · rwa [show l ^ (a + 3 * b) = l ^ a * (l ^ b) ^ 3 by group] at hs
  · rwa [show l ^ (2 * a + 3 * b) = (l ^ a) ^ 2 * (l ^ b) ^ 3 by group] at hs

end Torus

section Scalars

variable (Ψ : ↥(parabolicRadical Tag.G2 K {i1}) →* ↥(parabolicRadical Tag.G2 K {i1}))
  (hH : ∀ (s : Kˣ) (x y : ↥(parabolicRadical Tag.G2 K {i1})),
    (y : ModGL Tag.G2 K) = dT s 1 * (x : ModGL Tag.G2 K) * (dT s 1)⁻¹ →
      (Ψ y : ModGL Tag.G2 K) = dT s 1 * (Ψ x : ModGL Tag.G2 K) * (dT s 1)⁻¹)
  (hT : ∀ (l : Kˣ) (x y : ↥(parabolicRadical Tag.G2 K {i1})),
    (y : ModGL Tag.G2 K) = dT (l⁻¹ ^ 3) (l ^ 2) * (x : ModGL Tag.G2 K) * (dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ →
      (Ψ y : ModGL Tag.G2 K) =
        (dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ * (Ψ x : ModGL Tag.G2 K) * dT (l⁻¹ ^ 3) (l ^ 2))

section Light

include hH hT in
private theorem fixed_of_hH_hT (l s : Kˣ) {a b : ℤ} (hs : l ^ a = l⁻¹ ^ 3 * s)
    (ht : l ^ b = l ^ 2) (x y : Qr)
    (h1 : (y : ModGL Tag.G2 K) = dT s 1 * (x : ModGL Tag.G2 K) * (dT s 1)⁻¹)
    (h2 : (y : ModGL Tag.G2 K) =
      dT (l⁻¹ ^ 3) (l ^ 2) * (x : ModGL Tag.G2 K) * (dT (l⁻¹ ^ 3) (l ^ 2))⁻¹) :
    dT (l ^ a) (l ^ b) * (Ψ x : ModGL Tag.G2 K) * (dT (l ^ a) (l ^ b))⁻¹ =
      (Ψ x : ModGL Tag.G2 K) := by
  have e := (hH s x y h1).symm.trans (hT l x y h2)
  have e3 : dT (l ^ a) (l ^ b) = dT (l⁻¹ ^ 3) (l ^ 2) * dT s 1 := by
    rw [dT_mul, mul_one, hs, ht]
  rw [e3]
  calc _ = dT (l⁻¹ ^ 3) (l ^ 2) * (dT s 1 * (Ψ x : ModGL Tag.G2 K) * (dT s 1)⁻¹) *
          (dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ := by group
    _ = _ := by rw [e]; group

include hH in
private theorem scalar_law {P R : K → Qr}
    (hP : ∀ (s : Kˣ) (c : K), (P ((s : K) * c) : ModGL Tag.G2 K) =
      dT s 1 * (P c : ModGL Tag.G2 K) * (dT s 1)⁻¹)
    (hR : ∀ (s : Kˣ) (c : K), (R ((s : K) * c) : ModGL Tag.G2 K) =
      dT s 1 * (R c : ModGL Tag.G2 K) * (dT s 1)⁻¹)
    (hP0 : P 0 = 1) (hR0 : R 0 = 1) {κ : K} (h1 : Ψ (P 1) = R κ) (x : K) :
    Ψ (P x) = R (κ * x) := by
  by_cases hx : x = 0
  · rw [hx, mul_zero, hP0, hR0, map_one]
  · let s : Kˣ := Units.mk0 x hx
    have e := hH s (P 1) (P ((s : K) * 1)) (hP s 1)
    rw [h1] at e
    have e' : Ψ (P ((s : K) * 1)) = R ((s : K) * κ) := Subtype.ext (e.trans (hR s κ).symm)
    rwa [show (s : K) * 1 = x by simp [s], show (s : K) * κ = κ * x by simp [s, mul_comm]] at e'

end Light

variable [CharP K 2]

include hH hT in
private theorem scalars_a {l : Kˣ} (hl : l ^ 3 ≠ 1) :
    ∃ κ : K, ∀ x : K, Ψ (xqA x) = xqB (κ * x) := by
  have hfix := fixed_of_hH_hT Ψ hH hT l (l⁻¹ ^ 3) (a := -6) (b := 2) (by group) (by group)
    (xqA 1) (xqA ((l⁻¹ ^ 3 : Kˣ) : K))
    (by rw [xqA_coe, xqA_coe, dT_conj_a, mul_one]) (by rw [xqA_coe, xqA_coe, dT_conj_a, mul_one])
  obtain ⟨B, C, D, E, F, hΨ⟩ := exists_g2N (Ψ (xqA 1))
  rw [hΨ] at hfix
  obtain ⟨h1, h2, h3, -, h5⟩ := vanish_of_fixed_zpow l hfix
  have hB := h1 (zpow_ne_one_of hl (by decide))
  have hC := h2 (zpow_ne_one_of hl (by decide))
  have hD := h3 (zpow_ne_one_of hl (by decide))
  have hF := h5 (zpow_ne_one_of hl (by decide))
  subst hB hC hD hF
  exact ⟨E, scalar_law Ψ hH (P := xqA) (R := xqB) conj_xqA conj_xqB xqA_zero xqB_zero
    (Subtype.ext (hΨ.trans (pinnedX_b_eq_g2N E).symm))⟩

include hH hT in
private theorem scalars_u {l : Kˣ} (hl : l ^ 3 ≠ 1) :
    ∃ κ : K, ∀ x : K, Ψ (xqU x) = xqV (κ * x) := by
  have hfix := fixed_of_hH_hT Ψ hH hT l (l⁻¹ ^ 3 * l ^ 2) (a := -4) (b := 2) (by group)
    (by group) (xqU 1) (xqU ((l⁻¹ ^ 3 * l ^ 2 : Kˣ) : K))
    (by rw [xqU_coe, xqU_coe, dT_conj_u]; simp only [Units.val_one, mul_one])
    (by rw [xqU_coe, xqU_coe, dT_conj_u, Units.val_mul, mul_one])
  obtain ⟨B, C, D, E, F, hΨ⟩ := exists_g2N (Ψ (xqU 1))
  rw [hΨ] at hfix
  obtain ⟨h1, h2, -, h4, h5⟩ := vanish_of_fixed_zpow l hfix
  have hB := h1 (zpow_ne_one_of hl (by decide))
  have hC := h2 (zpow_ne_one_of hl (by decide))
  have hE := h4 (zpow_ne_one_of hl (by decide))
  have hF := h5 (zpow_ne_one_of hl (by decide))
  subst hB hC hE hF
  exact ⟨D, scalar_law Ψ hH (P := xqU) (R := xqV) conj_xqU conj_xqV xqU_zero xqV_zero
    (Subtype.ext (hΨ.trans (pinnedX_v_eq_g2N D).symm))⟩

include hH hT in
private theorem scalars_v {l : Kˣ} (hl : l ^ 3 ≠ 1) :
    ∃ κ : K, ∀ x : K, Ψ (xqV x) = xqU (κ * x) := by
  have hfix := fixed_of_hH_hT Ψ hH hT l (l⁻¹ ^ 3 * (l ^ 2) ^ 2) (a := -2) (b := 2) (by group)
    (by group) (xqV 1) (xqV ((l⁻¹ ^ 3 * (l ^ 2) ^ 2 : Kˣ) : K))
    (by rw [xqV_coe, xqV_coe, dT_conj_v]; simp only [Units.val_one, one_pow, mul_one])
    (by simp only [xqV_coe, dT_conj_v, Units.val_mul, Units.val_pow_eq_pow_val, mul_one])
  obtain ⟨B, C, D, E, F, hΨ⟩ := exists_g2N (Ψ (xqV 1))
  rw [hΨ] at hfix
  obtain ⟨h1, -, h3, h4, h5⟩ := vanish_of_fixed_zpow l hfix
  have hB := h1 (zpow_ne_one_of hl (by decide))
  have hD := h3 (zpow_ne_one_of hl (by decide))
  have hE := h4 (zpow_ne_one_of hl (by decide))
  have hF := h5 (zpow_ne_one_of hl (by decide))
  subst hB hD hE hF
  exact ⟨C, scalar_law Ψ hH (P := xqV) (R := xqU) conj_xqV conj_xqU xqV_zero xqU_zero
    (Subtype.ext (hΨ.trans (pinnedX_u_eq_g2N C).symm))⟩

include hH hT in
private theorem scalars_b {l : Kˣ} (hl : l ^ 3 ≠ 1) :
    ∃ κ : K, ∀ x : K, Ψ (xqB x) = xqA (κ * x) := by
  have hfix := fixed_of_hH_hT Ψ hH hT l (l⁻¹ ^ 3 * (l ^ 2) ^ 3) (a := 0) (b := 2) (by group)
    (by group) (xqB 1) (xqB ((l⁻¹ ^ 3 * (l ^ 2) ^ 3 : Kˣ) : K))
    (by rw [xqB_coe, xqB_coe, dT_conj_b]; simp only [Units.val_one, one_pow, mul_one])
    (by simp only [xqB_coe, dT_conj_b, Units.val_mul, Units.val_pow_eq_pow_val, mul_one])
  obtain ⟨B, C, D, E, F, hΨ⟩ := exists_g2N (Ψ (xqB 1))
  rw [hΨ] at hfix
  obtain ⟨-, h2, h3, h4, h5⟩ := vanish_of_fixed_zpow l hfix
  have hC := h2 (zpow_ne_one_of hl (by decide))
  have hD := h3 (zpow_ne_one_of hl (by decide))
  have hE := h4 (zpow_ne_one_of hl (by decide))
  have hF := h5 (zpow_ne_one_of hl (by decide))
  subst hC hD hE hF
  exact ⟨B, scalar_law Ψ hH (P := xqB) (R := xqA) conj_xqB conj_xqA xqB_zero xqA_zero
    (Subtype.ext (hΨ.trans (pinnedX_a_eq_g2N B).symm))⟩

include hH hT in
private theorem rigid_scalars [Finite K] (hK : 8 ≤ Nat.card K) :
    ∃ κa κu κv κb : K, (∀ x, Ψ (xqA x) = xqB (κa * x)) ∧ (∀ x, Ψ (xqU x) = xqV (κu * x)) ∧
      (∀ x, Ψ (xqV x) = xqU (κv * x)) ∧ (∀ x, Ψ (xqB x) = xqA (κb * x)) := by
  obtain ⟨l, hl⟩ := exists_unit_pow_three_ne_one_of_card hK
  obtain ⟨κa, ha⟩ := scalars_a Ψ hH hT hl
  obtain ⟨κu, hu⟩ := scalars_u Ψ hH hT hl
  obtain ⟨κv, hv⟩ := scalars_v Ψ hH hT hl
  obtain ⟨κb, hb⟩ := scalars_b Ψ hH hT hl
  exact ⟨κa, κu, κv, κb, ha, hu, hv, hb⟩

end Scalars

section Calculus

variable [CharP K 2]

private theorem prod_swap_roots (p q q' p' F : K) :
    X g2b p * X g2v q * X g2u q' * X g2a p' * X g2c F =
      g2N 0 p' q' q p (F + q' * q + p' * p) := by
  rw [pinnedX_b_eq_g2N, g2N_mul_v, g2N_mul_u, g2N_mul_a, g2N_mul_c]
  exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by ring)

private theorem image_g2N {Ψ : Qr →* Qr} {κa κu κv κb : K} (sh : RigidShape Ψ κa κu κv κb)
    {x : Qr} {B C D E F : K} (hx : (x : ModGL Tag.G2 K) = g2N 0 B C D E F) :
    (Ψ x : ModGL Tag.G2 K) =
      g2N 0 (κb * E) (κv * D) (κu * C) (κa * B)
        (F + κv * D * (κu * C) + κb * E * (κa * B)) := by
  rw [eq_prod_of_coe hx, map_mul, map_mul, map_mul, map_mul, sh.a, sh.u, sh.v, sh.b, sh.c]
  exact prod_swap_roots _ _ _ _ _

private theorem rigid_kappa_ab {Ψ : Qr →* Qr} {κa κu κv κb : K}
    (sh : RigidShape Ψ κa κu κv κb) : κa * κb = 1 := by
  have hx : ((xqB 1 * xqA 1 : Qr) : ModGL Tag.G2 K) = g2N 0 1 0 0 1 1 := by
    have h := swap_b_a (1 : K) 1 1
    simp only [mul_one] at h
    show X g2b 1 * X g2a 1 = _
    rw [h]
    simp only [g2N, pinnedX_zero, one_mul, mul_one, mul_assoc]
  have h1 := image_g2N sh hx
  rw [map_mul, sh.b, sh.a] at h1
  have h2 : ((xqA (κb * 1) * xqB (κa * 1) : Qr) : ModGL Tag.G2 K) =
      g2N 0 (κb * 1) 0 0 (κa * 1) 0 := by
    show X g2a (κb * 1) * X g2b (κa * 1) = _
    rw [pinnedX_a_eq_g2N, g2N_mul_b]
    exact g2N_eq_g2N rfl rfl rfl rfl (by ring) rfl
  rw [h2] at h1
  have h3 := (g2N_injective h1).2.2.2.2.2
  linear_combination (-1 : K) * h3 - two_eq_zero_K (K := K)

private theorem rigid_kappa_uv {Ψ : Qr →* Qr} {κa κu κv κb : K}
    (sh : RigidShape Ψ κa κu κv κb) : κu * κv = 1 := by
  have hx : ((xqV 1 * xqU 1 : Qr) : ModGL Tag.G2 K) = g2N 0 0 1 1 0 1 := by
    have h := swap_v_u (1 : K) 1 1
    simp only [mul_one] at h
    show X g2v 1 * X g2u 1 = _
    rw [h]
    simp only [g2N, pinnedX_zero, one_mul, mul_one, mul_assoc]
  have h1 := image_g2N sh hx
  rw [map_mul, sh.v, sh.u] at h1
  have h2 : ((xqU (κv * 1) * xqV (κu * 1) : Qr) : ModGL Tag.G2 K) =
      g2N 0 0 (κv * 1) (κu * 1) 0 0 := by
    show X g2u (κv * 1) * X g2v (κu * 1) = _
    rw [pinnedX_u_eq_g2N, g2N_mul_v]
    exact g2N_eq_g2N rfl rfl rfl (by ring) rfl rfl
  rw [h2] at h1
  have h3 := (g2N_injective h1).2.2.2.2.2
  linear_combination (-1 : K) * h3 - two_eq_zero_K (K := K)

private theorem image_cr {cr : Qr →* Qr}
    (hcr : ∀ x, (cr x : ModGL Tag.G2 K) = X g2r 1 * (x : ModGL Tag.G2 K) * X g2r 1)
    {x : Qr} {B C D E F : K} (hx : (x : ModGL Tag.G2 K) = g2N 0 B C D E F) :
    (cr x : ModGL Tag.G2 K) =
      g2N 0 B (C + B) (D + B) (E + B + C + D) (F + B ^ 2 + B * C + C ^ 2) := by
  rw [hcr, hx, conj_r]
  exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by ring)

private theorem rigid_cube {Ψ cr : Qr →* Qr}
    (hcr : ∀ x, (cr x : ModGL Tag.G2 K) = X g2r 1 * (x : ModGL Tag.G2 K) * X g2r 1)
    (hcube : ∀ x, Ψ (cr (Ψ (cr (Ψ (cr x))))) = x) {κa κu κv κb : K}
    (sh : RigidShape Ψ κa κu κv κb) (hab : κa * κb = 1) (huv : κu * κv = 1) :
    κa = 1 ∧ κu = 1 ∧ κv = 1 ∧ κb = 1 := by
  have e1 : cr (xqB 1) = xqB 1 := by
    apply Subtype.ext
    rw [hcr]
    show X g2r 1 * X g2b 1 * X g2r 1 = X g2b 1
    rw [(commute_r_b (1 : K) 1).eq, mul_assoc, pinnedX_mul_self, mul_one]
  have h0 := hcube (xqB 1)
  rw [e1, sh.b] at h0
  have c1 := image_cr hcr (x := xqA (κb * 1)) (pinnedX_a_eq_g2N (κb * 1))
  have c2 := image_g2N sh c1
  have c3 := image_cr hcr c2
  have c4 := image_g2N sh c3
  rw [h0, xqB_coe, pinnedX_b_eq_g2N] at c4
  obtain ⟨-, -, hC, -, hE, -⟩ := g2N_injective c4
  have hκb : κb = 1 := by linear_combination (-κb) * hab - hE
  subst hκb
  have hκa : κa = 1 := by linear_combination hab
  have hκv : κv = 1 := by linear_combination (-1 : K) * hC - huv - two_eq_zero_K (K := K)
  have hκu : κu = 1 := by linear_combination huv - κu * hκv
  exact ⟨hκa, hκu, hκv, rfl⟩

private theorem rigid_eq_weyl {Ψ : Qr →* Qr} (sh : RigidShape Ψ 1 1 1 1) (x : Qr) :
    (Ψ x : ModGL Tag.G2 K) =
      weylElt Tag.G2 K g2ir 1 * (x : ModGL Tag.G2 K) * (weylElt Tag.G2 K g2ir 1)⁻¹ := by
  obtain ⟨B, C, D, E, F, hx⟩ := exists_g2N x
  have hg : g2N (0 : K) B C D E F = X g2a B * X g2u C * X g2v D * X g2b E * X g2c F := by
    simp only [g2N, pinnedX_zero, one_mul]
  have hR : weylElt Tag.G2 K g2ir 1 * (x : ModGL Tag.G2 K) * (weylElt Tag.G2 K g2ir 1)⁻¹ =
      X g2b B * X g2v C * X g2u D * X g2a E * X g2c F := by
    rw [hx, hg]
    change MulAut.conj (weylElt Tag.G2 K g2ir 1)
      (X g2a B * X g2u C * X g2v D * X g2b E * X g2c F) = _
    simp only [map_mul, MulAut.conj_apply, weylElt_conj g2ir isRoot_g2a,
      weylElt_conj g2ir isRoot_g2u, weylElt_conj g2ir isRoot_g2v, weylElt_conj g2ir isRoot_g2b,
      weylElt_conj g2ir isRoot_g2c, reflect_r_a, reflect_r_u, reflect_r_v, reflect_r_b,
      reflect_r_c]
  rw [hR, eq_prod_of_coe hx, map_mul, map_mul, map_mul, map_mul, sh.a, sh.u, sh.v, sh.b, sh.c]
  simp only [one_mul]
  rfl

end Calculus

theorem radA_conj_eq_weyl [Finite K] [CharP K 2]
    (hK : 8 ≤ Nat.card K)
    (Ψ : ↥(parabolicRadical Tag.G2 K {i1}) →* ↥(parabolicRadical Tag.G2 K {i1}))
    (hH : ∀ (s : Kˣ) (x y : ↥(parabolicRadical Tag.G2 K {i1})),
      (y : ModGL Tag.G2 K) = dT s 1 * (x : ModGL Tag.G2 K) * (dT s 1)⁻¹ →
        (Ψ y : ModGL Tag.G2 K) = dT s 1 * (Ψ x : ModGL Tag.G2 K) * (dT s 1)⁻¹)
    (hT : ∀ (l : Kˣ) (x y : ↥(parabolicRadical Tag.G2 K {i1})),
      (y : ModGL Tag.G2 K) =
          dT (l⁻¹ ^ 3) (l ^ 2) * (x : ModGL Tag.G2 K) * (dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ →
        (Ψ y : ModGL Tag.G2 K) =
          (dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ * (Ψ x : ModGL Tag.G2 K) * dT (l⁻¹ ^ 3) (l ^ 2))
    (hc : ∀ (c : K) (x : ↥(parabolicRadical Tag.G2 K {i1})), (x : ModGL Tag.G2 K) = X g2c c →
      (Ψ x : ModGL Tag.G2 K) = X g2c c)
    (cr : ↥(parabolicRadical Tag.G2 K {i1}) →* ↥(parabolicRadical Tag.G2 K {i1}))
    (hcr : ∀ x, (cr x : ModGL Tag.G2 K) = X g2r 1 * (x : ModGL Tag.G2 K) * X g2r 1)
    (hcube : ∀ x, Ψ (cr (Ψ (cr (Ψ (cr x))))) = x) (x : ↥(parabolicRadical Tag.G2 K {i1})) :
    (Ψ x : ModGL Tag.G2 K) =
      weylElt Tag.G2 K g2ir 1 * (x : ModGL Tag.G2 K) * (weylElt Tag.G2 K g2ir 1)⁻¹ := by
  obtain ⟨κa, κu, κv, κb, ha, hu, hv, hb⟩ := rigid_scalars Ψ hH hT hK
  have sh : RigidShape Ψ κa κu κv κb :=
    ⟨ha, hu, hv, hb, fun c => Subtype.ext (hc c (xqC c) rfl)⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ := rigid_cube hcr hcube sh (rigid_kappa_ab sh) (rigid_kappa_uv sh)
  exact rigid_eq_weyl sh x

end CFSG.Quasithin.F112R.St84.G2q

end
