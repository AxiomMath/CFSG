module

public import CFSG.Milestones.ASVolI.F429.C6L3
public import CFSG.Milestones.ASVolI.F429.C2L3
public import CFSG.Milestones.ASVolI.F429.aC4Gen
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpAut

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Counting

variable {F : Type} [Field F] [Finite F]

theorem burnsideF429_card_fiber_le {α : Type*} [Finite α] (σ : F ≃+* F) {l : F} (hl : l ≠ 0)
    (β : α → F) (S : Set (α × F)) (hS : ∀ p ∈ S, l * σ p.2 + β p.1 = p.2) :
    Nat.card S ≤ Nat.card (Prod.fst '' S) * Nat.card {a : F // σ a = a} := by
  classical
  let c₀ : α → F := fun a => if h : ∃ c, (a, c) ∈ S then h.choose else 0
  have hc₀ : ∀ p ∈ S, (p.1, c₀ p.1) ∈ S := by
    intro p hp
    have h : ∃ c, (p.1, c) ∈ S := ⟨p.2, hp⟩
    simp only [c₀, dif_pos h]
    exact h.choose_spec
  have hmem₂ : ∀ p ∈ S, l * σ (p.2 - c₀ p.1) = p.2 - c₀ p.1 := by
    intro p hp
    have h1 := hS p hp
    have h2 := hS _ (hc₀ p hp)
    rw [map_sub, mul_sub]
    linear_combination h1 - h2
  let S₂ : Set F := {c | l * σ c = c}
  let φ : S → (Prod.fst '' S) × S₂ := fun p =>
    (⟨p.1.1, p.1, p.2, rfl⟩, ⟨p.1.2 - c₀ p.1.1, hmem₂ p.1 p.2⟩)
  have hφ : Function.Injective φ := by
    intro p q hpq
    have h1 : p.1.1 = q.1.1 := congrArg (fun r : (Prod.fst '' S) × S₂ => (r.1 : α)) hpq
    have h2 : p.1.2 - c₀ p.1.1 = q.1.2 - c₀ q.1.1 :=
      congrArg (fun r : (Prod.fst '' S) × S₂ => (r.2 : F)) hpq
    rw [h1] at h2
    exact Subtype.ext (Prod.ext h1 (sub_left_injective h2))
  calc Nat.card S ≤ Nat.card ((Prod.fst '' S) × S₂) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (Prod.fst '' S) * Nat.card S₂ := Nat.card_prod _ _
    _ ≤ Nat.card (Prod.fst '' S) * Nat.card {a : F // σ a = a} :=
        Nat.mul_le_mul_left _ (burnsideF429_card_twisted_le σ hl S₂ fun _ hx => hx)

theorem burnsideF429_card_twisted_le_cube (σ : F ≃+* F) {l₁ l₂ l₃ : F} (hl₁ : l₁ ≠ 0)
    (hl₂ : l₂ ≠ 0) (hl₃ : l₃ ≠ 0) (β₁ : F → F) (β₂ : F × F → F) (S : Set ((F × F) × F))
    (hS : ∀ p ∈ S, l₁ * σ p.1.1 = p.1.1 ∧ l₂ * σ p.1.2 + β₁ p.1.1 = p.1.2 ∧
      l₃ * σ p.2 + β₂ p.1 = p.2) :
    Nat.card S ≤ Nat.card {a : F // σ a = a} ^ 3 := by
  have h1 := burnsideF429_card_fiber_le σ hl₃ β₂ S fun p hp => (hS p hp).2.2
  have h2 := burnsideF429_card_twisted_le_sq σ hl₁ hl₂ β₁ (Prod.fst '' S) (by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨(hS p hp).1, (hS p hp).2.1⟩)
  calc Nat.card S ≤ Nat.card (Prod.fst '' S) * Nat.card {a : F // σ a = a} := h1
    _ ≤ Nat.card {a : F // σ a = a} ^ 2 * Nat.card {a : F // σ a = a} := Nat.mul_le_mul_right _ h2
    _ = Nat.card {a : F // σ a = a} ^ 3 := by ring

end Counting

section SpUnipotent

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2 uElt_inj)

variable {F : Type} [Field F] [CharP F 2]

theorem burnsideF429_Sp_conjU_radA1 (A B C D b c d : F) :
    uElt A B C D * uElt 0 b c d * (uElt A B C D)⁻¹ = uElt 0 (b + A * d) (c + A ^ 2 * d) d := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [mul_inv_eq_iff_eq_mul, uElt_mul, uElt_mul]
  have e1 : A + 0 = 0 + A := by ring
  have e2 : B + b + A * d = b + A * d + B + 0 * D := by ring
  have e3 : C + c + A * b + A * 0 * d + B * 0 =
      c + A ^ 2 * d + C + 0 * B + 0 * A * D + (b + A * d) * A := by
    linear_combination (-(A ^ 2 * d)) * h2
  have e4 : D + d = d + D := by ring
  rw [e1, e2, e3, e4]

theorem burnsideF429_Sp_conjU_radA2 (A B C D a b c : F) :
    uElt A B C D * uElt a b c 0 * (uElt A B C D)⁻¹ = uElt a (b + D * a) c 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [mul_inv_eq_iff_eq_mul, uElt_mul, uElt_mul]
  have e1 : A + a = a + A := by ring
  have e2 : B + b + A * 0 = b + D * a + B + a * D := by linear_combination (-(a * D)) * h2
  have e3 : C + c + A * b + A * a * 0 + B * a =
      c + C + a * B + a * A * D + (b + D * a) * A := by
    linear_combination (-(a * A * D)) * h2
  have e4 : D + 0 = 0 + D := by ring
  rw [e1, e2, e3, e4]

theorem burnsideF429_Sp_conjU_center (A B C D b c : F) :
    uElt A B C D * uElt 0 b c 0 * (uElt A B C D)⁻¹ = uElt 0 b c 0 := by
  rw [mul_inv_eq_iff_eq_mul, uElt_mul, uElt_mul]
  have e1 : A + 0 = 0 + A := by ring
  have e2 : B + b + A * 0 = b + B + 0 * D := by ring
  have e3 : C + c + A * b + A * 0 * 0 + B * 0 = c + C + 0 * B + 0 * A * D + b * A := by ring
  have e4 : D + 0 = 0 + D := by ring
  rw [e1, e2, e3, e4]

variable [Finite F]

theorem burnsideF429_Sp_bor_decomp {g : antiSp F} (hg : g ∈ bor F) :
    ∃ (s t : Fˣ) (A B C D : F), g = dSp s t * uElt A B C D := by
  obtain ⟨h0, h1, -, -⟩ := upper_diag_ne_zero (upper_of_mem_normalizer hg)
  set s : Fˣ := Units.mk0 _ h0 with hs
  set t : Fˣ := Units.mk0 _ h1 with ht
  have hd : (dSp s t)⁻¹ ∈ bor F := inv_mem (dSp_mem_normalizer s t)
  have hdiag : ∀ i : Fin 4, i = 0 ∨ i = 1 →
      glMat (((dSp s t)⁻¹ * g : antiSp F) : GL (Fin 4) F) i i = 1 := by
    intro i hi
    have e := (dgHom F i).map_mul ⟨_, hd⟩ ⟨g, hg⟩
    rw [dgHom_apply, dgHom_apply, dgHom_apply] at e
    have e' : glMat (((dSp s t)⁻¹ * g : antiSp F) : GL (Fin 4) F) i i =
        glMat (((dSp s t)⁻¹ : antiSp F) : GL (Fin 4) F) i i *
          glMat ((g : antiSp F) : GL (Fin 4) F) i i := e
    rw [e', dSp_inv]
    rcases hi with rfl | rfl
    · rw [(glMat_dSp_diag (F := F) s⁻¹ t⁻¹).1, Units.val_inv_eq_inv_val, hs, Units.val_mk0,
        inv_mul_cancel₀ h0]
    · rw [(glMat_dSp_diag (F := F) s⁻¹ t⁻¹).2, Units.val_inv_eq_inv_val, ht, Units.val_mk0,
        inv_mul_cancel₀ h1]
  obtain ⟨A, B, C, D, hu⟩ := mem_U_of_dg_eq_one (mul_mem hd hg) (hdiag 0 (Or.inl rfl))
    (hdiag 1 (Or.inr rfl))
  exact ⟨s, t, A, B, C, D, by rw [← hu]; group⟩

omit [Finite F] in
theorem burnsideF429_zero_pow_two_pow (k : ℕ) : (0 : F) ^ 2 ^ k = 0 :=
  zero_pow (pow_ne_zero k two_ne_zero)

theorem burnsideF429_Sp_act_radA1 (s t : Fˣ) (A B C D : F) (k : ℕ) (b c d : F) :
    (MulAut.conj (dSp s t * uElt A B C D) * frobAut F ^ k) (uElt 0 b c d) =
      uElt 0 ((s : F) * t * (b ^ 2 ^ k + A * d ^ 2 ^ k))
        ((s : F) ^ 2 * (c ^ 2 ^ k + A ^ 2 * d ^ 2 ^ k)) ((t : F) ^ 2 * d ^ 2 ^ k) := by
  rw [MulAut.mul_apply, frobAut_pow_uElt, MulAut.conj_apply, burnsideF429_zero_pow_two_pow]
  calc dSp s t * uElt A B C D * uElt 0 (b ^ 2 ^ k) (c ^ 2 ^ k) (d ^ 2 ^ k) *
        (dSp s t * uElt A B C D)⁻¹
      = dSp s t * (uElt A B C D * uElt 0 (b ^ 2 ^ k) (c ^ 2 ^ k) (d ^ 2 ^ k) *
          (uElt A B C D)⁻¹) * (dSp s t)⁻¹ := by group
    _ = dSp s t * uElt 0 (b ^ 2 ^ k + A * d ^ 2 ^ k) (c ^ 2 ^ k + A ^ 2 * d ^ 2 ^ k) (d ^ 2 ^ k) *
          (dSp s t)⁻¹ := by rw [burnsideF429_Sp_conjU_radA1]
    _ = _ := by rw [dSp_conj_uElt, mul_zero]

theorem burnsideF429_Sp_act_radA2 (s t : Fˣ) (A B C D : F) (k : ℕ) (a b c : F) :
    (MulAut.conj (dSp s t * uElt A B C D) * frobAut F ^ k) (uElt a b c 0) =
      uElt ((s : F) * (t⁻¹ : Fˣ) * a ^ 2 ^ k) ((s : F) * t * (b ^ 2 ^ k + D * a ^ 2 ^ k))
        ((s : F) ^ 2 * c ^ 2 ^ k) 0 := by
  rw [MulAut.mul_apply, frobAut_pow_uElt, MulAut.conj_apply, burnsideF429_zero_pow_two_pow]
  calc dSp s t * uElt A B C D * uElt (a ^ 2 ^ k) (b ^ 2 ^ k) (c ^ 2 ^ k) 0 *
        (dSp s t * uElt A B C D)⁻¹
      = dSp s t * (uElt A B C D * uElt (a ^ 2 ^ k) (b ^ 2 ^ k) (c ^ 2 ^ k) 0 *
          (uElt A B C D)⁻¹) * (dSp s t)⁻¹ := by group
    _ = dSp s t * uElt (a ^ 2 ^ k) (b ^ 2 ^ k + D * a ^ 2 ^ k) (c ^ 2 ^ k) 0 * (dSp s t)⁻¹ := by
        rw [burnsideF429_Sp_conjU_radA2]
    _ = _ := by rw [dSp_conj_uElt, mul_zero]

theorem burnsideF429_Sp_act_center (s t : Fˣ) (A B C D : F) (k : ℕ) (b c : F) :
    (MulAut.conj (dSp s t * uElt A B C D) * frobAut F ^ k) (uElt 0 b c 0) =
      uElt 0 ((s : F) * t * b ^ 2 ^ k) ((s : F) ^ 2 * c ^ 2 ^ k) 0 := by
  rw [MulAut.mul_apply, frobAut_pow_uElt, MulAut.conj_apply, burnsideF429_zero_pow_two_pow]
  calc dSp s t * uElt A B C D * uElt 0 (b ^ 2 ^ k) (c ^ 2 ^ k) 0 * (dSp s t * uElt A B C D)⁻¹
      = dSp s t * (uElt A B C D * uElt 0 (b ^ 2 ^ k) (c ^ 2 ^ k) 0 * (uElt A B C D)⁻¹) *
          (dSp s t)⁻¹ := by group
    _ = dSp s t * uElt 0 (b ^ 2 ^ k) (c ^ 2 ^ k) 0 * (dSp s t)⁻¹ := by
        rw [burnsideF429_Sp_conjU_center]
    _ = _ := by rw [dSp_conj_uElt, mul_zero, mul_zero]

@[expose] noncomputable def burnsideF429_frobPow (F : Type) [Field F] [Finite F] [CharP F 2] (k : ℕ) :
    F ≃+* F :=
  RingEquiv.ofBijective (iterateFrobenius F 2 k)
    ⟨(iterateFrobenius F 2 k).injective,
      Finite.injective_iff_surjective.mp (iterateFrobenius F 2 k).injective⟩

theorem burnsideF429_frobPow_apply (k : ℕ) (x : F) : burnsideF429_frobPow F k x = x ^ 2 ^ k :=
  rfl

theorem burnsideF429_Sp_card_fix_radA1 {g : antiSp F} (hg : g ∈ bor F) (k : ℕ)
    {X : Subgroup (antiSp F)} (hXV : X ≤ radA1 F)
    (hfix : ∀ y ∈ X, (MulAut.conj g * frobAut F ^ k) y = y) :
    Nat.card X ≤ Nat.card {a : F // burnsideF429_frobPow F k a = a} ^ 3 := by
  obtain ⟨s, t, A, B, C, D, rfl⟩ := burnsideF429_Sp_bor_decomp hg
  set σ := burnsideF429_frobPow F k with hσ
  have hσa : ∀ x, σ x = x ^ 2 ^ k := burnsideF429_frobPow_apply k
  let S : Set ((F × F) × F) := {p | (MulAut.conj (dSp s t * uElt A B C D) * frobAut F ^ k)
    (uElt 0 p.1.2 p.2 p.1.1) = uElt 0 p.1.2 p.2 p.1.1}
  have hcoord : ∀ y : X, ∃ p : (F × F) × F, (y : antiSp F) = uElt 0 p.1.2 p.2 p.1.1 := fun y => by
    obtain ⟨b, c, d, h⟩ := hXV y.2
    exact ⟨((d, b), c), h⟩
  choose co hco using hcoord
  have hmem : ∀ y : X, co y ∈ S := fun y => by
    show (MulAut.conj (dSp s t * uElt A B C D) * frobAut F ^ k)
      (uElt 0 (co y).1.2 (co y).2 (co y).1.1) = uElt 0 (co y).1.2 (co y).2 (co y).1.1
    rw [← hco y]
    exact hfix y y.2
  have hinj : Function.Injective (fun y : X => (⟨co y, hmem y⟩ : S)) := by
    intro y y' h
    have h' : co y = co y' := congrArg Subtype.val h
    exact Subtype.ext (by rw [hco y, hco y', h'])
  refine (Nat.card_le_card_of_injective _ hinj).trans ?_
  refine burnsideF429_card_twisted_le_cube σ (l₁ := (t : F) ^ 2) (l₂ := (s : F) * t)
    (l₃ := (s : F) ^ 2) (pow_ne_zero 2 t.ne_zero) (mul_ne_zero s.ne_zero t.ne_zero)
    (pow_ne_zero 2 s.ne_zero) (fun d => (s : F) * t * A * σ d)
    (fun p => (s : F) ^ 2 * A ^ 2 * σ p.1) S ?_
  intro p hp
  have hp' : (MulAut.conj (dSp s t * uElt A B C D) * frobAut F ^ k)
      (uElt 0 p.1.2 p.2 p.1.1) = uElt 0 p.1.2 p.2 p.1.1 := hp
  rw [burnsideF429_Sp_act_radA1] at hp'
  obtain ⟨-, hb, hc, hd⟩ := uElt_inj hp'
  refine ⟨?_, ?_, ?_⟩
  · rw [hσa]; exact hd
  · rw [hσa, hσa]; linear_combination hb
  · rw [hσa, hσa]; linear_combination hc

theorem burnsideF429_Sp_card_fix_radA2 {g : antiSp F} (hg : g ∈ bor F) (k : ℕ)
    {X : Subgroup (antiSp F)} (hXV : X ≤ radA2 F)
    (hfix : ∀ y ∈ X, (MulAut.conj g * frobAut F ^ k) y = y) :
    Nat.card X ≤ Nat.card {a : F // burnsideF429_frobPow F k a = a} ^ 3 := by
  obtain ⟨s, t, A, B, C, D, rfl⟩ := burnsideF429_Sp_bor_decomp hg
  set σ := burnsideF429_frobPow F k with hσ
  have hσa : ∀ x, σ x = x ^ 2 ^ k := burnsideF429_frobPow_apply k
  let S : Set ((F × F) × F) := {p | (MulAut.conj (dSp s t * uElt A B C D) * frobAut F ^ k)
    (uElt p.1.1 p.1.2 p.2 0) = uElt p.1.1 p.1.2 p.2 0}
  have hcoord : ∀ y : X, ∃ p : (F × F) × F, (y : antiSp F) = uElt p.1.1 p.1.2 p.2 0 := fun y => by
    obtain ⟨a, b, c, h⟩ := hXV y.2
    exact ⟨((a, b), c), h⟩
  choose co hco using hcoord
  have hmem : ∀ y : X, co y ∈ S := fun y => by
    show (MulAut.conj (dSp s t * uElt A B C D) * frobAut F ^ k)
      (uElt (co y).1.1 (co y).1.2 (co y).2 0) = uElt (co y).1.1 (co y).1.2 (co y).2 0
    rw [← hco y]
    exact hfix y y.2
  have hinj : Function.Injective (fun y : X => (⟨co y, hmem y⟩ : S)) := by
    intro y y' h
    have h' : co y = co y' := congrArg Subtype.val h
    exact Subtype.ext (by rw [hco y, hco y', h'])
  refine (Nat.card_le_card_of_injective _ hinj).trans ?_
  refine burnsideF429_card_twisted_le_cube σ (l₁ := (s : F) * (t⁻¹ : Fˣ)) (l₂ := (s : F) * t)
    (l₃ := (s : F) ^ 2) (mul_ne_zero s.ne_zero (t⁻¹).ne_zero) (mul_ne_zero s.ne_zero t.ne_zero)
    (pow_ne_zero 2 s.ne_zero) (fun a => (s : F) * t * D * σ a) (fun _ => 0) S ?_
  intro p hp
  have hp' : (MulAut.conj (dSp s t * uElt A B C D) * frobAut F ^ k)
      (uElt p.1.1 p.1.2 p.2 0) = uElt p.1.1 p.1.2 p.2 0 := hp
  rw [burnsideF429_Sp_act_radA2] at hp'
  obtain ⟨ha, hb, hc, -⟩ := uElt_inj hp'
  refine ⟨?_, ?_, ?_⟩
  · rw [hσa]; exact ha
  · rw [hσa, hσa]; linear_combination hb
  · rw [hσa, add_zero]; exact hc

end SpUnipotent

section SpModelSetup

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_Sp4_model {f : ℕ} (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (Ψ : antiSp F ≃* ↥Gp),
      Nat.card F = 2 ^ f ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (antiUnipotent F).map (Gp.subtype.comp Ψ.toMonoidHom) ∧
      ∀ r ∈ M₁ ⊓ M₂, ∃ g ∈ bor F, ∃ k : ℕ, ∀ x : antiSp F,
        ((Ψ ((MulAut.conj g * frobAut F ^ k) x) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹ := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨marking, e1, e2⟩ := burnsideF4g_marking (c := .Sp4) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4gSp_yam_of_marking_ge marking
  rw [← e1, ← e2] at hTD
  obtain ⟨-, F, hFf, hFfin, hFchar, e, R, i, hFcard, hRi, hDd, he1, he2⟩ :=
    CFSG.Quasithin.H13.F431.SpOut2.spAmalgam_data_out (burnsideF4g_lieModel_Sp4 hf hyp.model)
      (burnsideF4d_amalgamExt hyp.toHypF_4_4g TD hTD)
  have hP : ∀ (X : Subgroup ↥Gp) (P : Subgroup (antiSp F)), X.map e.toMonoidHom = P →
      X = P.map e.symm.toMonoidHom := by
    intro X P hXP
    subst hXP
    ext x
    constructor
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
  have h₁ : M₁.subgroupOf Gp = (Subgroup.normalizer (R 0 : Set (antiSp F))).map
      e.symm.toMonoidHom := hP _ _ he1
  have h₂ : M₂.subgroupOf Gp = (Subgroup.normalizer (R 1 : Set (antiSp F))).map
      e.symm.toMonoidHom := hP _ _ he2
  have hBor : Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
      Subgroup.normalizer (R 1 : Set (antiSp F)) = bor F :=
    CFSG.QuasithinUnique.Borel252.BorelData.inf_norm hDd.borel
  have hU : pCoreOf 2 (Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
      Subgroup.normalizer (R 1 : Set (antiSp F))) = antiUnipotent F := by
    rw [hBor]
    exact CFSG.QuasithinUnique.Borel252.pCoreOf_normalizer_sylow hDd.borel.sylow
  refine ⟨F, hFf, hFfin, hFchar, e.symm, hFcard, ?_, ?_⟩
  · have hB : (M₁ ⊓ M₂).subgroupOf Gp = (Subgroup.normalizer (R 0 : Set (antiSp F)) ⊓
        Subgroup.normalizer (R 1 : Set (antiSp F))).map e.symm.toMonoidHom := by
      rw [burnsideF429a_subgroupOf_inf, h₁, h₂, Subgroup.map_inf_eq _ _ _ e.symm.injective]
    have hφ : Function.Injective (Gp.subtype.comp e.symm.toMonoidHom) :=
      Gp.subtype_injective.comp e.symm.injective
    rw [burnsideF429_inf_eq_map e.symm hB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, hU]
  · intro r hr
    obtain ⟨β, hβ₁, hβ₂, hβ⟩ := burnsideF429_model_aut e.symm h₁ h₂ hr
    have hA0 : ∀ x, x ∈ R 0 ↔ β x ∈ R 0 :=
      (mem_autStab_iff_of_normalizer hDd.borel.core₁ β).mp (fun y => (hβ₁ y).symm)
    have hA1 : ∀ x, x ∈ R 1 ↔ β x ∈ R 1 :=
      (mem_autStab_iff_of_normalizer hDd.borel.core₂ β).mp (fun y => (hβ₂ y).symm)
    have hst : StabRad β := by
      rcases hRi with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨fun x => (hA0 x).symm, fun x => (hA1 x).symm⟩
      · exact ⟨fun x => (hA1 x).symm, fun x => (hA0 x).symm⟩
    obtain ⟨g, hg, k, hgk⟩ := aut_form_both hf hFcard hst
    exact ⟨g, hg, k, fun x => by rw [← hgk]; exact hβ x⟩

end SpModelSetup

section Clause6

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2 uElt_inj elementary_le_radA1_or_radA2
  card_radicals mem_antiUnipotentCenter_iff_central radA1_le_antiUnipotent
  antiUnipotentCenter_le_radA1 mul_self_of_mem_radA1)

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}


theorem burnsideF429_c6_Sp4 {f : ℕ} (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C6 .Sp4 f Gp M₁ M₂ T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, hFf, hFfin, hFchar, Ψ, hFcard, hS, hform⟩ := burnsideF429_Sp4_model hyp hf
  set φ : antiSp F →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hf1 : 1 ≤ f := le_trans (by norm_num) hf
  have hTG := burnsideF429_T_inf_Gp hyp hT
  have hST := burnsideF429_sbar_le (Gp := Gp) hT
  have hinner : ∀ (r : E) (g : antiSp F),
      (∀ x, ((Ψ (MulAut.conj g x) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹) → r ∈ Gp :=
    fun r g h => burnsideF429_mem_of_inner hyp.centralizer_trivial Ψ h ⟨g, rfl⟩
  have hinv : ∀ t : E, t ∉ Gp → t * t = 1 → ∀ g ∈ bor F, ∀ k : ℕ,
      (∀ x, ((Ψ ((MulAut.conj g * frobAut F ^ k) x) : ↥Gp) : E) = t * ((Ψ x : ↥Gp) : E) * t⁻¹) →
      Even f ∧ (∀ x : F, x ^ 2 ^ k = x ^ 2 ^ (f / 2)) ∧ frobAut F ^ (2 * k) = 1 := by
    intro t htG htt g hg k hgk
    have hβ2 : (MulAut.conj g * frobAut F ^ k) ^ 2 = 1 :=
      burnsideF429a_pow_eq_one_of_intertwine Ψ hgk (n := 2) (by rw [pow_two]; exact htt)
    have hFr2 : frobAut F ^ (2 * k) = 1 := by
      rw [pow_two, burnsideF429_conj_mul_conj, ← pow_add, ← two_mul] at hβ2
      have h1 : MulAut.conj (g * (frobAut F ^ k) g)⁻¹ = frobAut F ^ (2 * k) := by
        rw [map_inv]
        exact (eq_inv_of_mul_eq_one_right hβ2).symm
      rw [← h1, conj_eq_frobAut_pow hf1 hFcard h1, map_one]
    have hFr1 : frobAut F ^ k ≠ 1 := by
      intro h
      apply htG
      refine hinner t g fun x => ?_
      have := hgk x
      rwa [h, mul_one] at this
    set σ := burnsideF429_frobPow F k with hσ
    have hσa : ∀ x, σ x = x ^ 2 ^ k := burnsideF429_frobPow_apply k
    have hσ1 : σ ≠ 1 := by
      intro h
      apply hFr1
      refine frobAut_pow_eq_one_of_fix fun x => ?_
      rw [← hσa, h]
      rfl
    have hσσ : σ * σ = 1 := by
      refine RingEquiv.ext fun x => ?_
      show σ (σ x) = x
      have hx := congrArg (fun h : MulAut (antiSp F) => h (uElt x 0 0 0)) hFr2
      simp only [frobAut_pow_uElt, MulAut.one_apply] at hx
      have hx' := (uElt_inj hx).1
      rw [hσa, hσa, ← pow_mul, ← pow_add, ← two_mul]
      exact hx'
    obtain ⟨hfe, hσf⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution hf1 hFcard
        hσ1 hσσ
    exact ⟨hfe, fun x => by rw [← hσa]; exact hσf x, hFr2⟩
  have hcardR : Nat.card ((radA1 F).map φ) = (2 ^ f) ^ 3 := by
    rw [Subgroup.card_map_of_injective hφ, (card_radicals (K := F)).2.1, hFcard]
  refine burnsideF429_c6_of' (R := (radA1 F).map φ) (W := (antiUnipotentCenter F).map φ) hST ?_
    (isElemAbelian_radA1.map φ) ?_ ?_ ?_ ?_ ?_
  · rw [hS]
    exact Subgroup.map_mono radA1_le_antiUnipotent
  ·
    intro A hAT hAe hAS
    obtain ⟨t, htA, htS⟩ := SetLike.not_le_iff_exists.mp hAS
    have htT := hAT htA
    have htt : t * t = 1 := by rw [← pow_two]; exact hAe.2 t htA
    have htG : t ∉ Gp := fun h => htS (by rw [← hTG]; exact ⟨htT, h⟩)
    have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := isMulCommutative_iff_of_setLike.mp hAe.1
    obtain ⟨g, hg, k, hgk⟩ := hform t (hT.1 htT)
    obtain ⟨hfe, hσk, hFr2⟩ := hinv t htG htt g hg k hgk
    have hsplit : ∀ a ∈ A, a ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
        t * a ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
      intro a haA haS
      have haa : a * a = 1 := by rw [← pow_two]; exact hAe.2 a haA
      have haG : a ∉ Gp := fun h => haS (by rw [← hTG]; exact ⟨hAT haA, h⟩)
      obtain ⟨g', hg', k', hgk'⟩ := hform a (hT.1 (hAT haA))
      obtain ⟨-, hσk', -⟩ := hinv a haG haa g' hg' k' hgk'
      have hFr : frobAut F ^ k' = frobAut F ^ k := by
        refine MulEquiv.ext fun x => mat_ext ?_
        rw [mat_frobAut_pow, mat_frobAut_pow]
        ext i j
        simp only [Matrix.map_apply]
        rw [hσk, hσk']
      have hprod : MulAut.conj (g * (frobAut F ^ k) g') =
          (MulAut.conj g * frobAut F ^ k) * (MulAut.conj g' * frobAut F ^ k') := by
        rw [hFr, burnsideF429_conj_mul_conj, ← pow_add, ← two_mul, hFr2, mul_one]
      have hta : t * a ∈ Gp := by
        refine hinner (t * a) (g * (frobAut F ^ k) g') fun x => ?_
        rw [hprod, MulAut.mul_apply, hgk, hgk']
        group
      rw [← hTG]
      exact ⟨T.mul_mem htT (hAT haA), hta⟩
    have hcardA := burnsideF429_card_le_two_mul_of htA htt hsplit
    set X : Subgroup E := A ⊓ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hXdef
    have hy2 : 2 ≤ 2 ^ (f / 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (f / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hX : Nat.card X ≤ (2 ^ (f / 2)) ^ 3 := by
      have hXr : X ≤ φ.range := (inf_le_right.trans hS.le).trans (Subgroup.map_le_range φ _)
      have hXX : (X.comap φ).map φ = X := Subgroup.map_comap_eq_self hXr
      have hX'U : X.comap φ ≤ antiUnipotent F := fun y hy =>
        (Subgroup.mem_map_iff_mem hφ).mp (by rw [← hS]; exact hy.2)
      have hX'2 : ∀ y ∈ X.comap φ, y * y = 1 := fun y hy =>
        hφ (by rw [map_mul, map_one, ← pow_two]; exact hAe.2 _ hy.1)
      have hfix : ∀ y ∈ X.comap φ, (MulAut.conj g * frobAut F ^ k) y = y := by
        intro y hy
        apply hφ
        rw [hφx, hgk, ← hφx, hAcomm t htA _ hy.1, mul_inv_cancel_right]
      have hN : Nat.card {a : F // burnsideF429_frobPow F k a = a} ≤ 2 ^ (f / 2) :=
        CFSG.SeitzReduction.natCard_le_of_forall_pow_eq_self (by omega)
          {a : F | burnsideF429_frobPow F k a = a}
          fun a ha => by
            have ha' : burnsideF429_frobPow F k a = a := ha
            rwa [burnsideF429_frobPow_apply, hσk] at ha'
      rw [← hXX, Subgroup.card_map_of_injective hφ]
      rcases elementary_le_radA1_or_radA2 hX'U hX'2 with h | h
      · exact (burnsideF429_Sp_card_fix_radA1 hg k h hfix).trans (Nat.pow_le_pow_left hN 3)
      · exact (burnsideF429_Sp_card_fix_radA2 hg k h hfix).trans (Nat.pow_le_pow_left hN 3)
    have hsq : (2 ^ (f / 2)) ^ 2 = 2 ^ f := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp hfe)]
    rw [hcardR, ← hsq]
    have h8 : 8 ≤ (2 ^ (f / 2)) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (2 ^ (f / 2)) ^ 3 := Nat.pow_le_pow_left hy2 3
    calc Nat.card A ≤ 2 * Nat.card X := hcardA
      _ ≤ 2 * (2 ^ (f / 2)) ^ 3 := Nat.mul_le_mul_left 2 hX
      _ < ((2 ^ (f / 2)) ^ 2) ^ 3 := by
        have e : ((2 ^ (f / 2)) ^ 2) ^ 3 = (2 ^ (f / 2)) ^ 3 * (2 ^ (f / 2)) ^ 3 := by ring
        rw [e]
        nlinarith
  ·
    rw [hS]
    exact Subgroup.map_mono (antiUnipotentCenter_le_radA1.trans radA1_le_antiUnipotent)
  ·
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [hS] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    rw [← map_mul, ← map_mul, ((mem_antiUnipotentCenter_iff_central z).mp hz).2 p hp]
  ·
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_pow, pow_two, mul_self_of_mem_radA1 (antiUnipotentCenter_le_radA1 hz), map_one]
  ·
    rintro r ⟨hrT, hrc⟩
    obtain ⟨g, hg, k, hgk⟩ := hform r (hT.1 hrT)
    obtain ⟨s, t, A₀, B₀, C₀, D₀, rfl⟩ := burnsideF429_Sp_bor_decomp hg
    have hfixZ : ∀ b : F, (MulAut.conj (dSp s t * uElt A₀ B₀ C₀ D₀) * frobAut F ^ k)
        (uElt 0 b 0 0) = uElt 0 b 0 0 := by
      intro b
      apply hφ
      have hz : φ (uElt 0 b 0 0) ∈ (antiUnipotentCenter F).map φ := ⟨_, ⟨b, 0, rfl⟩, rfl⟩
      have hc := Subgroup.mem_centralizer_iff.mp hrc _ hz
      rw [hφx, hgk, ← hφx, ← hc, mul_inv_cancel_right]
    have hb : ∀ b : F, (s : F) * t * b ^ 2 ^ k = b := fun b => by
      have := hfixZ b
      rw [burnsideF429_Sp_act_center] at this
      exact (uElt_inj this).2.1
    have hst1 : (s : F) * t = 1 := by
      have := hb 1
      rwa [one_pow, mul_one] at this
    have hFr : frobAut F ^ k = 1 := frobAut_pow_eq_one_of_fix fun x => by
      have := hb x
      rwa [hst1, one_mul] at this
    have hrG : r ∈ Gp := hinner r _ fun x => by
      have := hgk x
      rwa [hFr, mul_one] at this
    rw [← hTG]
    exact ⟨hrT, hrG⟩

end Clause6

end CFSG.ASVolI
