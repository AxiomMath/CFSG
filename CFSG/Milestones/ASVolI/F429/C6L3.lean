module

public import CFSG.Milestones.ASVolI.F429.C6Gen
public import CFSG.Milestones.ASVolI.F429.Gen
public import CFSG.Milestones.ASVolI.F4L3Aut
public import CFSG.LocalAnalysis.SeitzReduction.Fusion

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34

section Counting

variable {F : Type} [Field F] [Finite F]

theorem burnsideF429_card_twisted_le (σ : F ≃+* F) {l : F} (hl : l ≠ 0) (S : Set F)
    (hS : ∀ x ∈ S, l * σ x = x) : Nat.card S ≤ Nat.card {a : F // σ a = a} := by
  by_cases h : ∃ x₀ ∈ S, x₀ ≠ 0
  · obtain ⟨x₀, hx₀S, hx₀⟩ := h
    have h₀ := hS x₀ hx₀S
    have hσx₀ : σ x₀ ≠ 0 := fun h0 => hx₀ (by rw [← h₀, h0, mul_zero])
    have hmem : ∀ x : S, σ ((x : F) * x₀⁻¹) = (x : F) * x₀⁻¹ := by
      intro x
      have h₁ := hS x x.2
      have e : σ x * (σ x₀)⁻¹ = (l * σ x) * (l * σ x₀)⁻¹ := by
        rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hl, one_mul]
      rw [map_mul, map_inv₀, e, h₁, h₀]
    refine Nat.card_le_card_of_injective (fun x => ⟨(x : F) * x₀⁻¹, hmem x⟩) ?_
    intro x y hxy
    have h' : (x : F) * x₀⁻¹ = (y : F) * x₀⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_right_cancel₀ (inv_ne_zero hx₀) h')
  · push_neg at h
    refine Nat.card_le_card_of_injective (fun _ => (⟨0, map_zero σ⟩ : {a : F // σ a = a})) ?_
    intro a b _
    exact Subtype.ext (by rw [h a a.2, h b b.2])

theorem burnsideF429_card_twisted_le_sq (σ : F ≃+* F) {l₁ l₂ : F} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (β : F → F) (S : Set (F × F))
    (hS : ∀ p ∈ S, l₁ * σ p.1 = p.1 ∧ l₂ * σ p.2 + β p.1 = p.2) :
    Nat.card S ≤ Nat.card {a : F // σ a = a} ^ 2 := by
  classical
  let c₀ : F → F := fun a => if h : ∃ c, (a, c) ∈ S then h.choose else 0
  have hc₀ : ∀ p ∈ S, (p.1, c₀ p.1) ∈ S := by
    intro p hp
    have h : ∃ c, (p.1, c) ∈ S := ⟨p.2, hp⟩
    simp only [c₀, dif_pos h]
    exact h.choose_spec
  have hmem₂ : ∀ p ∈ S, l₂ * σ (p.2 - c₀ p.1) = p.2 - c₀ p.1 := by
    intro p hp
    have h1 := (hS p hp).2
    have h2 := (hS _ (hc₀ p hp)).2
    rw [map_sub, mul_sub]
    linear_combination h1 - h2
  let S₁ : Set F := {a | l₁ * σ a = a}
  let S₂ : Set F := {c | l₂ * σ c = c}
  let φ : S → S₁ × S₂ := fun p => (⟨p.1.1, (hS p.1 p.2).1⟩, ⟨p.1.2 - c₀ p.1.1, hmem₂ p.1 p.2⟩)
  have hφ : Function.Injective φ := by
    intro p q hpq
    have h1 : p.1.1 = q.1.1 := congrArg (fun r : S₁ × S₂ => (r.1 : F)) hpq
    have h2 : p.1.2 - c₀ p.1.1 = q.1.2 - c₀ q.1.1 := congrArg (fun r : S₁ × S₂ => (r.2 : F)) hpq
    rw [h1] at h2
    exact Subtype.ext (Prod.ext h1 (sub_left_injective h2))
  calc Nat.card S ≤ Nat.card (S₁ × S₂) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card S₁ * Nat.card S₂ := Nat.card_prod _ _
    _ ≤ Nat.card {a : F // σ a = a} * Nat.card {a : F // σ a = a} :=
        Nat.mul_le_mul (burnsideF429_card_twisted_le σ hl₁ S₁ fun _ hx => hx)
          (burnsideF429_card_twisted_le σ hl₂ S₂ fun _ hx => hx)
    _ = Nat.card {a : F // σ a = a} ^ 2 := (sq _).symm

end Counting

theorem burnsideF429_isElemAbelian_comap {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {U : Subgroup H} (hU : IsElemAbelian 2 U) :
    IsElemAbelian 2 (U.comap φ) := by
  refine ⟨isMulCommutative_iff_of_setLike.mpr fun a ha b hb => hφ ?_, fun x hx => hφ ?_⟩
  · rw [map_mul, map_mul]
    exact isMulCommutative_iff_of_setLike.mp hU.1 _ ha _ hb
  · rw [map_pow, map_one]
    exact hU.2 _ hx

section P3

variable {F : Type} [Field F] [CharP F 2]

theorem burnsideF429_L3_sq (a b c : F) : (wP c * xP a * yP b) ^ 2 = wP (a * b) := by
  rw [pow_two]
  calc wP c * xP a * yP b * (wP c * xP a * yP b)
      = wP c * xP a * (yP b * wP c) * xP a * yP b := by group
    _ = wP c * xP a * (wP c * yP b) * xP a * yP b := by rw [wP_mul_yP]
    _ = wP c * (xP a * wP c) * yP b * xP a * yP b := by group
    _ = wP c * (wP c * xP a) * yP b * xP a * yP b := by rw [wP_mul_xP]
    _ = (wP c * wP c) * xP a * (yP b * xP a) * yP b := by group
    _ = xP a * (wP (a * b) * xP a * yP b) * yP b := by rw [wP_mul_self, one_mul, yP_mul_xP]
    _ = (xP a * wP (a * b)) * xP a * (yP b * yP b) := by group
    _ = (wP (a * b) * xP a) * xP a * (yP b * yP b) := by rw [wP_mul_xP]
    _ = wP (a * b) * (xP a * xP a) * (yP b * yP b) := by group
    _ = wP (a * b) := by rw [xP_mul_self, yP_mul_self, mul_one, mul_one]

theorem burnsideF429_L3_V1_inj {a c a' c' : F} (h : xP a * wP c = xP a' * wP c') :
    a = a' ∧ c = c' := by
  have h1 : xP (a + a') * wP (c + c') = yP 0 * wP 0 := by
    rw [← V1_mul, h, V1_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, xP_zero, yP_zero]
  obtain ⟨ha, -, hc⟩ := xP_wP_eq_yP_wP h1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  exact ⟨by linear_combination ha - a' * h2, by linear_combination hc - c' * h2⟩

theorem burnsideF429_L3_V2_inj {b c b' c' : F} (h : yP b * wP c = yP b' * wP c') :
    b = b' ∧ c = c' := by
  have h1 : xP 0 * wP 0 = yP (b + b') * wP (c + c') := by
    rw [← V2_mul, h, V2_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, xP_zero, yP_zero]
  obtain ⟨-, hb, hc⟩ := xP_wP_eq_yP_wP h1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  exact ⟨by linear_combination hb - b' * h2, by linear_combination -hc - c' * h2⟩

theorem burnsideF429_L3_wP_inj {c c' : F} (h : wP c = wP c') : c = c' := by
  have h1 : xP 0 * wP c = yP 0 * wP c' := by rw [xP_zero, yP_zero, h]
  exact (xP_wP_eq_yP_wP h1).2.2

theorem burnsideF429_L3_card_V1 [Finite F] :
    Nat.card (V1 : Subgroup (projectiveSL 3 F)) = Nat.card F ^ 2 := by
  have hbij : Function.Bijective (fun p : F × F =>
      (⟨xP p.1 * wP p.2, p.1, p.2, rfl⟩ : (V1 : Subgroup (projectiveSL 3 F)))) := by
    refine ⟨fun p q hpq => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := burnsideF429_L3_V1_inj (congrArg Subtype.val hpq)
      exact Prod.ext h1 h2
    · rintro ⟨g, a, c, rfl⟩
      exact ⟨(a, c), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, sq]

theorem burnsideF429_L3_card_V2 [Finite F] :
    Nat.card (V2 : Subgroup (projectiveSL 3 F)) = Nat.card F ^ 2 := by
  have hbij : Function.Bijective (fun p : F × F =>
      (⟨yP p.1 * wP p.2, p.1, p.2, rfl⟩ : (V2 : Subgroup (projectiveSL 3 F)))) := by
    refine ⟨fun p q hpq => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := burnsideF429_L3_V2_inj (congrArg Subtype.val hpq)
      exact Prod.ext h1 h2
    · rintro ⟨g, b, c, rfl⟩
      exact ⟨(b, c), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, sq]

theorem burnsideF429_L3_elemAb_le {B : Subgroup (projectiveSL 3 F)}
    (hBU : B ≤ projUnitriangular 3 F) (hB : IsElemAbelian 2 B) : B ≤ V1 ∨ B ≤ V2 := by
  by_contra h
  rw [not_or, SetLike.not_le_iff_exists, SetLike.not_le_iff_exists] at h
  obtain ⟨⟨g, hgB, hgV⟩, ⟨g', hg'B, hg'V⟩⟩ := h
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp (hBU hgB)
  obtain ⟨c', a', b', rfl⟩ := mem_Ubar.mp (hBU hg'B)
  have hsq : ∀ x ∈ B, x ^ 2 = 1 := hB.2
  have hab : a * b = 0 := by
    have := hsq _ hgB
    rwa [burnsideF429_L3_sq, wP_eq_one_iff] at this
  have ha'b' : a' * b' = 0 := by
    have := hsq _ hg'B
    rwa [burnsideF429_L3_sq, wP_eq_one_iff] at this
  have hb : b ≠ 0 := by
    rintro rfl
    exact hgV ⟨a, c, by rw [yP_zero, mul_one, wP_mul_xP]⟩
  have ha' : a' ≠ 0 := by
    rintro rfl
    exact hg'V ⟨b', c', by rw [xP_zero, mul_one, wP_mul_yP]⟩
  have ha : a = 0 := (mul_eq_zero.mp hab).resolve_right hb
  have hb' : b' = 0 := (mul_eq_zero.mp ha'b').resolve_left ha'
  subst ha hb'
  have hprod : (wP c * xP 0 * yP b) * (wP c' * xP a' * yP 0) =
      wP (c + c' + a' * b) * xP a' * yP b := by
    rw [xP_zero, yP_zero, mul_one, mul_one, wP_add, wP_add]
    calc wP c * yP b * (wP c' * xP a') = wP c * (yP b * wP c') * xP a' := by group
      _ = wP c * (wP c' * yP b) * xP a' := by rw [wP_mul_yP]
      _ = wP c * wP c' * (yP b * xP a') := by group
      _ = wP c * wP c' * (wP (a' * b) * xP a' * yP b) := by rw [yP_mul_xP]
      _ = wP c * wP c' * wP (a' * b) * xP a' * yP b := by group
  have := hsq _ (B.mul_mem hgB hg'B)
  rw [hprod, burnsideF429_L3_sq, wP_eq_one_iff] at this
  exact (mul_ne_zero ha' hb) this

theorem burnsideF429_L3_wP_comm (c : F) {g : projectiveSL 3 F}
    (hg : g ∈ projUnitriangular 3 F) : wP c * g = g * wP c := by
  obtain ⟨c', a, b, rfl⟩ := mem_Ubar.mp hg
  calc wP c * (wP c' * xP a * yP b) = wP c * wP c' * xP a * yP b := by group
    _ = wP c' * wP c * xP a * yP b := by rw [← wP_add, ← wP_add, add_comm]
    _ = wP c' * (wP c * xP a) * yP b := by group
    _ = wP c' * (xP a * wP c) * yP b := by rw [wP_mul_xP]
    _ = wP c' * xP a * (wP c * yP b) := by group
    _ = wP c' * xP a * (yP b * wP c) := by rw [wP_mul_yP]
    _ = wP c' * xP a * yP b * wP c := by group

theorem burnsideF429_L3_conjU_V1 {u : projectiveSL 3 F} (hu : u ∈ projUnitriangular 3 F) :
    ∃ b₀ : F, ∀ a c : F, u * (xP a * wP c) * u⁻¹ = xP a * wP (c + a * b₀) := by
  obtain ⟨c₀, a₀, b₀, rfl⟩ := mem_Ubar.mp hu
  refine ⟨b₀, fun a c => ?_⟩
  have e1 : yP b₀ * (xP a * wP c) * (yP b₀)⁻¹ = xP a * wP (c + a * b₀) := by
    calc yP b₀ * (xP a * wP c) * (yP b₀)⁻¹
        = (yP b₀ * xP a * (yP b₀)⁻¹) * (yP b₀ * wP c * (yP b₀)⁻¹) := by group
      _ = (xP a * wP (a * b₀)) * wP c := by
          rw [yP_conj_xP, ← wP_mul_yP, mul_inv_cancel_right]
      _ = xP a * wP (c + a * b₀) := by rw [mul_assoc, ← wP_add, add_comm]
  have hv : xP a * wP (c + a * b₀) ∈ (V1 : Subgroup (projectiveSL 3 F)) := ⟨a, c + a * b₀, rfl⟩
  have hx : xP a₀ ∈ (V1 : Subgroup (projectiveSL 3 F)) := ⟨a₀, 0, by rw [wP_zero, mul_one]⟩
  have e2 : xP a₀ * (xP a * wP (c + a * b₀)) * (xP a₀)⁻¹ = xP a * wP (c + a * b₀) := by
    rw [isMulCommutative_iff_of_setLike.mp isElemAbelian_V1.1 _ hx _ hv, mul_inv_cancel_right]
  have e3 : wP c₀ * (xP a * wP (c + a * b₀)) * (wP c₀)⁻¹ = xP a * wP (c + a * b₀) := by
    rw [burnsideF429_L3_wP_comm c₀ (V1_le_U hv), mul_inv_cancel_right]
  calc wP c₀ * xP a₀ * yP b₀ * (xP a * wP c) * (wP c₀ * xP a₀ * yP b₀)⁻¹
      = wP c₀ * (xP a₀ * (yP b₀ * (xP a * wP c) * (yP b₀)⁻¹) * (xP a₀)⁻¹) * (wP c₀)⁻¹ := by
        group
    _ = xP a * wP (c + a * b₀) := by rw [e1, e2, e3]

theorem burnsideF429_L3_conjU_V2 {u : projectiveSL 3 F} (hu : u ∈ projUnitriangular 3 F) :
    ∃ a₀ : F, ∀ b c : F, u * (yP b * wP c) * u⁻¹ = yP b * wP (c + a₀ * b) := by
  obtain ⟨c₀, a₀, b₀, rfl⟩ := mem_Ubar.mp hu
  refine ⟨a₀, fun b c => ?_⟩
  have hv : yP b * wP c ∈ (V2 : Subgroup (projectiveSL 3 F)) := ⟨b, c, rfl⟩
  have hy : yP b₀ ∈ (V2 : Subgroup (projectiveSL 3 F)) := ⟨b₀, 0, by rw [wP_zero, mul_one]⟩
  have e1 : yP b₀ * (yP b * wP c) * (yP b₀)⁻¹ = yP b * wP c := by
    rw [isMulCommutative_iff_of_setLike.mp isElemAbelian_V2.1 _ hy _ hv, mul_inv_cancel_right]
  have e2 : xP a₀ * (yP b * wP c) * (xP a₀)⁻¹ = yP b * wP (c + a₀ * b) := by
    calc xP a₀ * (yP b * wP c) * (xP a₀)⁻¹
        = (xP a₀ * yP b * (xP a₀)⁻¹) * (xP a₀ * wP c * (xP a₀)⁻¹) := by group
      _ = (wP (a₀ * b) * yP b) * wP c := by
          rw [xP_conj_yP, ← wP_mul_xP, mul_inv_cancel_right]
      _ = yP b * wP (c + a₀ * b) := by rw [wP_mul_yP, mul_assoc, ← wP_add, add_comm]
  have hv' : yP b * wP (c + a₀ * b) ∈ (V2 : Subgroup (projectiveSL 3 F)) := ⟨b, c + a₀ * b, rfl⟩
  have e3 : wP c₀ * (yP b * wP (c + a₀ * b)) * (wP c₀)⁻¹ = yP b * wP (c + a₀ * b) := by
    rw [burnsideF429_L3_wP_comm c₀ (V2_le_U hv'), mul_inv_cancel_right]
  calc wP c₀ * xP a₀ * yP b₀ * (yP b * wP c) * (wP c₀ * xP a₀ * yP b₀)⁻¹
      = wP c₀ * (xP a₀ * (yP b₀ * (yP b * wP c) * (yP b₀)⁻¹) * (xP a₀)⁻¹) * (wP c₀)⁻¹ := by
        group
    _ = yP b * wP (c + a₀ * b) := by rw [e1, e2, e3]

variable [Finite F]

theorem burnsideF429_L3_card_fix_V1 {u : projectiveSL 3 F} (hu : u ∈ projUnitriangular 3 F)
    (x y z : Fˣ) (σ : F ≃+* F) {B : Subgroup (projectiveSL 3 F)} (hBV : B ≤ V1)
    (hfix : ∀ g ∈ B,
      (MulAut.conj u * conjAut 3 F (burnsideF447_diagGL x y z) * fieldAut 3 F σ) g = g) :
    Nat.card B ≤ Nat.card {a : F // σ a = a} ^ 2 := by
  obtain ⟨b₀, hb₀⟩ := burnsideF429_L3_conjU_V1 hu
  set θ := MulAut.conj u * conjAut 3 F (burnsideF447_diagGL x y z) * fieldAut 3 F σ with hθ
  have hact : ∀ a c : F, θ (xP a * wP c) = xP ((x : F) * ((y⁻¹ : Fˣ) : F) * σ a) *
      wP ((x : F) * ((z⁻¹ : Fˣ) : F) * σ c + (x : F) * ((y⁻¹ : Fˣ) : F) * σ a * b₀) := by
    intro a c
    rw [hθ, MulAut.mul_apply, MulAut.mul_apply, map_mul, fieldAut_xP, fieldAut_wP, map_mul,
      burnsideF447_conj_diag_xP, burnsideF447_conj_diag_wP, MulAut.conj_apply, hb₀]
  let S : Set (F × F) := {p | θ (xP p.1 * wP p.2) = xP p.1 * wP p.2}
  have hcoord : ∀ g : B, ∃ p : F × F, (g : projectiveSL 3 F) = xP p.1 * wP p.2 := fun g => by
    obtain ⟨a, c, h⟩ := hBV g.2
    exact ⟨(a, c), h⟩
  choose co hco using hcoord
  have hmem : ∀ g : B, co g ∈ S := fun g => by
    show θ (xP (co g).1 * wP (co g).2) = xP (co g).1 * wP (co g).2
    rw [← hco g]
    exact hfix g g.2
  have hinj : Function.Injective (fun g : B => (⟨co g, hmem g⟩ : S)) := by
    intro g g' h
    have h' : co g = co g' := congrArg Subtype.val h
    exact Subtype.ext (by rw [hco g, hco g', h'])
  refine (Nat.card_le_card_of_injective _ hinj).trans ?_
  refine burnsideF429_card_twisted_le_sq σ (mul_ne_zero x.ne_zero (y⁻¹).ne_zero)
    (mul_ne_zero x.ne_zero (z⁻¹).ne_zero) (fun a => (x : F) * ((y⁻¹ : Fˣ) : F) * σ a * b₀) S ?_
  intro p hp
  have hp' : θ (xP p.1 * wP p.2) = xP p.1 * wP p.2 := hp
  rw [hact] at hp'
  exact burnsideF429_L3_V1_inj hp'

theorem burnsideF429_L3_card_fix_V2 {u : projectiveSL 3 F} (hu : u ∈ projUnitriangular 3 F)
    (x y z : Fˣ) (σ : F ≃+* F) {B : Subgroup (projectiveSL 3 F)} (hBV : B ≤ V2)
    (hfix : ∀ g ∈ B,
      (MulAut.conj u * conjAut 3 F (burnsideF447_diagGL x y z) * fieldAut 3 F σ) g = g) :
    Nat.card B ≤ Nat.card {a : F // σ a = a} ^ 2 := by
  obtain ⟨a₀, ha₀⟩ := burnsideF429_L3_conjU_V2 hu
  set θ := MulAut.conj u * conjAut 3 F (burnsideF447_diagGL x y z) * fieldAut 3 F σ with hθ
  have hact : ∀ b c : F, θ (yP b * wP c) = yP ((y : F) * ((z⁻¹ : Fˣ) : F) * σ b) *
      wP ((x : F) * ((z⁻¹ : Fˣ) : F) * σ c + a₀ * ((y : F) * ((z⁻¹ : Fˣ) : F) * σ b)) := by
    intro b c
    rw [hθ, MulAut.mul_apply, MulAut.mul_apply, map_mul, fieldAut_yP, fieldAut_wP, map_mul,
      burnsideF447_conj_diag_yP, burnsideF447_conj_diag_wP, MulAut.conj_apply, ha₀]
  let S : Set (F × F) := {p | θ (yP p.1 * wP p.2) = yP p.1 * wP p.2}
  have hcoord : ∀ g : B, ∃ p : F × F, (g : projectiveSL 3 F) = yP p.1 * wP p.2 := fun g => by
    obtain ⟨b, c, h⟩ := hBV g.2
    exact ⟨(b, c), h⟩
  choose co hco using hcoord
  have hmem : ∀ g : B, co g ∈ S := fun g => by
    show θ (yP (co g).1 * wP (co g).2) = yP (co g).1 * wP (co g).2
    rw [← hco g]
    exact hfix g g.2
  have hinj : Function.Injective (fun g : B => (⟨co g, hmem g⟩ : S)) := by
    intro g g' h
    have h' : co g = co g' := congrArg Subtype.val h
    exact Subtype.ext (by rw [hco g, hco g', h'])
  refine (Nat.card_le_card_of_injective _ hinj).trans ?_
  refine burnsideF429_card_twisted_le_sq σ (mul_ne_zero y.ne_zero (z⁻¹).ne_zero)
    (mul_ne_zero x.ne_zero (z⁻¹).ne_zero) (fun b => a₀ * ((y : F) * ((z⁻¹ : Fˣ) : F) * σ b)) S ?_
  intro p hp
  have hp' : θ (yP p.1 * wP p.2) = yP p.1 * wP p.2 := hp
  rw [hact] at hp'
  exact burnsideF429_L3_V2_inj hp'

end P3

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] {f : ℕ}
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF429_L3_normalForm [Finite E] [Φ.range.Normal] (C : burnsideF447_Ctx f Φ ρ Gp)
    {t : E} (ht : t ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E)) :
    ∃ u ∈ projUnitriangular 3 F, ∃ (x y z : Fˣ) (σ : F ≃+* F),
      ρ t = MulAut.conj u * conjAut 3 F (burnsideF447_diagGL x y z) * fieldAut 3 F σ ∧
      burnsideF447_fpE C.hE t = σ := by
  obtain ⟨u, hu, b, hb, rfl⟩ := burnsideF447_frattini C.hq C.hΦ ht
  obtain ⟨δ, t₁, t₂, σ, hρb⟩ := burnsideF447_diag C.hq C.hΦ C.hΦρ C.hE hb.1 hb.2
  obtain ⟨u', hu', rfl⟩ := hu
  have hρ : ρ (Φ u' * b) = MulAut.conj u' *
      conjAut 3 F (burnsideF447_diagGL ((δ * 1) * t₁) (1 * t₂) (1 * (t₁ * t₂)⁻¹)) *
      fieldAut 3 F σ := by
    rw [map_mul, burnsideF447_rho_Phi C.hΦ C.hΦρ, hρb, burnsideF447_nuDiagGL_eq, ← conjAut_toGL,
      burnsideF447_toGL_dMat, ← map_mul, burnsideF447_diagGL_mul]
    exact (mul_assoc _ _ _).symm
  refine ⟨u', hu', _, _, _, σ, hρ, ?_⟩
  obtain ⟨g, rfl⟩ := proj_surjective 3 F u'
  refine burnsideF447_fpE_eq C.hE (A := Matrix.SpecialLinearGroup.toGL g *
    burnsideF447_diagGL ((δ * 1) * t₁) (1 * t₂) (1 * (t₁ * t₂)⁻¹)) ?_
  rw [hρ, map_mul, conjAut_toGL]

theorem burnsideF429_L3_mem_of_fp (C : burnsideF447_Ctx f Φ ρ Gp) {r : E} {k : ℕ}
    (hk : r ^ 2 ^ k = 1) (hfp : burnsideF447_fpE C.hE r = 1) : r ∈ Gp := by
  have hlin : ρ r ∈ linearAutGroup 3 F := (burnsideF447_fpE_one_iff C.hE r).mp hfp
  have hinn : ρ r ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
    refine CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two le_rfl (fun h => ?_) _
      hlin k ?_
    · have := h.trans (Nat.gcd_dvd_left 3 _)
      omega
    · rw [← map_pow, hk, map_one]
      exact Subgroup.one_mem _
  obtain ⟨g, hg⟩ := hinn
  have hrg : r = Φ g := C.hρ (by rw [burnsideF447_rho_Phi C.hΦ C.hΦρ, hg])
  rw [hrg, ← C.hrange]
  exact ⟨g, rfl⟩

theorem burnsideF429_L3_fp_inv (C : burnsideF447_Ctx f Φ ρ Gp) {t : E} (htt : t * t = 1)
    (htG : t ∉ Gp) : Even f ∧ ∀ x, burnsideF447_fpE C.hE t x = x ^ 2 ^ (f / 2) := by
  have hσ1 : burnsideF447_fpE C.hE t ≠ 1 := fun h =>
    htG (burnsideF429_L3_mem_of_fp C (k := 1) (by rw [pow_one, pow_two, htt]) h)
  have hσσ : burnsideF447_fpE C.hE t * burnsideF447_fpE C.hE t = 1 := by
    rw [← map_mul, htt, map_one]
  have hf1 : 1 ≤ f := le_trans (by norm_num) C.hf
  exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution hf1 C.hF
    hσ1 hσσ

end Model

section Clause6

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}


theorem burnsideF429_c6_L3 {f : ℕ} (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C6 .L3 f Gp M₁ M₂ T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hρ, hΦρ, hE, hD, hO,
    h₁, h₂, -⟩ := burnsideF447_setup hf hyp.toHypF_4_4g
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hNp := burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 F).map Φ := by
    have hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := burnsideF4d_Y2_pCore_le hf hyp.toHypF_4_4g
    rw [burnsideF4d_pCoreOf_inf_eq (M₁ ⊓ M₂) hle]
    exact hNp.2
  have C : burnsideF447_Ctx f Φ ρ Gp := ⟨hf, hFcard, hΦ, hρ, hrange, hΦρ, hE⟩
  have hTG := burnsideF429_T_inf_Gp hyp hT
  have hST := burnsideF429_sbar_le (Gp := Gp) hT
  have hTN : ∀ t ∈ T,
      t ∈ Subgroup.normalizer (((projUnitriangular 3 F).map Φ : Subgroup E) : Set E) := by
    intro t ht
    rw [← hNp.1]
    exact hT.1 ht
  have hcardR : Nat.card ((V1 : Subgroup (projectiveSL 3 F)).map Φ) = 2 ^ f * 2 ^ f := by
    rw [Subgroup.card_map_of_injective hΦ, burnsideF429_L3_card_V1, hFcard, sq]
  refine burnsideF429_c6_of (R := (V1 : Subgroup (projectiveSL 3 F)).map Φ)
    (W := (Wg : Subgroup (projectiveSL 3 F)).map Φ) hST ?_ ?_ (Subgroup.map_mono Wg_le_V1) ?_ ?_ ?_
  ·
    refine ⟨?_, isElemAbelian_V1.map Φ, fun B hB hBe => ?_⟩
    · rw [hS]
      exact Subgroup.map_mono V1_le_U
    · have hBr : B ≤ Φ.range := (hB.trans hS.le).trans (Subgroup.map_le_range Φ _)
      have hBB : (B.comap Φ).map Φ = B := Subgroup.map_comap_eq_self hBr
      have hB'U : B.comap Φ ≤ projUnitriangular 3 F := fun g hg =>
        (Subgroup.mem_map_iff_mem hΦ).mp (by rw [← hS]; exact hB hg)
      have hB'e : IsElemAbelian 2 (B.comap Φ) := burnsideF429_isElemAbelian_comap hΦ hBe
      rw [← hBB, Subgroup.card_map_of_injective hΦ, Subgroup.card_map_of_injective hΦ,
        burnsideF429_L3_card_V1]
      rcases burnsideF429_L3_elemAb_le hB'U hB'e with h | h
      · exact (Subgroup.card_le_of_le h).trans burnsideF429_L3_card_V1.le
      · exact (Subgroup.card_le_of_le h).trans burnsideF429_L3_card_V2.le
  ·
    intro A hAT hAe hAS
    obtain ⟨t, htA, htS⟩ := SetLike.not_le_iff_exists.mp hAS
    have htT := hAT htA
    have htt : t * t = 1 := by rw [← pow_two]; exact hAe.2 t htA
    have htG : t ∉ Gp := fun h => htS (by rw [← hTG]; exact ⟨htT, h⟩)
    obtain ⟨hfe, hσt⟩ := burnsideF429_L3_fp_inv C htt htG
    have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := isMulCommutative_iff_of_setLike.mp hAe.1
    have hsplit : ∀ a ∈ A, a ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
        t * a ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
      intro a haA haS
      have haa : a * a = 1 := by rw [← pow_two]; exact hAe.2 a haA
      have haG : a ∉ Gp := fun h => haS (by rw [← hTG]; exact ⟨hAT haA, h⟩)
      obtain ⟨-, hσa⟩ := burnsideF429_L3_fp_inv C haa haG
      have hfp : burnsideF447_fpE C.hE (t * a) = 1 := by
        have e : burnsideF447_fpE C.hE a = burnsideF447_fpE C.hE t :=
          RingEquiv.ext fun x => by rw [hσa, hσt]
        rw [map_mul, e, ← map_mul, htt, map_one]
      have hta : (t * a) ^ 2 ^ 1 = 1 := by
        rw [pow_one, pow_two]
        calc t * a * (t * a) = t * (a * t) * a := by group
          _ = t * (t * a) * a := by rw [hAcomm a haA t htA]
          _ = (t * t) * (a * a) := by group
          _ = 1 := by rw [htt, haa, one_mul]
      rw [← hTG]
      exact ⟨T.mul_mem htT (hAT haA), burnsideF429_L3_mem_of_fp C hta hfp⟩
    set X : Subgroup E := A ⊓ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hXdef
    have hcardA : Nat.card A ≤ 2 * Nat.card X := by
      classical
      have hmemX : ∀ a : A, (a : E) ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * (a : E) ∈ X :=
        fun a ha => ⟨A.mul_mem htA a.2, hsplit a a.2 ha⟩
      let φ : A → Bool × X := fun a =>
        if h : (a : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) then (false, ⟨a, a.2, h⟩)
        else (true, ⟨t * a, hmemX a h⟩)
      have hleft : ∀ a : A,
          (fun p : Bool × X => if p.1 then t * (p.2 : E) else (p.2 : E)) (φ a) = a := by
        intro a
        by_cases ha : (a : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))
        · have e : φ a = (false, ⟨a, a.2, ha⟩) := dif_pos ha
          rw [e]
          rfl
        · have e : φ a = (true, ⟨t * a, hmemX a ha⟩) := dif_neg ha
          rw [e]
          show t * (t * (a : E)) = a
          rw [← mul_assoc, htt, one_mul]
      have hφ : Function.Injective φ := fun a b hab =>
        Subtype.ext (by rw [← hleft a, ← hleft b, hab])
      calc Nat.card A ≤ Nat.card (Bool × X) := Nat.card_le_card_of_injective φ hφ
        _ = 2 * Nat.card X := by rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
            Fintype.card_bool]
    have hX : Nat.card X ≤ 2 ^ f := by
      have hXr : X ≤ Φ.range := (inf_le_right.trans hS.le).trans (Subgroup.map_le_range Φ _)
      have hXX : (X.comap Φ).map Φ = X := Subgroup.map_comap_eq_self hXr
      have hX'U : X.comap Φ ≤ projUnitriangular 3 F := fun g hg =>
        (Subgroup.mem_map_iff_mem hΦ).mp (by rw [← hS]; exact hg.2)
      have hX'e : IsElemAbelian 2 (X.comap Φ) :=
        burnsideF429_isElemAbelian_comap hΦ (hAe.mono inf_le_left)
      obtain ⟨u, hu, x, y, z, σ, hρt, hfpt⟩ := burnsideF429_L3_normalForm C (hTN t htT)
      have hfix : ∀ g ∈ X.comap Φ,
          (MulAut.conj u * conjAut 3 F (burnsideF447_diagGL x y z) * fieldAut 3 F σ) g = g := by
        intro g hg
        rw [← hρt]
        exact (burnsideF447_comm_iff hΦ hΦρ t g).mpr (hAcomm t htA _ hg.1)
      have hσ : ∀ a, σ a = a ^ 2 ^ (f / 2) := fun a => by rw [← hfpt]; exact hσt a
      have h1q : 1 < 2 ^ (f / 2) := Nat.one_lt_two_pow (by omega)
      have hfixF : Nat.card {a : F // σ a = a} ≤ 2 ^ (f / 2) :=
        CFSG.SeitzReduction.natCard_le_of_forall_pow_eq_self h1q {a : F | σ a = a}
          fun a ha => by rw [← hσ a]; exact ha
      have hsq : (2 ^ (f / 2)) ^ 2 = 2 ^ f := by
        rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp hfe)]
      have hbound : Nat.card {a : F // σ a = a} ^ 2 ≤ 2 ^ f :=
        (Nat.pow_le_pow_left hfixF 2).trans hsq.le
      rw [← hXX, Subgroup.card_map_of_injective hΦ]
      rcases burnsideF429_L3_elemAb_le hX'U hX'e with h | h
      · exact (burnsideF429_L3_card_fix_V1 hu x y z σ h hfix).trans hbound
      · exact (burnsideF429_L3_card_fix_V2 hu x y z σ h hfix).trans hbound
    rw [hcardR]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    calc Nat.card A ≤ 2 * Nat.card X := hcardA
      _ ≤ 2 * 2 ^ f := Nat.mul_le_mul_left 2 hX
      _ < 2 ^ f * 2 ^ f := by nlinarith
  ·
    rintro _ ⟨w, ⟨c, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [hS] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    rw [← map_mul, ← map_mul, burnsideF429_L3_wP_comm c hp]
  ·
    rintro _ ⟨w, ⟨c, rfl⟩, rfl⟩
    rw [← map_pow, pow_two, wP_mul_self, map_one]
  ·
    rintro r ⟨hrT, hrc⟩
    obtain ⟨u, hu, x, y, z, σ, hρr, hfpr⟩ := burnsideF429_L3_normalForm C (hTN r hrT)
    have hfixW : ∀ c : F, ρ r (wP c) = wP c := fun c =>
      (burnsideF447_comm_iff hΦ hΦρ r _).mpr
        ((Subgroup.mem_centralizer_iff.mp hrc _ ⟨wP c, ⟨c, rfl⟩, rfl⟩).symm)
    have hact : ∀ c : F, ρ r (wP c) = wP ((x : F) * ((z⁻¹ : Fˣ) : F) * σ c) := fun c => by
      rw [hρr, MulAut.mul_apply, MulAut.mul_apply, fieldAut_wP, burnsideF447_conj_diag_wP,
        MulAut.conj_apply, ← burnsideF429_L3_wP_comm _ hu, mul_inv_cancel_right]
    have hl : ∀ c : F, (x : F) * ((z⁻¹ : Fˣ) : F) * σ c = c := fun c =>
      burnsideF429_L3_wP_inj ((hact c).symm.trans (hfixW c))
    have hl1 : (x : F) * ((z⁻¹ : Fˣ) : F) = 1 := by
      have := hl 1
      rwa [map_one, mul_one] at this
    have hσ1 : σ = 1 := by
      refine RingEquiv.ext fun c => ?_
      show σ c = c
      have := hl c
      rwa [hl1, one_mul] at this
    obtain ⟨k, hk⟩ := hT.2.1 ⟨r, hrT⟩
    have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [← hTG]
    exact ⟨hrT, burnsideF429_L3_mem_of_fp C hrk (hfpr.trans hσ1)⟩

end Clause6

end CFSG.ASVolI
