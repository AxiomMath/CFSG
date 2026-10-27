module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2GrpFus

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat uElt uElt_mul minorAut)
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj)

variable {k : Type} [Field k]

theorem sp4c2_isUpper_one : IsUpper (1 : antiSp k) := fun i j hij => by
  change (1 : Matrix (Fin 4) (Fin 4) k) i j = 0
  exact Matrix.one_apply_ne (ne_of_gt hij)

theorem glMat_diag_mul_of_upper {x y : antiSp k} (hx : IsUpper x) (hy : IsUpper y) (i : Fin 4) :
    glMat ((x * y : antiSp k) : GL (Fin 4) k) i i =
      glMat (x : GL (Fin 4) k) i i * glMat (y : GL (Fin 4) k) i i :=
  upper_mul_apply_self hx hy i

def diagPairs (I : Subgroup (antiSp k)) : Subgroup (kˣ × kˣ) where
  carrier := {p | ∃ x ∈ I, IsUpper x ∧ (p.1 : k) = glMat (x : GL (Fin 4) k) 0 0 ^ 2 ∧
    (p.2 : k) = glMat (x : GL (Fin 4) k) 0 0 * glMat (x : GL (Fin 4) k) 1 1}
  mul_mem' := by
    rintro p q ⟨x, hx, hxu, hp1, hp2⟩ ⟨y, hy, hyu, hq1, hq2⟩
    refine ⟨x * y, I.mul_mem hx hy, isUpper_mul hxu hyu, ?_, ?_⟩
    · rw [Prod.fst_mul, Units.val_mul, hp1, hq1, glMat_diag_mul_of_upper hxu hyu 0]
      ring
    · rw [Prod.snd_mul, Units.val_mul, hp2, hq2, glMat_diag_mul_of_upper hxu hyu 0,
        glMat_diag_mul_of_upper hxu hyu 1]
      ring
  one_mem' := ⟨1, I.one_mem, sp4c2_isUpper_one, by simp [glMat], by simp [glMat]⟩
  inv_mem' := by
    rintro p ⟨x, hx, hxu, hp1, hp2⟩
    have h0 : glMat ((x⁻¹ : antiSp k) : GL (Fin 4) k) 0 0 = (glMat (x : GL (Fin 4) k) 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_right (isUpper_diag_mul_inv hxu 0)
    have h1 : glMat ((x⁻¹ : antiSp k) : GL (Fin 4) k) 1 1 = (glMat (x : GL (Fin 4) k) 1 1)⁻¹ :=
      eq_inv_of_mul_eq_one_right (isUpper_diag_mul_inv hxu 1)
    refine ⟨x⁻¹, I.inv_mem hx, isUpper_inv hxu, ?_, ?_⟩
    · rw [Prod.fst_inv, Units.val_inv_eq_inv_val, hp1, h0, inv_pow]
    · rw [Prod.snd_inv, Units.val_inv_eq_inv_val, hp2, h0, h1, mul_inv]

section CharTwo

variable [CharP k 2] [Finite k]

omit [Finite k] in
theorem uElt_mem_of_mem_diagPairs {I : Subgroup (antiSp k)} {b₀ c₀ : k}
    (hz₀ : uElt 0 b₀ c₀ 0 ∈ I) {p : kˣ × kˣ} (hp : p ∈ diagPairs I) :
    uElt 0 (b₀ * (p.2 : k)) (c₀ * (p.1 : k)) 0 ∈ I := by
  obtain ⟨x, hx, hxu, hp1, hp2⟩ := hp
  have hmem : x * uElt 0 b₀ c₀ 0 * x⁻¹ ∈ I := I.mul_mem (I.mul_mem hx hz₀) (I.inv_mem hx)
  rw [P6B.conj_uElt_center hxu b₀ c₀] at hmem
  rw [hp1, hp2, mul_comm b₀, mul_comm c₀]
  exact hmem

variable {I : Subgroup (antiSp k)} (htr : ∀ x ∈ I, ¬ IsTransvection x)
  (htr' : ∀ x ∈ I, ¬ IsTransvection (minorAut k x)) {g : antiSp k} (hg : IsOppStd g)
  {b₀ c₀ : k} (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hz₀ : uElt 0 b₀ c₀ 0 ∈ I)
  (hz₀g : g * uElt 0 b₀ c₀ 0 * g⁻¹ ∈ I)

include htr htr' hg hb₀ hc₀ hz₀ hz₀g in
theorem exists_mem_diagPairs {b c : k} (h : uElt 0 b c 0 ∈ I) (hne : ¬ (b = 0 ∧ c = 0)) :
    ∃ p ∈ diagPairs I, c = c₀ * (p.1 : k) ∧ b = b₀ * (p.2 : k) := by
  obtain ⟨y, hy, hyu, e⟩ := exists_upper_conj htr htr' hg hb₀ hc₀ hz₀g hz₀ h
    (fun h0 => hb₀ h0.1 |>.elim) hne
  have hcj := P6B.conj_uElt_center hyu b₀ c₀
  rw [e] at hcj
  obtain ⟨-, e1, e2, -⟩ := uElt_inj hcj
  have d0 := isUpper_diag_ne_zero hyu 0
  have d1 := isUpper_diag_ne_zero hyu 1
  refine ⟨(Units.mk0 _ (pow_ne_zero 2 d0), Units.mk0 _ (mul_ne_zero d0 d1)),
    ⟨y, hy, hyu, rfl, rfl⟩, ?_, ?_⟩
  · simp only [Units.val_mk0]
    rw [e2]
    ring
  · simp only [Units.val_mk0]
    rw [e1]
    ring

include htr htr' hb₀ hz₀ in
theorem diagPairs_graph {p q : kˣ × kˣ} (hp : p ∈ diagPairs I) (hq : q ∈ diagPairs I)
    (h : p.1 = q.1) : p.2 = q.2 := by
  have h1 := uElt_mem_of_mem_diagPairs hz₀ hp
  have h2 := uElt_mem_of_mem_diagPairs hz₀ hq
  rw [h] at h1
  exact Units.ext (mul_left_cancel₀ hb₀ (c2_coord_inj_c htr htr' h1 h2))

include htr htr' hg hb₀ hc₀ hz₀ hz₀g in
theorem exists_twisted_line :
    ∃ (Γ : Subgroup kˣ) (φ : Γ →* kˣ),
      (∀ γ : Γ, uElt 0 (b₀ * ((φ γ : kˣ) : k)) (c₀ * ((γ : kˣ) : k)) 0 ∈ I) ∧
      (∀ b c : k, uElt 0 b c 0 ∈ I →
        (b = 0 ∧ c = 0) ∨ ∃ γ : Γ, c = c₀ * ((γ : kˣ) : k) ∧ b = b₀ * ((φ γ : kˣ) : k)) ∧
      (∀ γ γ' : Γ,
        (∃ δ : Γ, c₀ * (γ : kˣ) + c₀ * (γ' : kˣ) = c₀ * (δ : kˣ) ∧
          b₀ * (φ γ : kˣ) + b₀ * (φ γ' : kˣ) = b₀ * (φ δ : kˣ)) ∨
        (c₀ * (γ : kˣ) + c₀ * (γ' : kˣ) = 0 ∧ b₀ * (φ γ : kˣ) + b₀ * (φ γ' : kˣ) = 0)) := by
  let D := diagPairs I
  let pr : D →* kˣ := (MonoidHom.fst kˣ kˣ).comp D.subtype
  have hpr : Function.Injective pr := fun p q h =>
    Subtype.ext (Prod.ext h (diagPairs_graph htr htr' hb₀ hz₀ p.2 q.2 h))
  let e : D ≃* pr.range := MonoidHom.ofInjective hpr
  let φ : pr.range →* kˣ := ((MonoidHom.snd kˣ kˣ).comp D.subtype).comp e.symm.toMonoidHom
  have hφ : ∀ γ : pr.range, ((e.symm γ : D) : kˣ × kˣ) = ((γ : kˣ), φ γ) := fun γ =>
    Prod.ext (congrArg Subtype.val (e.apply_symm_apply γ)) rfl
  have hmem : ∀ γ : pr.range,
      uElt 0 (b₀ * ((φ γ : kˣ) : k)) (c₀ * ((γ : kˣ) : k)) 0 ∈ I := fun γ => by
    have := uElt_mem_of_mem_diagPairs hz₀ (e.symm γ).2
    rw [hφ γ] at this
    exact this
  have hii : ∀ b c : k, uElt 0 b c 0 ∈ I →
      (b = 0 ∧ c = 0) ∨ ∃ γ : pr.range, c = c₀ * ((γ : kˣ) : k) ∧ b = b₀ * ((φ γ : kˣ) : k) := by
    intro b c h
    by_cases hne : b = 0 ∧ c = 0
    · exact Or.inl hne
    · obtain ⟨p, hp, hc, hb⟩ := exists_mem_diagPairs htr htr' hg hb₀ hc₀ hz₀ hz₀g h hne
      refine Or.inr ⟨⟨p.1, ⟨⟨p, hp⟩, rfl⟩⟩, hc, ?_⟩
      have h1 := hφ ⟨p.1, ⟨⟨p, hp⟩, rfl⟩⟩
      have h2 : e.symm ⟨p.1, ⟨⟨p, hp⟩, rfl⟩⟩ = ⟨p, hp⟩ :=
        e.symm_apply_eq.mpr (Subtype.ext rfl)
      rw [h2] at h1
      rw [hb]
      exact congrArg (fun x => b₀ * ((x.2 : kˣ) : k)) h1
  refine ⟨pr.range, φ, hmem, hii, fun γ γ' => ?_⟩
  have hm := I.mul_mem (hmem γ) (hmem γ')
  have hprod : uElt 0 (b₀ * ((φ γ : kˣ) : k)) (c₀ * ((γ : kˣ) : k)) 0 *
      uElt 0 (b₀ * ((φ γ' : kˣ) : k)) (c₀ * ((γ' : kˣ) : k)) 0 =
      uElt 0 (b₀ * (φ γ : kˣ) + b₀ * (φ γ' : kˣ)) (c₀ * (γ : kˣ) + c₀ * (γ' : kˣ)) 0 := by
    rw [uElt_mul]
    congr 1 <;> ring
  rw [hprod] at hm
  rcases hii _ _ hm with ⟨hb, hc⟩ | ⟨δ, hc, hb⟩
  · exact Or.inr ⟨hc, hb⟩
  · exact Or.inl ⟨δ, hc, hb⟩

end CharTwo

end CFSG.Quasithin.Ch3E213M.Sp4C2
