module

public import CFSG.Quasithin.EmptyFaithful.SzN31FactRB

public section

namespace CFSG.Quasithin.SzN31

section FactRD

variable {p : ℕ} {Q : Type*} [Group Q] [Finite Q] {Bh : Type*} [Group Bh]

omit [Finite Q] in
theorem agree_of_scalar {L : Subgroup Q} (act : Bh →* MulAut Q) {b c : Bh}
    (hb : (∀ x ∈ L, act b x = x) ∨ (∀ x ∈ L, act b x = x⁻¹))
    (hc : (∀ x ∈ L, act c x = x) ∨ (∀ x ∈ L, act c x = x⁻¹))
    (h : (∀ x ∈ L, act b x = x) ↔ (∀ x ∈ L, act c x = x)) : ∀ x ∈ L, act b x = act c x := by
  intro x hx
  by_cases h1 : ∀ x ∈ L, act b x = x
  · rw [h1 x hx, h.1 h1 x hx]
  · have h2 : ¬ ∀ x ∈ L, act c x = x := fun h2 => h1 (h.2 h2)
    rcases hb with hb | hb
    · exact absurd hb h1
    rcases hc with hc | hc
    · exact absurd hc h2
    rw [hb x hx, hc x hx]

theorem sign_bound (hp : p.Prime) (hp2 : p ≠ 2) (act : Bh →* MulAut Q) (hB : ∀ b : Bh, b * b = 1)
    {E : Subgroup Q} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E ≤ p ^ 2) (hinv : ∀ b : Bh, ∀ x ∈ E, act b x ∈ E) :
    ∃ g : MulAut Q → Bool × Bool,
      ∀ b c : Bh, g (act b) = g (act c) → ∀ x ∈ E, act b x = act c x := by
  classical
  by_cases hall : ∀ b : Bh, (∀ x ∈ E, act b x = x) ∨ (∀ x ∈ E, act b x = x⁻¹)
  · refine ⟨fun σ => (decide (∀ x ∈ E, σ x = x), true), ?_⟩
    intro b c hbc
    exact agree_of_scalar act (hall b) (hall c) (decide_eq_decide.1 (congrArg Prod.fst hbc))
  · push Not at hall
    obtain ⟨b₀, ⟨x₁, hx₁E, hx₁⟩, ⟨x₂, hx₂E, hx₂⟩⟩ := hall
    have hσ := act_invol act hB b₀
    have hWMne : invSub (act b₀) E hcomm ≠ ⊥ := by
      intro h
      obtain ⟨u, hu, v, hv, hx⟩ := exists_fix_inv_decomp hp hp2 hσ hcomm hexp (hinv b₀) hx₁E
      rw [h, Subgroup.mem_bot] at hv
      subst hv
      apply hx₁
      rw [hx, mul_one]
      exact hu.2
    have hWPne : fixSub (act b₀) E ≠ ⊥ := by
      intro h
      obtain ⟨u, hu, v, hv, hx⟩ := exists_fix_inv_decomp hp hp2 hσ hcomm hexp (hinv b₀) hx₂E
      rw [h, Subgroup.mem_bot] at hu
      subst hu
      apply hx₂
      rw [hx, one_mul]
      exact hv.2
    have hWPinv : ∀ c : Bh, ∀ x ∈ fixSub (act b₀) E, act c x ∈ fixSub (act b₀) E := by
      intro c x hx
      exact ⟨hinv c x hx.1, by rw [act_comm act hB b₀ c x, hx.2]⟩
    have hWMinv : ∀ c : Bh, ∀ x ∈ invSub (act b₀) E hcomm, act c x ∈ invSub (act b₀) E hcomm := by
      intro c x hx
      exact ⟨hinv c x hx.1, by rw [act_comm act hB b₀ c x, hx.2, map_inv]⟩
    obtain ⟨LP, hLPle, hLPcard, hLPinv⟩ := exists_invariant_line_ambient hp hp2 act hB hWPne
      (fun x hx y hy => hcomm x hx.1 y hy.1) (fun x hx => hexp x hx.1) hWPinv
    obtain ⟨LM, hLMle, hLMcard, hLMinv⟩ := exists_invariant_line_ambient hp hp2 act hB hWMne
      (fun x hx y hy => hcomm x hx.1 y hy.1) (fun x hx => hexp x hx.1) hWMinv
    have hLPE : LP ≤ E := hLPle.trans (fixSub_le _ _)
    have hLME : LM ≤ E := hLMle.trans (invSub_le _ _ _)
    have hφinj : Function.Injective (fun ab : LP × LM =>
        (⟨(ab.1 : Q) * ab.2, E.mul_mem (hLPE ab.1.2) (hLME ab.2.2)⟩ : E)) := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      have h' : a * b = a' * b' := congrArg Subtype.val h
      have ht : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
          _ = b' * b⁻¹ := by group
      have h₁ : a'⁻¹ * a ∈ fixSub (act b₀) E :=
        mul_mem (inv_mem (hLPle ha')) (hLPle ha)
      have h₂ : b' * b⁻¹ ∈ invSub (act b₀) E hcomm := mul_mem (hLMle hb') (inv_mem (hLMle hb))
      rw [ht] at h₁
      have h3 : (b' * b⁻¹)⁻¹ = b' * b⁻¹ := h₂.2.symm.trans h₁.2
      have h4 : (b' * b⁻¹) * (b' * b⁻¹) = 1 := by
        calc (b' * b⁻¹) * (b' * b⁻¹) = (b' * b⁻¹)⁻¹ * (b' * b⁻¹) := by rw [h3]
          _ = 1 := inv_mul_cancel _
      have h5 : b' * b⁻¹ = 1 := eq_one_of_sq_eq_one_of_pow_eq_one hp hp2 h4 (hexp _ h₂.1)
      have hbb : b' = b := mul_inv_eq_one.1 h5
      have h6 : a'⁻¹ * a = 1 := by rw [ht, h5]
      have haa : a' = a := inv_mul_eq_one.1 h6
      subst hbb haa
      rfl
    have hcard' : Nat.card E ≤ Nat.card (LP × LM) := by
      rw [Nat.card_prod, hLPcard, hLMcard]
      simpa [sq] using hcard
    have hφsurj := (hφinj.bijective_of_nat_card_le hcard').2
    refine ⟨fun σ => (decide (∀ x ∈ LP, σ x = x), decide (∀ x ∈ LM, σ x = x)), ?_⟩
    intro b c hbc x hx
    have h1 : (∀ x ∈ LP, act b x = x) ↔ (∀ x ∈ LP, act c x = x) :=
      decide_eq_decide.1 (congrArg Prod.fst hbc)
    have h2 : (∀ x ∈ LM, act b x = x) ↔ (∀ x ∈ LM, act c x = x) :=
      decide_eq_decide.1 (congrArg Prod.snd hbc)
    have sP : ∀ d : Bh, (∀ x ∈ LP, act d x = x) ∨ (∀ x ∈ LP, act d x = x⁻¹) := fun d =>
      scalar_of_card_prime hp hp2 (act_invol act hB d)
        (fun x hx y hy => hcomm x (hLPE hx) y (hLPE hy)) (fun x hx => hexp x (hLPE hx))
        (hLPinv d) hLPcard
    have sM : ∀ d : Bh, (∀ x ∈ LM, act d x = x) ∨ (∀ x ∈ LM, act d x = x⁻¹) := fun d =>
      scalar_of_card_prime hp hp2 (act_invol act hB d)
        (fun x hx y hy => hcomm x (hLME hx) y (hLME hy)) (fun x hx => hexp x (hLME hx))
        (hLMinv d) hLMcard
    obtain ⟨⟨a, b'⟩, hab⟩ := hφsurj ⟨x, hx⟩
    have hx' : (a : Q) * b' = x := congrArg Subtype.val hab
    rw [← hx', map_mul, map_mul, agree_of_scalar act (sP b) (sP c) h1 a a.2,
      agree_of_scalar act (sM b) (sM c) h2 b' b'.2]

end FactRD

end CFSG.Quasithin.SzN31
