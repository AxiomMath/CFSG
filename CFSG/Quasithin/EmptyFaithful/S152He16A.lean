module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.He16

open Matrix

abbrev SL25 := SpecialLinearGroup (Fin 2) (ZMod 5)

set_option maxRecDepth 1000000 in
theorem sl2_five_card : Nat.card SL25 = 120 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sl2_five_sq : ∀ A : SL25, A ^ 2 = 1 → A = 1 ∨ A = -1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sl2_five_pow : ∀ A : SL25, A ^ 8 = 1 → A ^ 4 = 1 := by
  decide +kernel

theorem false_of_comm_card_eight {Q : Type*} [CommGroup Q] [Finite Q]
    (hQ8 : Nat.card Q = 8) (φ : Q →* SL25) (hφ : Function.Injective φ) : False := by
  have h8 : ∀ q : Q, q ^ 8 = 1 := fun q => by
    rw [← hQ8]; exact pow_card_eq_one'
  have h4 : ∀ q : Q, q ^ 4 = 1 := fun q => by
    apply hφ
    rw [map_pow, map_one]
    exact sl2_five_pow _ (by rw [← map_pow, h8, map_one])
  have hΩ : ∀ a b : Q, a ^ 2 = 1 → b ^ 2 = 1 → a = b ∨ a = 1 ∨ b = 1 := by
    intro a b ha hb
    have ha' := sl2_five_sq (φ a) (by rw [← map_pow, ha, map_one])
    have hb' := sl2_five_sq (φ b) (by rw [← map_pow, hb, map_one])
    rcases ha' with ha' | ha'
    · exact Or.inr (Or.inl (hφ (by rw [ha', map_one])))
    · rcases hb' with hb' | hb'
      · exact Or.inr (Or.inr (hφ (by rw [hb', map_one])))
      · exact Or.inl (hφ (by rw [ha', hb']))
  let sq : Q →* Q := powMonoidHom 2
  have hmemker : ∀ q : Q, q ∈ sq.ker ↔ q ^ 2 = 1 := fun q => by
    rw [MonoidHom.mem_ker]; rfl
  have hker : Nat.card sq.ker ≤ 2 := by
    by_contra h
    push Not at h
    have : Fintype ↥sq.ker := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h
    have hab' : a ≠ b := fun h => hab (Subtype.ext h)
    have hac' : a ≠ c := fun h => hac (Subtype.ext h)
    have hbc' : b ≠ c := fun h => hbc (Subtype.ext h)
    rw [hmemker] at ha hb hc
    rcases hΩ a b ha hb with h | h | h
    · exact hab' h
    · rcases hΩ b c hb hc with h' | h' | h'
      · exact hbc' h'
      · exact hab' (h.trans h'.symm)
      · exact hac' (h.trans h'.symm)
    · rcases hΩ a c ha hc with h' | h' | h'
      · exact hac' h'
      · exact hab' (h'.trans h.symm)
      · exact hbc' (h.trans h'.symm)
  have hrange : Nat.card sq.range ≤ 2 := by
    refine le_trans (Subgroup.card_le_of_le (K := sq.ker) ?_) hker
    rintro _ ⟨q, rfl⟩
    rw [hmemker]
    change (q ^ 2) ^ 2 = 1
    rw [← pow_mul]
    exact h4 q
  have := Subgroup.card_ker_mul_card_range sq
  rw [hQ8] at this
  nlinarith

theorem basis_aux (v₀ : Fin 2 → ZMod 5) (hv₀ : v₀ ≠ 0) : ∃ v₁ : Fin 2 → ZMod 5,
    (∀ w : Fin 2 → ZMod 5, ∃ c₁ c₂ : ZMod 5, w = c₁ • v₀ + c₂ • v₁) ∧
    ∀ c₁ c₂ d₁ d₂ : ZMod 5, c₁ • v₀ + c₂ • v₁ = d₁ • v₀ + d₂ • v₁ → c₁ = d₁ ∧ c₂ = d₂ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have key : ∀ v₁ : Fin 2 → ZMod 5, (∀ c₁ c₂ d₁ d₂ : ZMod 5,
      c₁ • v₀ + c₂ • v₁ = d₁ • v₀ + d₂ • v₁ → c₁ = d₁ ∧ c₂ = d₂) →
      (∀ w : Fin 2 → ZMod 5, ∃ c₁ c₂ : ZMod 5, w = c₁ • v₀ + c₂ • v₁) ∧
      ∀ c₁ c₂ d₁ d₂ : ZMod 5, c₁ • v₀ + c₂ • v₁ = d₁ • v₀ + d₂ • v₁ → c₁ = d₁ ∧ c₂ = d₂ := by
    intro v₁ hv
    refine ⟨fun w => ?_, hv⟩
    let f : ZMod 5 × ZMod 5 → (Fin 2 → ZMod 5) := fun p => p.1 • v₀ + p.2 • v₁
    have hf : Function.Injective f := fun p q h => by
      have := hv p.1 p.2 q.1 q.2 h
      exact Prod.ext this.1 this.2
    have hb := Function.Injective.bijective_of_nat_card_le hf (by
      simp [Nat.card_eq_fintype_card])
    obtain ⟨p, hp⟩ := hb.2 w
    exact ⟨p.1, p.2, hp.symm⟩
  by_cases h1 : v₀ 1 = 0
  · have h0 : v₀ 0 ≠ 0 := fun h0 => hv₀ (by ext i; fin_cases i <;> simp [h0, h1])
    refine ⟨![0, 1], key _ fun c₁ c₂ d₁ d₂ h => ?_⟩
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp [h1] at e0 e1
    exact ⟨e0.resolve_right h0, e1⟩
  · refine ⟨![1, 0], key _ fun c₁ c₂ d₁ d₂ h => ?_⟩
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp at e0 e1
    have hc : c₁ = d₁ := e1.resolve_right h1
    subst hc
    exact ⟨rfl, add_left_cancel e0⟩

theorem eight_smul_eq_zero : ∀ t : ZMod 5, 8 • t = 0 → t = 0 := by decide

variable {X : Type*} [Group X]

set_option maxRecDepth 100000 in
theorem no_invariant_line [Finite X] {P Q Y : Subgroup X}
    (e : ↥P ≃* Multiplicative (Fin 2 → ZMod 5))
    (hQP : ∀ q ∈ Q, ∀ d ∈ P, q * d * q⁻¹ ∈ P)
    (hker : ∀ q ∈ Q, (∀ d ∈ P, q * d * q⁻¹ = d) → q = 1)
    (hY5 : Nat.card Y = 5) (hYP : Y ≤ P) (hQY : ∀ q ∈ Q, ∀ y ∈ Y, q * y * q⁻¹ ∈ Y)
    (hQ8 : Nat.card Q = 8) (φ : ↥Q →* SL25) (hφ : Function.Injective φ) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hYne : Y ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hY5; omega
  obtain ⟨⟨a, haY⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hord : orderOf a = 5 := by
    have hd : orderOf a ∣ Nat.card Y := by
      have := orderOf_dvd_natCard (⟨a, haY⟩ : ↥Y)
      rwa [← Subgroup.orderOf_coe] at this
    rw [hY5] at hd
    rcases (Nat.dvd_prime Nat.prime_five).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1'
    · exact h
  have hYz : Y = Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haY)
      (by rw [Nat.card_zpowers, hord, hY5])).symm
  have haP : a ∈ P := hYP haY
  let conjP : ↥Q → ↥P → ↥P := fun q d => ⟨q * d * q⁻¹, hQP q q.2 d d.2⟩
  have conjP_mul : ∀ q d₁ d₂, conjP q (d₁ * d₂) = conjP q d₁ * conjP q d₂ := by
    intro q d₁ d₂; apply Subtype.ext; simp [conjP, mul_assoc]
  have conjP_comp : ∀ q q' d, conjP (q * q') d = conjP q (conjP q' d) := by
    intro q q' d; apply Subtype.ext; simp [conjP, mul_assoc]
  have conjP_one : ∀ d, conjP 1 d = d := by
    intro d; apply Subtype.ext; simp [conjP]
  let act : ↥Q → (Fin 2 → ZMod 5) → (Fin 2 → ZMod 5) := fun q v =>
    Multiplicative.toAdd (e (conjP q (e.symm (Multiplicative.ofAdd v))))
  have act_add : ∀ q v w, act q (v + w) = act q v + act q w := by
    intro q v w
    simp only [act]
    rw [← toAdd_mul, ← map_mul, ← conjP_mul, ← map_mul]
    rfl
  have act_mul : ∀ q q' v, act (q * q') v = act q (act q' v) := by
    intro q q' v
    simp only [act]
    rw [conjP_comp]
    simp
  have act_one : ∀ v, act 1 v = v := by
    intro v; simp [act, conjP_one]
  have act_zero : ∀ q, act q 0 = 0 := fun q => by
    have := act_add q 0 0
    simpa using this
  have act_nsmul : ∀ q (n : ℕ) v, act q (n • v) = n • act q v := by
    intro q n v
    induction n with
    | zero => simp [act_zero]
    | succ n ih => rw [succ_nsmul, act_add, ih, succ_nsmul]
  have act_smul : ∀ q (c : ZMod 5) v, act q (c • v) = c • act q v := by
    intro q c v
    have hc : ∀ w : Fin 2 → ZMod 5, c • w = c.val • w := fun w => by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 5) c.val w, ZMod.natCast_zmod_val]
    rw [hc, act_nsmul, ← hc]
  set v₀ : Fin 2 → ZMod 5 := Multiplicative.toAdd (e ⟨a, haP⟩) with hv₀def
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have h1 : e ⟨a, haP⟩ = 1 := h
    have h2 : (⟨a, haP⟩ : ↥P) = 1 := e.injective (by rw [h1, map_one])
    exact ha1' (congrArg Subtype.val h2)
  have hline : ∀ q : ↥Q, ∃ c : ZMod 5, act q v₀ = c • v₀ := by
    intro q
    have hqa : (q : X) * a * (q : X)⁻¹ ∈ Y := hQY q q.2 a haY
    rw [hYz] at hqa
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqa
    refine ⟨(k : ZMod 5), ?_⟩
    have h1 : conjP q (e.symm (Multiplicative.ofAdd v₀)) = (⟨a, haP⟩ : ↥P) ^ k := by
      apply Subtype.ext
      simp only [hv₀def, ofAdd_toAdd, MulEquiv.symm_apply_apply, conjP, Subgroup.coe_zpow]
      exact hk.symm
    simp only [act]
    rw [h1, map_zpow, toAdd_zpow, ← hv₀def]
    exact (Int.cast_smul_eq_zsmul (ZMod 5) k v₀).symm
  obtain ⟨v₁, hspan, huniq⟩ := basis_aux v₀ hv₀
  choose c hc using hline
  choose s m hsm using fun q : ↥Q => hspan (act q v₁)
  have scal : ∀ c₁ d₁ : ZMod 5, c₁ • v₀ = d₁ • v₀ → c₁ = d₁ := fun c₁ d₁ h =>
    (huniq c₁ 0 d₁ 0 (by rw [zero_smul, add_zero, add_zero]; exact h)).1
  have hcmul : ∀ q q', c (q * q') = c q * c q' := by
    intro q q'
    apply scal
    rw [← hc, act_mul, hc q', act_smul, hc q, smul_smul, mul_comm]
  have hmsm : ∀ q q', s (q * q') • v₀ + m (q * q') • v₁ =
      (s q' * c q + m q' * s q) • v₀ + (m q * m q') • v₁ := by
    intro q q'
    rw [← hsm, act_mul, hsm q', act_add, act_smul, act_smul, hsm q, hc q]
    module
  have hmmul : ∀ q q', m (q * q') = m q * m q' := fun q q' => (huniq _ _ _ _ (hmsm q q')).2
  have hc1 : c 1 = 1 := by
    apply scal
    rw [← hc, act_one, one_smul]
  have hm1 : m 1 = 1 := by
    have h1 : s 1 • v₀ + m 1 • v₁ = (0 : ZMod 5) • v₀ + (1 : ZMod 5) • v₁ := by
      rw [← hsm, act_one, zero_smul, one_smul, zero_add]
    exact (huniq _ _ _ _ h1).2
  have hkernel : ∀ q : ↥Q, c q = 1 → m q = 1 → q = 1 := by
    intro q hcq hmq
    have h0 : act q v₀ = v₀ := by rw [hc, hcq, one_smul]
    have h1 : act q v₁ = s q • v₀ + v₁ := by rw [hsm, hmq, one_smul]
    have hpow : ∀ n : ℕ, act (q ^ n) v₀ = v₀ ∧ act (q ^ n) v₁ = (n • s q) • v₀ + v₁ := by
      intro n
      induction n with
      | zero => simp [act_one]
      | succ n ih =>
        rw [pow_succ]
        refine ⟨by rw [act_mul, h0, ih.1], ?_⟩
        rw [act_mul, h1, act_add, act_smul, ih.1, ih.2, succ_nsmul]
        module
    have h8 : q ^ 8 = 1 := by
      have : Finite ↥Q := inferInstance
      rw [← hQ8]; exact pow_card_eq_one'
    have hs : 8 • s q = 0 := by
      apply scal
      have := (hpow 8).2
      rw [h8, act_one] at this
      have h3 : (8 • s q) • v₀ + v₁ = (0 : ZMod 5) • v₀ + v₁ := by
        rw [← this, zero_smul, zero_add]
      exact add_right_cancel h3
    have hs0 : s q = 0 := eight_smul_eq_zero _ hs
    have h1' : act q v₁ = v₁ := by rw [h1, hs0, zero_smul, zero_add]
    have hall : ∀ w, act q w = w := by
      intro w
      obtain ⟨c₁, c₂, rfl⟩ := hspan w
      rw [act_add, act_smul, act_smul, h0, h1']
    apply Subtype.ext
    refine hker q q.2 fun d hd => ?_
    have h2 := hall (Multiplicative.toAdd (e ⟨d, hd⟩))
    simp only [act, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h2
    have h3 : e (conjP q ⟨d, hd⟩) = e ⟨d, hd⟩ := h2
    have h4 := e.injective h3
    exact congrArg Subtype.val h4
  have hcinv : ∀ q : ↥Q, c q⁻¹ * c q = 1 := fun q => by rw [← hcmul, inv_mul_cancel, hc1]
  have hminv : ∀ q : ↥Q, m q⁻¹ * m q = 1 := fun q => by rw [← hmmul, inv_mul_cancel, hm1]
  have hcomm : ∀ q q' : ↥Q, q * q' = q' * q := by
    intro q q'
    have hg : q * q' * q⁻¹ * q'⁻¹ = 1 := by
      apply hkernel
      · rw [hcmul, hcmul, hcmul]
        calc c q * c q' * c q⁻¹ * c q'⁻¹ = (c q⁻¹ * c q) * (c q'⁻¹ * c q') := by ring
          _ = 1 := by rw [hcinv q, hcinv q', one_mul]
      · rw [hmmul, hmmul, hmmul]
        calc m q * m q' * m q⁻¹ * m q'⁻¹ = (m q⁻¹ * m q) * (m q'⁻¹ * m q') := by ring
          _ = 1 := by rw [hminv q, hminv q', one_mul]
    calc q * q' = (q * q' * q⁻¹ * q'⁻¹) * (q' * q) := by group
      _ = q' * q := by rw [hg, one_mul]
  let _ : CommGroup ↥Q := { (inferInstance : Group ↥Q) with mul_comm := hcomm }
  exact false_of_comm_card_eight hQ8 φ hφ

end CFSG.Quasithin.He16
