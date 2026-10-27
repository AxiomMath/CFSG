module

public import CFSG.Quasithin.EmptyFaithful.S146zNIrr5A

public section

namespace CFSG.Quasithin.A6Irr5

variable {V : Type*} [CommGroup V]

theorem map_prod_eq_of_invariant (L : Subgroup (MulAut V)) {T : Finset V}
    (hT : ∀ l ∈ L, ∀ t ∈ T, l t ∈ T) {l : MulAut V} (hl : l ∈ L) :
    l (∏ t ∈ T, t) = ∏ t ∈ T, t := by
  classical
  have himg : T.image l = T := Finset.eq_of_subset_of_card_le
    (fun x hx => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact hT l hl t ht)
    (Finset.card_image_of_injective _ l.injective).ge
  calc l (∏ t ∈ T, t) = ∏ t ∈ T, l t := map_prod l _ _
    _ = ∏ x ∈ T.image l, x :=
        (Finset.prod_image (s := T) (g := fun t => l t) (f := fun x => x)
          fun a _ b _ h => l.injective h).symm
    _ = ∏ t ∈ T, t := by rw [himg]

theorem false_of_invariant_six [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 32)
    {L : Subgroup (MulAut V)}
    (hirr : ∀ S : Subgroup V, (∀ l ∈ L, ∀ w ∈ S, l w ∈ S) → S = ⊥ ∨ S = ⊤)
    {T : Finset V} (hT : ∀ l ∈ L, ∀ t ∈ T, l t ∈ T) (h6 : T.card = 6) : False := by
  classical
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  have hσ : ∏ t ∈ T, t = 1 := by
    refine eq_one_of_invariant_finset hV hcard hirr (T := {∏ t ∈ T, t}) ?_ (by simp) _
      (Finset.mem_singleton_self _)
    intro l hl t ht
    rw [Finset.mem_singleton] at ht ⊢
    rw [ht]
    exact map_prod_eq_of_invariant L hT hl
  obtain ⟨w₀, hw₀⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have h5 : (T.erase w₀).card = 5 := by rw [Finset.card_erase_of_mem hw₀, h6]
  obtain ⟨w₁, hw₁⟩ : (T.erase w₀).Nonempty := Finset.card_pos.mp (by omega)
  have h4 : ((T.erase w₀).erase w₁).card = 4 := by rw [Finset.card_erase_of_mem hw₁, h5]
  have hw₁T : w₁ ∈ T := Finset.mem_of_mem_erase hw₁
  have hw₁ne : w₁ ≠ w₀ := Finset.ne_of_mem_erase hw₁
  set R := (T.erase w₀).erase w₁ with hR
  have hprod : w₀ * (w₁ * ∏ t ∈ R, t) = 1 := by
    have e1 := Finset.mul_prod_erase (T.erase w₀) (fun t => t) hw₁
    have e2 := Finset.mul_prod_erase T (fun t => t) hw₀
    rw [e1, e2]
    exact hσ
  have hP : ∏ t ∈ R, t = w₁ * w₀ := by
    have h1 : w₁ * ∏ t ∈ R, t = w₀ := by
      have := eq_inv_of_mul_eq_one_right hprod
      rwa [hinv] at this
    have h2 := eq_inv_mul_of_mul_eq h1
    rwa [hinv] at h2
  have hprodU : ∏ w ∈ R, (w * w₀) = w₁ * w₀ := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, h4, hP]
    have : w₀ ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hV]
    rw [this, mul_one]
  let U : Finset V := R.image (fun w => w * w₀)
  have hUcard : U.card ≤ 4 := Finset.card_image_le.trans h4.le
  have hmemU : ∀ a ∈ T, a * w₀ ∈ Subgroup.closure (U : Set V) := by
    intro a ha
    by_cases h0 : a = w₀
    · rw [h0, hsq]
      exact one_mem _
    by_cases h1 : a = w₁
    · rw [h1, ← hprodU]
      exact Subgroup.prod_mem _ fun c hc => Subgroup.subset_closure
        (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨c, hc, rfl⟩))
    · exact Subgroup.subset_closure (Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨a, Finset.mem_erase.mpr ⟨h1, Finset.mem_erase.mpr ⟨h0, ha⟩⟩, rfl⟩))
  let T₂ : Set V := {x | ∃ a ∈ T, ∃ b ∈ T, x = a * b}
  have hT₂ : ∀ l ∈ L, ∀ x ∈ T₂, l x ∈ T₂ := by
    rintro l hl _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨l a, hT l hl a ha, l b, hT l hl b hb, map_mul l a b⟩
  have hE_le : Subgroup.closure T₂ ≤ Subgroup.closure (U : Set V) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have hab : a * b = (a * w₀) * (b * w₀) := by
      rw [mul_mul_mul_comm, hsq, mul_one]
    show a * b ∈ Subgroup.closure (U : Set V)
    rw [hab]
    exact mul_mem (hmemU a ha) (hmemU b hb)
  have hEbot : Subgroup.closure T₂ = ⊥ := by
    refine eq_bot_of_card_le hcard hirr (closure_invariant L hT₂) ?_
    calc Nat.card (Subgroup.closure T₂) ≤ Nat.card (Subgroup.closure (U : Set V)) :=
          Subgroup.card_le_of_le hE_le
      _ ≤ 2 ^ U.card := card_closure_le hV U
      _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hUcard
      _ = 16 := by norm_num
  have hmem : w₀ * w₁ ∈ Subgroup.closure T₂ := Subgroup.subset_closure ⟨w₀, hw₀, w₁, hw₁T, rfl⟩
  rw [hEbot, Subgroup.mem_bot] at hmem
  have hw : w₁ = w₀ := by
    have := eq_inv_of_mul_eq_one_right hmem
    rwa [hinv] at this
  exact hw₁ne hw

end CFSG.Quasithin.A6Irr5
