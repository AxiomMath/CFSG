module

public import CFSG.Quasithin.Recognition.U33Defs

public section

namespace CFSG.Quasithin

@[expose] def IsCentralProductZ4Q8 (P : Type*) [Group P] : Prop :=
  Nat.card P = 16 ∧ ∃ A B : Subgroup P,
    (A ≤ Subgroup.centralizer (B : Set P) ∧ A ⊔ B = ⊤) ∧ Nat.card A = 4 ∧ IsCyclic A ∧
      Nonempty (B ≃* QuaternionGroup 2)

private theorem order_le_two_cases (x : Multiplicative (ZMod 4) × QuaternionGroup 2)
    (h : x * x = 1) :
    x = 1 ∨ x = (Multiplicative.ofAdd 2, 1) ∨ x = (1, QuaternionGroup.a 2) ∨
      x = z4Q8Identification := by
  revert x
  decide

private theorem card_z4_prod_q8 :
    Nat.card (Multiplicative (ZMod 4) × QuaternionGroup 2) = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem nonempty_mulEquiv_Z4StarQ8_of_isCentralProductZ4Q8 {P : Type*} [Group P]
    (h : IsCentralProductZ4Q8 P) : Nonempty (P ≃* Z4StarQ8) := by
  obtain ⟨hcard, A, B, ⟨hAB, hgen⟩, hA4, hAcyc, ⟨β⟩⟩ := h
  obtain ⟨g, hg⟩ := hAcyc.exists_generator
  have hord : orderOf g = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hA4]
  set g' : P := (g : P) with hg'
  have hord' : orderOf g' = 4 := by rw [hg', Subgroup.orderOf_coe, hord]
  have h4 : ∀ n : ℕ, g' ^ (n % 4) = g' ^ n := fun n => by
    have := pow_mod_orderOf g' n
    rwa [hord'] at this
  let ι : Multiplicative (ZMod 4) → P := fun t => g' ^ (Multiplicative.toAdd t).val
  have hι : ∀ s t, ι (s * t) = ι s * ι t := by
    intro s t
    simp only [ι, toAdd_mul, ZMod.val_add]
    rw [h4, pow_add]
  have hιA : ∀ t, ι t ∈ A := fun t => A.pow_mem g.2 _
  have hcomm : ∀ (t : Multiplicative (ZMod 4)) (b : B), (b : P) * ι t = ι t * (b : P) := fun t b =>
    Subgroup.mem_centralizer_iff.mp (hAB (hιA t)) b b.2
  let Φ : Multiplicative (ZMod 4) × QuaternionGroup 2 →* P :=
    MonoidHom.mk' (fun x => ι x.1 * (β.symm x.2 : P)) (fun x y => by
      have hc := hcomm y.1 (β.symm x.2)
      calc ι (x.1 * y.1) * ((β.symm (x.2 * y.2) : B) : P)
          = ι x.1 * ι y.1 * ((β.symm x.2 : P) * (β.symm y.2 : P)) := by
            rw [hι, map_mul, Subgroup.coe_mul]
        _ = ι x.1 * ((ι y.1 * (β.symm x.2 : P)) * (β.symm y.2 : P)) := by group
        _ = ι x.1 * (((β.symm x.2 : P) * ι y.1) * (β.symm y.2 : P)) := by rw [hc]
        _ = (ι x.1 * (β.symm x.2 : P)) * (ι y.1 * (β.symm y.2 : P)) := by group)
  have hΦ : ∀ t q, Φ (t, q) = ι t * (β.symm q : P) := fun t q => rfl
  have hι1 : ι 1 = 1 := by simp [ι]
  have hιone : ι (Multiplicative.ofAdd 1) = g' := by
    show g' ^ ((1 : ZMod 4).val) = g'
    have : (1 : ZMod 4).val = 1 := rfl
    rw [this, pow_one]
  have hΦsurj : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine sup_le ?_ ?_
    · have hg'mem : g' ∈ Φ.range := ⟨(Multiplicative.ofAdd 1, 1), by
        rw [hΦ, hιone, map_one, Subgroup.coe_one, mul_one]⟩
      intro a ha
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
      have : g' ^ j = a := by
        have := congrArg Subtype.val hj
        simpa [hg'] using this
      rw [← this]
      exact Subgroup.zpow_mem _ hg'mem j
    · intro b hb
      refine ⟨(1, β ⟨b, hb⟩), ?_⟩
      rw [hΦ, hι1, one_mul, MulEquiv.symm_apply_apply]
  have hker : Φ.ker = Subgroup.zpowers z4Q8Identification := by
    have h2 : Nat.card Φ.ker = 2 := by
      have := Subgroup.card_ker_mul_card_of_surjective hΦsurj
      rw [hcard, card_z4_prod_q8] at this
      omega
    have : Nontrivial Φ.ker := Finite.one_lt_card_iff_nontrivial.mp (by rw [h2]; omega)
    obtain ⟨κ, hκ1⟩ := exists_ne (1 : Φ.ker)
    have hκ2 : κ * κ = 1 := by
      have := pow_card_eq_one' (G := Φ.ker) (x := κ)
      rwa [h2, sq] at this
    have hκ : κ.1 = z4Q8Identification := by
      rcases order_le_two_cases κ.1 (congrArg Subtype.val hκ2) with h | h | h | h
      · exact absurd (Subtype.ext h) hκ1
      · exfalso
        have h0 : Φ κ.1 = 1 := κ.2
        rw [h, hΦ, map_one, Subgroup.coe_one, mul_one] at h0
        have : ι (Multiplicative.ofAdd 2) = g' ^ 2 := rfl
        rw [this] at h0
        have := orderOf_dvd_of_pow_eq_one h0
        rw [hord'] at this
        omega
      · exfalso
        have h0 : Φ κ.1 = 1 := κ.2
        rw [h, hΦ, hι1, one_mul] at h0
        have : β.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h0
        have := β.symm.injective (this.trans (map_one β.symm).symm)
        exact absurd this (by decide)
      · exact h
    have hle : Subgroup.zpowers z4Q8Identification ≤ Φ.ker :=
      Subgroup.zpowers_le.mpr (hκ ▸ κ.2)
    have hcz : Nat.card (Subgroup.zpowers z4Q8Identification) = 2 := by
      rw [Nat.card_zpowers]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by decide) (by decide)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h2, hcz])).symm
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective Φ hΦsurj).symm).trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

end CFSG.Quasithin
