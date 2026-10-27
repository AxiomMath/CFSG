module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.ChevalleyPerm
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem not_pow_dvd_factorial_G2 {r e : ℕ} (hr : r.Prime) (he : 1 ≤ e)
    (hre : r ≠ 2 ∨ 2 ≤ e) : ¬ r ^ (6 * e) ∣ (14).factorial := by
  intro h
  have h6 : r ^ 6 ∣ (14).factorial := (pow_dvd_pow r (by omega : 6 ≤ 6 * e)).trans h
  have hle : r ≤ 14 :=
    (Nat.Prime.dvd_factorial hr).1 ((dvd_pow_self r (by norm_num)).trans h6)
  by_cases hr2 : r = 2
  · subst hr2
    have he2 : 2 ≤ e := hre.resolve_left (by simp)
    have h12 : 2 ^ 12 ∣ (14).factorial := (pow_dvd_pow 2 (by omega : 12 ≤ 6 * e)).trans h
    revert h12
    decide
  · interval_cases r
    all_goals first
      | (exfalso; revert hr; norm_num; done)
      | (revert h6; decide)
      | exact absurd rfl hr2

theorem not_pow_dvd_factorial_F4_odd {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e) :
    ¬ r ^ (24 * e) ∣ (52).factorial := by
  intro h
  have h24 : r ^ 24 ∣ (52).factorial := (pow_dvd_pow r (by omega : 24 ≤ 24 * e)).trans h
  have hle : r ≤ 52 :=
    (Nat.Prime.dvd_factorial hr).1 ((dvd_pow_self r (by norm_num)).trans h24)
  interval_cases r
  all_goals first
    | (exfalso; revert hr; norm_num; done)
    | (revert h24; decide)
    | exact absurd rfl hr2

variable {K : Type} [Field K] [Finite K]

theorem exists_card_fixSubfield (σ : K ≃+* K) (r : ℕ) [Fact r.Prime] [CharP K r] :
    ∃ e : ℕ, 1 ≤ e ∧ Nat.card (fixSubfield σ) = r ^ e := by
  have hkr : CharP (fixSubfield σ) r :=
    (RingHom.charP_iff (fixSubfield σ).subtype (fixSubfield σ).subtype.injective r).mpr
      ‹CharP K r›
  have : Fintype (fixSubfield σ) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card (fixSubfield σ) r
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem nonLocalized_G2_of_card_ne_two
    (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) ≠ 2) :
    NonLocalized ((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)) := by
  obtain ⟨r, hrK⟩ := CharP.exists K
  have hr : r.Prime := CharP.char_is_prime K r
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨e, he, hke⟩ := exists_card_fixSubfield σ r
  have hre : r ≠ 2 ∨ 2 ≤ e := by
    by_cases h2 : r = 2
    · right
      by_contra hcon
      have : e = 1 := by omega
      subst this
      exact hk (by rw [hke, h2]; norm_num)
    · exact Or.inl h2
  have h3 : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [hke]
    rcases hre with h2 | h2
    · have : 3 ≤ r := by
        rcases hr.eq_two_or_odd' with h | h
        · exact absurd h h2
        · have := hr.two_le
          rcases h with ⟨m, hm⟩
          omega
      calc 3 ≤ r := this
        _ = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ e := Nat.pow_le_pow_right hr.pos he
    · calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ r ^ 2 := Nat.pow_le_pow_left hr.two_le 2
        _ ≤ r ^ e := Nat.pow_le_pow_right hr.pos h2
  have hsimple : IsSimpleGroup ↥(adjointGroup .G2 (fixSubfield σ)) :=
    isSimpleGroup_adjointGroup_of_quasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card _ h3)
  refine nonLocalized_fixedFieldImage_of_perm σ r hsimple ?_
  rw [hke, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2, ← pow_mul']
  exact not_pow_dvd_factorial_G2 hr he hre

theorem nonLocalized_F4_of_ne_two
    (σ : K ≃+* K) (r : ℕ) [Fact r.Prime] [CharP K r]
    (hr2 : r ≠ 2) :
    NonLocalized ((fixedFieldImage .F4 σ).subgroupOf (adjointGroup .F4 K)) := by
  obtain ⟨e, he, hke⟩ := exists_card_fixSubfield σ r
  have hsimple : IsSimpleGroup ↥(adjointGroup .F4 (fixSubfield σ)) :=
    isSimpleGroup_adjointGroup_of_quasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 _)
  refine nonLocalized_fixedFieldImage_of_perm σ r hsimple ?_
  rw [hke, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4, ← pow_mul']
  exact not_pow_dvd_factorial_F4_odd (Fact.out) hr2 he

end CFSG.SignalizerFunctorTheorem.NonLocalExc
