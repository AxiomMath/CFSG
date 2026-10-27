module

public import CFSG.Walter.Bender1970.S38.Omega
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Walter

open CFSG.SectionRank.Ccomm

variable {Q : Type*} [CommGroup Q] [Finite Q]

theorem card_mulAut_of_elementary (h2 : ∀ v : Q, v ^ 2 = 1) :
    (Nat.card Q = 4 → Nat.card (MulAut Q) = 6) ∧ (Nat.card Q = 8 → Nat.card (MulAut Q) = 168) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a b : Q, a * b = b * a := mul_comm
  refine ⟨fun h4 => ?_, fun h8 => ?_⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 2) hcomm h2
      (n := 2) (by rw [h4]; norm_num)
    rw [card_mulAut_eq_card_GL e, card_GL_zmod]
    simp [Fin.prod_univ_succ]
  · obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 2) hcomm h2
      (n := 3) (by rw [h8]; norm_num)
    rw [card_mulAut_eq_card_GL e, card_GL_zmod]
    simp [Fin.prod_univ_succ]

theorem exists_regular_of_card_eq (h2 : ∀ v : Q, v ^ 2 = 1)
    (hQ : Nat.card Q = 4 ∨ Nat.card Q = 8) {N : Subgroup (MulAut Q)} (hNodd : Odd (Nat.card N))
    (htrans : ∀ u v : Q, u ≠ 1 → v ≠ 1 → ∃ n ∈ N, n u = v) :
    ∃ R : Subgroup (MulAut Q), R ≤ N ∧ IsCyclic R ∧ Nat.card R + 1 = Nat.card Q ∧
      (∀ r ∈ R, ∀ v : Q, r v = v → v ≠ 1 → r = 1) ∧
      (∀ u v : Q, u ≠ 1 → v ≠ 1 → ∃ r ∈ R, r u = v) ∧
      (∀ g : MulAut Q, (∀ n ∈ N, g * n * g⁻¹ ∈ N) → ∀ r ∈ R, g * r * g⁻¹ ∈ R) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set p := Nat.card Q - 1 with hpdef
  have hp : p.Prime := by rcases hQ with h | h <;> rw [hpdef, h] <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hA4, hA8⟩ := card_mulAut_of_elementary h2
  have hNdvd : Nat.card N ∣ Nat.card (MulAut Q) := Subgroup.card_subgroup_dvd_card N
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Q, v₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card Q = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [h a, h b]⟩,
      ⟨1⟩⟩
    rcases hQ with h' | h' <;> omega
  have hNge : p ≤ Nat.card N := by
    have h1 := card_ne_one_add_one Q
    have hsurj : Function.Surjective (fun n : N => (⟨(n : MulAut Q) v₀, fun h => hv₀
        ((MulEquiv.map_eq_one_iff _).mp h)⟩ : {v : Q // v ≠ 1})) := by
      intro v
      obtain ⟨n, hn, hnv⟩ := htrans v₀ v hv₀ v.2
      exact ⟨⟨n, hn⟩, Subtype.ext hnv⟩
    have h2' := Nat.card_le_card_of_surjective _ hsurj
    omega
  have hpN : p ∣ Nat.card N ∧ Nat.card N < p * p := by
    rcases hQ with h | h
    · rw [hA4 h] at hNdvd
      have hp3 : p = 3 := by rw [hpdef, h]
      rw [hp3] at hNge ⊢
      have : Nat.card N ∣ 3 := by
        have h6 : (6 : ℕ) = 2 * 3 := rfl
        rw [h6] at hNdvd
        exact (Nat.Coprime.dvd_of_dvd_mul_left
          (Nat.Coprime.symm (Nat.coprime_two_left.mpr hNodd)) hNdvd)
      have h3 := Nat.le_of_dvd (by norm_num) this
      have : Nat.card N = 3 := by omega
      rw [this]
      norm_num
    · rw [hA8 h] at hNdvd
      have hp7 : p = 7 := by rw [hpdef, h]
      rw [hp7] at hNge ⊢
      have h21 : Nat.card N ∣ 21 := by
        have h168 : (168 : ℕ) = 8 * 21 := rfl
        rw [h168] at hNdvd
        exact (Nat.Coprime.dvd_of_dvd_mul_left
          (Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hNodd)).symm hNdvd)
      have hle := Nat.le_of_dvd (by norm_num) h21
      have : Nat.card N = 7 ∨ Nat.card N = 21 := by
        interval_cases hc : Nat.card N <;> omega
      rcases this with h' | h' <;> rw [h'] <;> norm_num
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpN.1
  set R : Subgroup (MulAut Q) := Subgroup.zpowers (n : MulAut Q) with hR
  have hRN : R ≤ N := (Subgroup.zpowers_le).mpr n.2
  have hRcard : Nat.card R = p := by
    rw [hR, Nat.card_zpowers, Subgroup.orderOf_coe, hn]
  have huniq : ∀ S : Subgroup (MulAut Q), S ≤ N → Nat.card S = p → S = R := by
    intro S hSN hS
    by_contra hne
    have hinf : S ⊓ R = ⊥ := by
      have hdvd : Nat.card (S ⊓ R : Subgroup (MulAut Q)) ∣ p :=
        hS ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact Subgroup.card_eq_one.mp h
      · exfalso
        apply hne
        have h1 : S ⊓ R = S := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hS])
        have h2 : S ⊓ R = R := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hRcard])
        rw [← h1, h2]
    have := card_mul_card_le_of_inf_eq_bot hSN hRN hinf
    rw [hS, hRcard] at this
    exact absurd this (not_le.mpr hpN.2)
  have hfree : ∀ r ∈ R, ∀ v : Q, r v = v → v ≠ 1 → r = 1 := by
    intro r hr v hrv hv1
    by_contra hr1
    have hrR : R = Subgroup.zpowers r := by
      symm
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hr) ?_
      rw [hRcard]
      have hdvd : Nat.card (Subgroup.zpowers r) ∣ p := hRcard ▸ Subgroup.card_dvd_of_le
        ((Subgroup.zpowers_le).mpr hr)
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exfalso
        rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
        exact hr1 h
      · exact h.ge
    set C : Subgroup Q := MonoidHom.eqLocus r.toMonoidHom (MonoidHom.id Q) with hC
    have hrp : IsPGroup p (Subgroup.zpowers r) := by
      rw [← hrR]
      exact IsPGroup.of_card (n := 1) (by rw [hRcard, pow_one])
    have hmod := hrp.card_modEq_card_fixedPoints Q
    have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers r) Q) = Nat.card C := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
      constructor
      · intro hw
        exact hw ⟨r, Subgroup.mem_zpowers r⟩
      · intro hw
        rintro ⟨g', hg'⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
        have hwr : r w = w := hw
        have key : ∀ k : ℤ, (r ^ k) w = w := by
          intro k
          induction k using Int.induction_on with
          | zero => rfl
          | succ k ih => rw [zpow_add_one, MulAut.mul_apply, hwr, ih]
          | pred k ih =>
            rw [zpow_sub_one, MulAut.mul_apply]
            calc (r ^ (-(k : ℤ))) (r⁻¹ w) = (r ^ (-(k : ℤ))) (r⁻¹ (r w)) := by rw [hwr]
              _ = w := by rw [MulAut.inv_apply_self, ih]
        exact key k
    rw [hfix] at hmod
    have hQp : IsPGroup 2 Q := fun a => ⟨1, by rw [pow_one, h2]⟩
    obtain ⟨c, hc⟩ := (hQp.to_subgroup C).exists_card_eq
    have hvC : v ∈ C := hrv
    have hc1 : 1 ≤ c := by
      by_contra h0
      have hC1 : Nat.card C = 1 := by rw [hc, show c = 0 by omega, pow_zero]
      have := Subgroup.card_eq_one.mp hC1
      rw [this] at hvC
      exact hv1 hvC
    have hCQ : Nat.card C < Nat.card Q := by
      by_contra hge
      have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (le_antisymm
        (Subgroup.card_le_card_group C) (not_lt.mp hge))
      apply hr1
      ext w
      have hw : w ∈ C := hCtop ▸ Subgroup.mem_top w
      exact hw
    have hCdvd : Nat.card C ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card C
    rw [hc] at hmod hCQ hCdvd
    rcases hQ with h | h
    · rw [h] at hmod hCQ hCdvd
      have hp3 : p = 3 := by rw [hpdef, h]
      rw [hp3] at hmod
      have : 2 ^ c ≤ 2 ^ 1 := by
        have := Nat.le_of_dvd (by norm_num) hCdvd
        have h2c : 2 ^ c ≠ 4 := by omega
        have h4 : (4 : ℕ) = 2 ^ 2 := rfl
        rw [h4] at hCQ
        exact Nat.pow_le_pow_right (by norm_num) (by
          have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hCQ; omega)
      have hc' : c = 1 := by
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
        omega
      rw [hc'] at hmod
      exact absurd hmod (by decide)
    · rw [h] at hmod hCQ hCdvd
      have hp7 : p = 7 := by rw [hpdef, h]
      rw [hp7] at hmod
      have h8 : (8 : ℕ) = 2 ^ 3 := rfl
      rw [h8] at hCQ
      have hc3 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hCQ
      interval_cases c <;> exact absurd hmod (by decide)
  refine ⟨R, hRN, ?_, ?_, hfree, ?_, ?_⟩
  · exact isCyclic_of_prime_card hRcard
  · rw [hRcard, hpdef]
    rcases hQ with h | h <;> omega
  ·
    intro u v hu hv
    have hinj : Function.Injective (fun r : R => (⟨(r : MulAut Q) u, fun h => hu
        ((MulEquiv.map_eq_one_iff _).mp h)⟩ : {w : Q // w ≠ 1})) := by
      intro r₁ r₂ h
      have h1 : (r₁ : MulAut Q) u = (r₂ : MulAut Q) u := congrArg Subtype.val h
      have h3 : ((r₁ : MulAut Q)⁻¹ * r₂) u = u := by
        rw [MulAut.mul_apply, ← h1, MulAut.inv_apply_self]
      have h4 := hfree _ (R.mul_mem (R.inv_mem r₁.2) r₂.2) u h3 hu
      rw [inv_mul_eq_one] at h4
      exact Subtype.ext h4
    have hcard : Nat.card R = Nat.card {w : Q // w ≠ 1} := by
      have := card_ne_one_add_one Q
      rw [hRcard, hpdef]
      omega
    have hbij := (Function.Injective.bijective_of_nat_card_le hinj hcard.ge).2
    obtain ⟨r, hr⟩ := hbij ⟨v, hv⟩
    exact ⟨r, r.2, congrArg Subtype.val hr⟩
  · intro g hg r hr
    have hS : (R.map (MulAut.conj g).toMonoidHom) = R := by
      refine huniq _ ?_ (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        hRcard])
      rintro _ ⟨x, hx, rfl⟩
      exact hg x (hRN hx)
    have : g * r * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rwa [hS] at this

end CFSG.Walter
