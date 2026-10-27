module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private lemma s16h_e3_gl2_card : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field]
  norm_num

private lemma s16h_e3_gl2_inv :
    ∀ a b : GL (Fin 2) (ZMod 2), a ^ 2 = 1 → a ≠ 1 → b ^ 3 = 1 → b ≠ 1 →
      a * b * a⁻¹ = b ^ 2 := by
  decide

private lemma s16h_e3_gl2_order_ne_six (y : GL (Fin 2) (ZMod 2)) (hy : y ≠ 1)
    (h6 : orderOf y = 6) : False := by
  have hy6 : y ^ 6 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [h6] at h
  have ha2 : (y ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, show (3 : ℕ) * 2 = 6 by norm_num, hy6]
  have ha1 : y ^ 3 ≠ 1 := by
    intro h
    have hd : orderOf y ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [h6] at hd
    norm_num at hd
  have hb3 : (y ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show (2 : ℕ) * 3 = 6 by norm_num, hy6]
  have hb1 : y ^ 2 ≠ 1 := by
    intro h
    have hd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [h6] at hd
    norm_num at hd
  have h := s16h_e3_gl2_inv (y ^ 3) (y ^ 2) ha2 ha1 hb3 hb1
  have hL : y ^ 3 * y ^ 2 * (y ^ 3)⁻¹ = y ^ 2 := by group
  have hR : (y ^ 2) ^ 2 = y ^ 4 := by
    rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num]
  rw [hL, hR] at h
  have h2 : y ^ 2 = 1 := by
    have hh : (1 : GL (Fin 2) (ZMod 2)) = y ^ 2 := by
      have hc := congrArg (fun x => x * (y ^ 2)⁻¹) h
      rw [mul_inv_cancel] at hc
      have hc' : y ^ 4 * (y ^ 2)⁻¹ = y ^ 2 := by group
      rw [hc'] at hc
      exact hc
    exact hh.symm
  have hd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [h6] at hd
  norm_num at hd

private lemma s16h_e3_eq_of_card_two {G : Type} [Group G] {H : Subgroup G}
    (hH : Nat.card ↥H = 2) {e h : G} (he : e ∈ H) (he1 : e ≠ 1) (hh : h ∈ H) (hh1 : h ≠ 1) :
    h = e := by
  obtain ⟨y, -, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥H)).mp hH
  have he' : (⟨e, he⟩ : ↥H) = y := hyuniq _ (by simpa using he1)
  have hh' : (⟨h, hh⟩ : ↥H) = y := hyuniq _ (by simpa using hh1)
  exact Subtype.ext_iff.mp (hh'.trans he'.symm)

private lemma s16h_e3_card_three_unique {G : Type} [Group G] [Finite G] (hG : Nat.card G < 9)
    {Q Q' : Subgroup G} (hQ : Nat.card ↥Q = 3) (hQ' : Nat.card ↥Q' = 3) : Q = Q' := by
  by_contra hne
  have hdvd : Nat.card ↥(Q ⊓ Q') ∣ 3 := by
    have h := Subgroup.card_dvd_of_le (H := Q ⊓ Q') (K := Q) inf_le_left
    rwa [hQ] at h
  have hcardne : Nat.card ↥(Q ⊓ Q') ≠ 3 := by
    intro h
    apply hne
    have hle : Q ≤ Q' := by
      have hEq : Q ⊓ Q' = Q :=
        Subgroup.eq_of_le_of_card_ge (H := Q ⊓ Q') (K := Q) inf_le_left (by omega)
      rw [← hEq]
      exact inf_le_right
    have hle' : Q' ≤ Q := by
      have hEq : Q ⊓ Q' = Q' :=
        Subgroup.eq_of_le_of_card_ge (H := Q ⊓ Q') (K := Q') inf_le_right (by omega)
      rw [← hEq]
      exact inf_le_left
    exact le_antisymm hle hle'
  have hcard : Nat.card ↥(Q ⊓ Q') = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exact absurd h hcardne
  have hbot : Q ⊓ Q' = ⊥ := Subgroup.eq_bot_of_card_eq (Q ⊓ Q') hcard
  have hinj : Function.Injective (fun p : ↥Q × ↥Q' => (p.1 : G) * (p.2 : G)) := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
    simp only [Prod.mk.injEq] at hxy ⊢
    have hxQ : (x' : G)⁻¹ * (x : G) ∈ Q := Q.mul_mem (Q.inv_mem x'.2) x.2
    have hyQ' : (y' : G) * (y : G)⁻¹ ∈ Q' := Q'.mul_mem y'.2 (Q'.inv_mem y.2)
    have heq : (x' : G)⁻¹ * (x : G) = (y' : G) * (y : G)⁻¹ := by
      calc (x' : G)⁻¹ * (x : G)
          = (x' : G)⁻¹ * ((x : G) * (y : G)) * (y : G)⁻¹ := by group
        _ = (x' : G)⁻¹ * ((x' : G) * (y' : G)) * (y : G)⁻¹ := by rw [hxy]
        _ = (y' : G) * (y : G)⁻¹ := by group
    have h1 : (x' : G)⁻¹ * (x : G) = 1 := by
      have hmem : (x' : G)⁻¹ * (x : G) ∈ Q ⊓ Q' := ⟨hxQ, by rw [heq]; exact hyQ'⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h2 : (y' : G) * (y : G)⁻¹ = 1 := by
      have hmem : (y' : G) * (y : G)⁻¹ ∈ Q ⊓ Q' := ⟨by rw [← heq]; exact hxQ, hyQ'⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hx' : (x' : G) = (x : G) := inv_mul_eq_one.mp h1
    have hy' : (y' : G) = (y : G) := mul_inv_eq_one.mp h2
    exact ⟨Subtype.ext hx'.symm, Subtype.ext hy'.symm⟩
  have hle9 : Nat.card (↥Q × ↥Q') ≤ Nat.card G :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod ↥Q ↥Q', hQ, hQ'] at hle9
  omega

theorem s16h_e3_gl2_K_structure {K : Type} [Group K] [Finite K]
    (π₁ π₂ : K →* GL (Fin 2) (ZMod 2))
    (hinj : ∀ x : K, π₁ x = 1 → π₂ x = 1 → x = 1)
    (hno : ∀ x : K, orderOf x = 3 → π₁ x ≠ 1 ∧ π₂ x ≠ 1)
    {d : K} (hd : orderOf d = 3) :
    ∃ Z : Subgroup K, Nat.card ↥Z = 3 ∧ d ∈ Z ∧
      (∀ Z' : Subgroup K, Nat.card ↥Z' = 3 → Z' = Z) ∧
      ∀ k : K, k ∈ Z ∨ (k ^ 2 = 1 ∧ ∀ z ∈ Z, k * z * k⁻¹ = z⁻¹) := by
  classical
  let N : Subgroup K := π₁.ker
  let g : ↥N →* GL (Fin 2) (ZMod 2) := π₂.comp N.subtype
  have hg_ker : g.ker = ⊥ := by
    ext x
    rw [Subgroup.mem_bot, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact Subtype.ext
        (hinj (x : K) (MonoidHom.mem_ker.mp (show (x : K) ∈ π₁.ker from x.2)) hx)
    · intro hx
      rw [hx, map_one]
  have hg_inj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hg_ker
  have hdvdN : Nat.card ↥N ∣ 6 := by
    have h := Subgroup.card_dvd_of_injective g hg_inj
    rwa [s16h_e3_gl2_card] at h
  have h3notdvd : ¬ 3 ∣ Nat.card ↥N := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 h3
    have hxK : orderOf (x : K) = 3 := (Subgroup.orderOf_coe x).trans hx
    exact (hno (x : K) hxK).1
      (MonoidHom.mem_ker.mp (show (x : K) ∈ π₁.ker from x.2))
  have hcop : Nat.Coprime (Nat.card ↥N) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr h3notdvd).symm
  have hdvd2 : Nat.card ↥N ∣ 2 := by
    refine (Nat.Coprime.dvd_mul_right hcop).mp ?_
    simpa using hdvdN
  have hNcases : Nat.card ↥N = 1 ∨ Nat.card ↥N = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hdvd2
  have hNnot2 : Nat.card ↥N ≠ 2 := by
    intro hN2
    have h2dvd : 2 ∣ Nat.card ↥N := by rw [hN2]
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2dvd
    have huK : orderOf (u : K) = 2 := (Subgroup.orderOf_coe u).trans hu
    have hu1 : (u : K) ≠ 1 := by
      intro h
      have : orderOf (u : K) = 1 := orderOf_eq_one_iff.mpr h
      omega
    have hmem_conj : d * (u : K) * d⁻¹ ∈ N := by
      show d * (u : K) * d⁻¹ ∈ π₁.ker
      exact (MonoidHom.normal_ker π₁).conj_mem (u : K)
        (show (u : K) ∈ π₁.ker from u.2) d
    have hconj_ne1 : d * (u : K) * d⁻¹ ≠ 1 := by
      intro h
      apply hu1
      have hc := congrArg (fun x => d⁻¹ * x * d) h
      simpa [mul_assoc] using hc
    have hcen : d * (u : K) * d⁻¹ = (u : K) :=
      s16h_e3_eq_of_card_two hN2 u.2 hu1 hmem_conj hconj_ne1
    have hcomm : d * (u : K) = (u : K) * d := by
      have hc := congrArg (fun x => x * d) hcen
      simpa [mul_assoc] using hc
    have hpu_ord : orderOf (π₂ (u : K)) = 2 := by
      have h := orderOf_injective g hg_inj u
      simpa [g, hu] using h
    have hpu2 : (π₂ (u : K)) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one (π₂ (u : K))
      rwa [hpu_ord] at h
    have hpu1 : π₂ (u : K) ≠ 1 := by
      intro h
      have hgu : g u = 1 := h
      have hu_eq : u = 1 := hg_inj (by rw [hgu, map_one])
      exact hu1 (congrArg Subtype.val hu_eq)
    have hd3 : d ^ 3 = 1 := by
      have h := pow_orderOf_eq_one d
      rwa [hd] at h
    have hpd3 : (π₂ d) ^ 3 = 1 := by
      rw [← map_pow, hd3, map_one]
    have hpd1 : π₂ d ≠ 1 := (hno d hd).2
    have hgl := s16h_e3_gl2_inv (π₂ (u : K)) (π₂ d) hpu2 hpu1 hpd3 hpd1
    have hcomm2 : π₂ (u : K) * π₂ d = π₂ d * π₂ (u : K) := by
      simp only [← map_mul]
      rw [hcomm]
    have hpinv : (π₂ (u : K))⁻¹ = π₂ (u : K) :=
      inv_eq_self_of_orderOf_eq_two hpu_ord
    have hLHS : π₂ (u : K) * π₂ d * (π₂ (u : K))⁻¹ = π₂ d := by
      rw [hpinv, hcomm2, mul_assoc, ← pow_two, hpu2, mul_one]
    have hpdsq : π₂ d = (π₂ d) ^ 2 := by
      rw [hLHS] at hgl
      exact hgl
    have hpd_eq_one : π₂ d = 1 := by
      have hc := congrArg (fun x => x * (π₂ d)⁻¹) hpdsq
      have h1 : (1 : GL (Fin 2) (ZMod 2)) = π₂ d := by
        simpa [pow_two, mul_assoc] using hc
      exact h1.symm
    exact hpd1 hpd_eq_one
  have hN1 : Nat.card ↥N = 1 := by
    rcases hNcases with h | h
    · exact h
    · exact absurd h hNnot2
  have hker_bot : π₁.ker = ⊥ := by
    have h := Subgroup.eq_bot_of_card_eq N hN1
    simpa [N] using h
  have hpinj : Function.Injective π₁ := (MonoidHom.ker_eq_bot_iff π₁).mp hker_bot
  have hKle : Nat.card K ≤ 6 := by
    have h := Nat.card_le_card_of_injective π₁ hpinj
    rwa [s16h_e3_gl2_card] at h
  have hKlt : Nat.card K < 9 := by omega
  have hd3 : d ^ 3 = 1 := by
    have h := pow_orderOf_eq_one d
    rwa [hd] at h
  refine ⟨Subgroup.zpowers d, ?_, Subgroup.mem_zpowers d, ?_, ?_⟩
  · rw [Nat.card_zpowers, hd]
  · intro Z' hZ'
    exact s16h_e3_card_three_unique hKlt hZ' (by rw [Nat.card_zpowers, hd])
  · intro k
    by_cases hk : k ∈ Subgroup.zpowers d
    · exact Or.inl hk
    · right
      have hk1 : k ≠ 1 := fun h => hk (h ▸ (Subgroup.zpowers d).one_mem)
      have hkordvd : orderOf k ∣ 6 := by
        have h := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers (π₁ k))
        rw [Nat.card_zpowers, s16h_e3_gl2_card] at h
        rwa [orderOf_injective π₁ hpinj k] at h
      have hk3 : orderOf k ≠ 3 := by
        intro h3
        apply hk
        have hcard : Nat.card ↥(Subgroup.zpowers k) = 3 := by rw [Nat.card_zpowers, h3]
        have huniq := s16h_e3_card_three_unique hKlt hcard (by rw [Nat.card_zpowers, hd])
        rw [← huniq]
        exact Subgroup.mem_zpowers k
      have hk6 : orderOf k ≠ 6 := by
        intro h6
        have hπk1 : π₁ k ≠ 1 := by
          intro h
          exact hk1 (hpinj (by rw [h, map_one]))
        have hπk6 : orderOf (π₁ k) = 6 := by
          rw [orderOf_injective π₁ hpinj k, h6]
        exact s16h_e3_gl2_order_ne_six (π₁ k) hπk1 hπk6
      have hkord : orderOf k = 2 := by
        have hne1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
        obtain ⟨c, hc⟩ := hkordvd
        have hcdvd : c ∣ 6 := ⟨orderOf k, by rw [mul_comm, hc]⟩
        have hcle : c ≤ 6 := Nat.le_of_dvd (by norm_num) hcdvd
        have hcpos : 0 < c := by
          by_contra h
          have h0 : c = 0 := Nat.eq_zero_of_not_pos h
          rw [h0, mul_zero] at hc
          omega
        interval_cases c <;> omega
      have hk2 : k ^ 2 = 1 := by
        rw [← hkord]
        exact pow_orderOf_eq_one k
      refine ⟨hk2, ?_⟩
      have hpk2 : (π₁ k) ^ 2 = 1 := by rw [← map_pow, hk2, map_one]
      have hpk1 : π₁ k ≠ 1 := by
        intro h
        exact hk1 (hpinj (by rw [h, map_one]))
      have hpd3 : (π₁ d) ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
      have hpd1 : π₁ d ≠ 1 := (hno d hd).1
      have hgl := s16h_e3_gl2_inv (π₁ k) (π₁ d) hpk2 hpk1 hpd3 hpd1
      have hkdk2 : k * d * k⁻¹ = d ^ 2 := by
        apply hpinj
        simpa [map_mul, map_inv, map_pow] using hgl
      have hd2 : d ^ 2 = d⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, show (2 : ℕ) + 1 = 3 by norm_num, hd3]
      have hkdk : k * d * k⁻¹ = d⁻¹ := by rw [hkdk2, hd2]
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← conj_zpow, hkdk, inv_zpow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
