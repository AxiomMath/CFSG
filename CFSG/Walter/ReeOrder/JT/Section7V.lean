module

public import CFSG.Walter.ReeOrder.JT.Section7U

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

theorem dvd_of_dvd_three_pow_sub_one {f n : ℕ} (hf : 2 ≤ f) (h : (3 ^ f - 1) / 2 ∣ 3 ^ n - 1) :
    f ∣ n := by
  set d := (3 ^ f - 1) / 2 with hd
  have h3f : 3 ^ f = 2 * d + 1 := by
    have hodd : 3 ^ f % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    have : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hmod : 3 ^ f ≡ 1 [MOD d] := by
    rw [h3f, Nat.ModEq, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
  have hn1 : 3 ^ n ≡ 1 [MOD d] :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr h |>.symm
  have hsplit : 3 ^ n = (3 ^ f) ^ (n / f) * 3 ^ (n % f) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hr : 3 ^ (n % f) ≡ 1 [MOD d] := by
    have h1 : (3 ^ f) ^ (n / f) * 3 ^ (n % f) ≡ 1 ^ (n / f) * 3 ^ (n % f) [MOD d] :=
      (hmod.pow _).mul_right _
    rw [one_pow, one_mul, ← hsplit] at h1
    exact h1.symm.trans hn1
  by_contra hfn
  have hr0 : n % f ≠ 0 := fun h0 => hfn (Nat.dvd_of_mod_eq_zero h0)
  have hrf : n % f < f := Nat.mod_lt _ (by omega)
  have hlt : 3 ^ (n % f) < d + 1 := by
    have h1 : 3 ^ (n % f) ≤ 3 ^ (f - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 ^ f = 3 * 3 ^ (f - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hgt : 1 < 3 ^ (n % f) := Nat.one_lt_pow hr0 (by norm_num)
  have hdvd : d ∣ 3 ^ (n % f) - 1 := (Nat.modEq_iff_dvd' hgt.le).mp hr.symm
  have := Nat.le_of_dvd (by omega) hdvd
  omega

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem lemma_7_11_b
    (c : TorusConf h) (P : Sylow 3 G) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card (P : Subgroup G) = h.q ^ m := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀, hCP₀, -, R, hRP₀, -, hRq⟩ := h.lemma_7_11_a hp3 c
  have hcard : Nat.card (P : Subgroup G) = Nat.card (P₀ : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  let := conjAct c.C P₀ hCP₀
  have : Fintype c.C := Fintype.ofFinite _
  have : Fintype (P₀ : Subgroup G) := Fintype.ofFinite _
  have hfix : ∀ g : c.C, g ≠ 1 → ∀ y : (P₀ : Subgroup G), g • y = y → y = 1 := by
    intro g hg y hy
    have hy' : (g : G) * y * (g : G)⁻¹ = y := congrArg Subtype.val hy
    have hyC : (y : G) ∈ Subgroup.centralizer ({(g : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * g = ((g : G) * y * (g : G)⁻¹) * g := by rw [hy']
        _ = g * y := by group
    have h74 := h.lemma_7_4 hp3 c.torus.le c.torus.cyclic c.card_C g.2
      (fun h0 => hg (Subtype.ext h0))
    have h1 := Subgroup.orderOf_dvd_natCard _ hyC
    obtain ⟨k, hk⟩ := P₀.isPGroup' y
    have h2 : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [← Subgroup.orderOf_coe] at h2
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (Subgroup.centralizer ({(g : G)} : Set G))) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h74)
    exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1))
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group c.C
    (P₀ : Subgroup G)
  have hsum : (∑ g : c.C, Fintype.card (MulAction.fixedBy (P₀ : Subgroup G) g)) =
      Fintype.card (P₀ : Subgroup G) + (Fintype.card c.C - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
    have h1 : Fintype.card (MulAction.fixedBy (P₀ : Subgroup G) (1 : c.C)) =
        Fintype.card (P₀ : Subgroup G) :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv (fun y => by
        rw [MulAction.mem_fixedBy, one_smul]))
    have h2 : ∀ g ∈ Finset.univ.erase (1 : c.C),
        Fintype.card (MulAction.fixedBy (P₀ : Subgroup G) g) = 1 := by
      intro g hg
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, smul_one g⟩, ?_⟩
      rintro ⟨y, hy⟩
      exact Subtype.ext (hfix g (Finset.ne_of_mem_erase hg) y hy)
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, mul_one]
  rw [hsum] at hburn
  have hC1 : 1 ≤ Fintype.card c.C := Fintype.card_pos
  have hdvd : Fintype.card c.C ∣ Fintype.card (P₀ : Subgroup G) - 1 := by
    have h1 : Fintype.card c.C ∣ Fintype.card (P₀ : Subgroup G) + (Fintype.card c.C - 1) :=
      ⟨_, by rw [hburn, mul_comm]⟩
    have h2 : Fintype.card (P₀ : Subgroup G) + (Fintype.card c.C - 1) =
        (Fintype.card (P₀ : Subgroup G) - 1) + Fintype.card c.C := by
      have : 1 ≤ Fintype.card (P₀ : Subgroup G) := Fintype.card_pos
      omega
    rw [h2] at h1
    exact (Nat.dvd_add_left (dvd_refl _)).mp h1
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hdvd
  obtain ⟨n, hn⟩ := P₀.isPGroup'.exists_card_eq
  have hqpow : h.q = 3 ^ h.f := by rw [JTHyp.q_eq, hp3]
  have hCcard : Nat.card c.C = (3 ^ h.f - 1) / 2 := by
    have := c.card_C
    rw [hqpow] at this
    omega
  have hf2 : 2 ≤ h.f := by
    have := h.five_lt
    rw [hp3] at this
    by_contra hf
    interval_cases hf' : h.f <;> norm_num at this
  rw [hCcard, hn] at hdvd
  obtain ⟨m, rfl⟩ := dvd_of_dvd_three_pow_sub_one hf2 hdvd
  refine ⟨m, ?_, by rw [hcard, hn, hqpow, pow_mul]⟩
  by_contra hm
  have hm0 : m = 0 := by omega
  rw [hm0, mul_zero, pow_zero] at hn
  have := Subgroup.card_le_of_le hRP₀
  rw [hn, hRq] at this
  have := h.five_lt
  rw [← JTHyp.q_eq] at this
  omega

end JTHyp

end CFSG.Walter.JT
