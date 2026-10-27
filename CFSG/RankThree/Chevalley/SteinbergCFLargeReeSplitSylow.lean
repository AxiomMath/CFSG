module

public import CFSG.RankThree.SteinbergR3ELargeReeOrder

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.RankThree.LargeReeOrder
open scoped Pointwise

theorem not_dvd_cofactor {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : 1 ≤ q) (hpq : p ∣ q - 1) :
    ¬ p ∣ q ^ 12 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : (q : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (q - 1) p).2 hpq
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
    exact h
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub hq2, Nat.cast_sub hq4]
  rw [hq1]
  norm_num
  intro h
  have h16 : ((16 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff, show (16 : ℕ) = 2 ^ 4 by norm_num] at h16
  have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h16)
  omega

theorem factorization_card_reeGamma_eq {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ 2 ^ (2 * a + 1) - 1) :
    (Nat.card (F4.reeGamma K a)).factorization p =
      (Nat.card (F4.reeFixedTorus K a)).factorization p := by
  rw [(large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1, card_reeFixedTorus hK,
    hK]
  set q := 2 ^ (2 * a + 1) with hqdef
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set R := q ^ 12 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)
    with hR
  have hsplit : q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1) = (q - 1) ^ 2 * R := by
    rw [hR]
    ring
  have hR0 : R ≠ 0 := by
    intro h
    apply not_dvd_cofactor hp hp3 (by omega) hpq
    rw [← hR, h]
    exact dvd_zero p
  have hq10 : (q - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  rw [hsplit, Nat.factorization_mul hq10 hR0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_cofactor hp hp3 (by omega) hpq), add_zero]

theorem large_Ree_split_torus_contains_Sylow_prime_subgroups (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ 2 ^ (2 * a + 1) - 1) :
    (Nat.card (F4.reeGamma K a)).factorization p =
        (Nat.card (F4.reeFixedTorus K a)).factorization p ∧
      (∀ P : Sylow p (F4.reeFixedTorus K a), ∃ Q : Sylow p (F4.reeGamma K a),
        (Q : Subgroup (F4.reeGamma K a)).map (F4.reeGamma K a).subtype =
          (P : Subgroup (F4.reeFixedTorus K a)).map (F4.reeFixedTorus K a).subtype) ∧
      ∀ R : Subgroup (ModGL F4.tag K), R ≤ F4.reeGamma K a → IsPGroup p R →
        ∃ g ∈ F4.reeGamma K a, R.map (MulAut.conj g).toMonoidHom ≤ F4.reeFixedTorus K a := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  set Γ := F4.reeGamma K a with hΓ
  set H₀ := F4.reeFixedTorus K a with hH₀
  have hH₀Γ : H₀ ≤ Γ := inf_le_right
  have hfact := factorization_card_reeGamma_eq hK hp hp3 hpq
  have hsyl : ∀ P : Sylow p H₀, ∃ Q : Sylow p Γ,
      (Q : Subgroup Γ).map Γ.subtype = (P : Subgroup H₀).map H₀.subtype := by
    intro P
    set P' := (P : Subgroup H₀).map H₀.subtype with hP'
    have hP'Γ : P' ≤ Γ := (Subgroup.map_subtype_le _).trans hH₀Γ
    have hcard : Nat.card (P'.subgroupOf Γ) = p ^ (Nat.card Γ).factorization p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'Γ).toEquiv, hP',
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Sylow.card_eq_multiplicity,
        hfact]
    refine ⟨Sylow.ofCard _ hcard, ?_⟩
    rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_of_le_left hP'Γ]
  refine ⟨hfact, hsyl, fun R hRΓ hR => ?_⟩
  obtain ⟨P⟩ : Nonempty (Sylow p H₀) := inferInstance
  obtain ⟨Q, hQ⟩ := hsyl P
  have hRp : IsPGroup p (R.subgroupOf Γ) :=
    hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRΓ).symm
  obtain ⟨S, hS⟩ := hRp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q S
  refine ⟨(g : ModGL F4.tag K)⁻¹, Γ.inv_mem g.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxS : (⟨x, hRΓ hx⟩ : Γ) ∈ (S : Subgroup Γ) := hS (Subgroup.mem_subgroupOf.2 hx)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
  have hmem : (g⁻¹ * ⟨x, hRΓ hx⟩ * g : Γ) ∈ (Q : Subgroup Γ) := by
    simpa using hxS
  have himg : ((g⁻¹ * ⟨x, hRΓ hx⟩ * g : Γ) : ModGL F4.tag K) ∈
      (P : Subgroup H₀).map H₀.subtype := by
    rw [← hQ]
    exact ⟨_, hmem, rfl⟩
  have hH : ((g⁻¹ * ⟨x, hRΓ hx⟩ * g : Γ) : ModGL F4.tag K) ∈ H₀ :=
    Subgroup.map_subtype_le _ himg
  simpa [MulAut.conj_apply, mul_assoc] using hH

end CFSG.RankThree.Chevalley
