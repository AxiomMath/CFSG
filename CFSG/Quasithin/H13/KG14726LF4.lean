module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.Quasithin.Vol2.RootDataF4

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

theorem five_dvd_card_suzuki (a : ℕ) :
    5 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  refine Dvd.dvd.mul_left ?_ _
  have h4 : (2 ^ (2 * a + 1)) ^ 2 = 4 ^ (2 * a + 1) := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h := Odd.nat_add_dvd_pow_add_pow 4 1 (show Odd (2 * a + 1) from odd_two_mul_add_one a)
  rw [one_pow] at h
  rw [h4]
  exact h

theorem exists_orderOf_five_commute_centralZ
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    ∃ ℓ ∈ F4.reeGamma K a, ℓ * centralZ K a c = centralZ K a c * ℓ ∧ orderOf ℓ = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥(rankOneGroupTwo K a)) 5
    (by rw [card_rankOneGroupTwo ha hK]; exact five_dvd_card_suzuki a)
  refine ⟨r, rankOneGroupTwo_le_reeGamma hK r.2,
    mem_centralizer_singleton_iff.mp (rankOneGroupTwo_le_centralizer ha hK c r.2), ?_⟩
  rw [Subgroup.orderOf_coe, hr]

theorem kg115F4Input_holds :
    KG115F4Input := by
  intro f X _ _ _ h
  obtain ⟨a, K, _, _, _, ha, rfl, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model h
  refine kg115Excluded_of_mulEquiv e ?_
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : center ↥(F4.reeGamma K a) = ⊥ := large_Ree_fixed_group_center_trivial a K hK
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨P₀, hP₀⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hS₀ : IsPGroup 2 ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) := by
    rw [← hP₀]
    exact P₀.isPGroup'
  have hS₀i : ¬ 2 ∣ ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).index := by
    rw [← hP₀]
    exact P₀.not_dvd_index
  have hcU : ∀ y : ↥(F4.reeGamma K a),
      (∀ s ∈ (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a), s * y = y * s) →
      ∀ z ∈ F4.reeFixedPosUnipotent K a, z * (y : ModGL F4.tag K) = y * z := by
    intro y hy z hz
    have := hy ⟨z, reeFixedPosUnipotent_le_reeGamma hz⟩ (mem_subgroupOf.mpr hz)
    exact congrArg Subtype.val this
  refine kg115Excluded_of_at hc (sylowTwoNoThree_of_conj hS₀ hS₀i fun y hy3 hyS => ?_) ?_
  · have h1 := RootData.F4.eq_one_of_centralizer_of_odd ha hK y.2 (hcU y hyS)
      (by rw [Subgroup.orderOf_coe, hy3]; decide)
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  · intro S hS hSi l hl hlc hl1
    refine kg115At_of_prime (forall_center_of_conj hS₀ hS₀i
      (Q := fun u => ∃ ℓ : ↥(F4.reeGamma K a), ℓ * u = u * ℓ ∧
        ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) (fun g _ hu => prime_conj g hu) ?_
      S hS hSi l hl hlc hl1)
    intro u hu huc _
    have huU : (u : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a := mem_subgroupOf.mp hu
    have huZ : (u : ModGL F4.tag K) ∈ ((center (F4.reeFixedPosUnipotent K a)).map
        (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) := by
      refine ⟨⟨u, huU⟩, mem_center_iff.mpr fun s => Subtype.ext ?_, rfl⟩
      have h1 := hcU u huc s s.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact h1
    rw [coe_center_eq_range_centralZ ha hK] at huZ
    obtain ⟨c, hcu⟩ := huZ
    obtain ⟨ℓ, hℓΓ, hℓc, hℓ5⟩ := exists_orderOf_five_commute_centralZ ha hK c
    refine ⟨⟨ℓ, hℓΓ⟩, Subtype.ext ?_, 5, by norm_num, le_rfl, by rw [Subgroup.orderOf_mk, hℓ5]⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hcu]
    exact hℓc

end CFSG.Quasithin.H13.KG14726

end
