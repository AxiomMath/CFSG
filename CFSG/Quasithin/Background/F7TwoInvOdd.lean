module

public import CFSG.Quasithin.Background.F7TwoInvNonempty

public section

namespace CFSG.Quasithin.F7Two

variable {Γ : Type*} [Group Γ] {L : Subgroup Γ} {a : Γ}

theorem exists_sq_of_inverted {v : Γ} (hodd : Odd (orderOf v)) (hv : a * v * a⁻¹ = v⁻¹) :
    ∃ w ∈ Subgroup.zpowers v, w * w = v⁻¹ ∧ a * w * a⁻¹ = w⁻¹ := by
  obtain ⟨t, ht⟩ := hodd
  have hvt : v ^ (2 * t + 1) = 1 := ht ▸ pow_orderOf_eq_one v
  refine ⟨(v⁻¹) ^ (t + 1), Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers v)) _,
    ?_, ?_⟩
  · have h1 : (v⁻¹) ^ (2 * t + 1) = 1 := by rw [inv_pow, hvt, inv_one]
    calc (v⁻¹) ^ (t + 1) * (v⁻¹) ^ (t + 1) = (v⁻¹) ^ (2 * t + 1) * v⁻¹ := by
          rw [← pow_add, show t + 1 + (t + 1) = (2 * t + 1) + 1 by ring, pow_succ]
      _ = v⁻¹ := by rw [h1, one_mul]
  · rw [← conj_pow, show a * v⁻¹ * a⁻¹ = (a * v * a⁻¹)⁻¹ by group, hv, inv_inv, inv_pow,
      inv_inv]

theorem exists_mul_inverted_of_odd (ha2 : a * a = 1) {U : Subgroup Γ} (hU : Odd (Nat.card U))
    (haU : ∀ x ∈ U, a * x * a⁻¹ ∈ U) {u : Γ} (hu : u ∈ U) :
    ∃ c ∈ U, ∃ w ∈ U, a * c = c * a ∧ Odd (orderOf w) ∧ a * w * a⁻¹ = w⁻¹ ∧ u = c * w := by
  have hai : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, ha2, inv_one]
  set v : Γ := u⁻¹ * (a * u * a⁻¹) with hvdef
  have hvU : v ∈ U := U.mul_mem (U.inv_mem hu) (haU u hu)
  have hv : a * v * a⁻¹ = v⁻¹ := by
    calc a * v * a⁻¹ = (a * u⁻¹ * a⁻¹) * ((a * a) * u * (a⁻¹ * a⁻¹)) := by rw [hvdef]; group
      _ = v⁻¹ := by rw [ha2, hai, hvdef]; group
  have hvodd : Odd (orderOf v) := hU.of_dvd_nat (Subgroup.orderOf_dvd_natCard U hvU)
  obtain ⟨w, hwv, hww, haw⟩ := exists_sq_of_inverted hvodd hv
  have hwU : w ∈ U := (Subgroup.zpowers_le.mpr hvU) hwv
  refine ⟨u * w⁻¹, U.mul_mem hu (U.inv_mem hwU), w, hwU, ?_, ?_, haw, by group⟩
  · have hu' : a * u * a⁻¹ = u * v := by rw [hvdef]; group
    have hwi : a * w⁻¹ * a⁻¹ = w := by
      rw [show a * w⁻¹ * a⁻¹ = (a * w * a⁻¹)⁻¹ by group, haw, inv_inv]
    have hvw : v = (w * w)⁻¹ := by rw [hww, inv_inv]
    calc a * (u * w⁻¹) = (a * u * a⁻¹) * (a * w⁻¹ * a⁻¹) * a := by group
      _ = u * w⁻¹ * a := by rw [hu', hwi, hvw]; group
  · exact hU.of_dvd_nat (Subgroup.orderOf_dvd_natCard U hwU)

theorem le_closure_invXi_of_odd (hne : (invXi L a).Nonempty) (ha2 : a * a = 1)
    {U : Subgroup Γ} (hUL : U ≤ L) (hU : Odd (Nat.card U)) (haU : ∀ x ∈ U, a * x * a⁻¹ ∈ U) :
    U ≤ Subgroup.closure (invXi L a) := by
  intro u hu
  obtain ⟨c, hcU, w, hwU, hac, hwodd, hwinv, rfl⟩ := exists_mul_inverted_of_odd ha2 hU haU hu
  have hcc : c ∈ L ⊓ Subgroup.centralizer {a} :=
    ⟨hUL hcU, Subgroup.mem_centralizer_singleton_iff.mpr hac.symm⟩
  exact Subgroup.mul_mem _ (centralizer_le_closure_invXi hne hcc)
    (mem_closure_invXi_of_inverted (hUL hwU) hwodd hwinv)

theorem invGen_of_odd_iSup [Finite Γ] {ι : Sort*} (hsimple : IsSimpleGroup ↥L)
    (hnonab : ∃ x y : ↥L, x * y ≠ y * x) (ha2 : a * a = 1)
    (haL : ∀ x ∈ L, a * x * a⁻¹ ∈ L) (hac : ∃ x ∈ L, a * x ≠ x * a) {U : ι → Subgroup Γ}
    (hUL : ∀ i, U i ≤ L) (hodd : ∀ i, Odd (Nat.card (U i)))
    (haU : ∀ i, ∀ x ∈ U i, a * x * a⁻¹ ∈ U i) (hsup : ⨆ i, U i = L) : InvGen L a := by
  have hne := invXi_nonempty hsimple hnonab ha2 haL hac
  refine le_antisymm closure_invXi_le ?_
  calc L = ⨆ i, U i := hsup.symm
    _ ≤ _ := iSup_le fun i => le_closure_invXi_of_odd hne ha2 (hUL i) (hodd i) (haU i)

theorem odd_natCard_of_isPGroup [Finite Γ] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {U : Subgroup Γ}
    (hU : IsPGroup p U) : Odd (Nat.card U) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU
  rw [hn]
  exact (Fact.out (p := p.Prime)).odd_of_ne_two hp |>.pow

end CFSG.Quasithin.F7Two
