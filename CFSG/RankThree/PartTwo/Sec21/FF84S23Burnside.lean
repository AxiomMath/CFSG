module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG

private theorem orderOf_eq_three_of_mem {H : Type} [Group H] [Finite H] (Q : Subgroup H)
    (hQ3 : Nat.card Q = 3) {x : H} (hxQ : x ∈ Q) (hx1 : x ≠ 1) : orderOf x = 3 := by
  have hdvd : orderOf x ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard Q hxQ
    rwa [hQ3] at h
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  exact ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne1

private theorem zpowers_eq_of_card_three {H : Type} [Group H] [Finite H] (Q : Subgroup H)
    (hQ3 : Nat.card Q = 3) {x : H} (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = Q := by
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxQ)
  simp [Nat.card_zpowers, orderOf_eq_three_of_mem Q hQ3 hxQ hx1, hQ3]

private theorem inverts_of_card_three {H : Type} [Group H] [Finite H] (Q : Subgroup H)
    (hQ3 : Nat.card Q = 3) {g x : H} (hxQ : x ∈ Q) (hx1 : x ≠ 1)
    (hgx : g * x * g⁻¹ ∈ Q) (hne : g * x * g⁻¹ ≠ x) :
    ∀ q ∈ Q, g * q * g⁻¹ = q⁻¹ := by
  have hord : orderOf x = 3 := orderOf_eq_three_of_mem Q hQ3 hxQ hx1
  have hZ : Subgroup.zpowers x = Q := zpowers_eq_of_card_three Q hQ3 hxQ hx1
  have hx3 : x ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one x
  have hx2 : x ^ 2 * x = 1 := by
    rw [← pow_succ]
    exact hx3
  have hconj : ∀ m : ℤ, g * x ^ m * g⁻¹ = (g * x * g⁻¹) ^ m := fun m =>
    map_zpow (MulAut.conj g) x m
  have hmem : g * x * g⁻¹ ∈ Subgroup.zpowers x := by
    rw [hZ]
    exact hgx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hsplit : x ^ k = x ^ (k % 3) := by
    have h3 : x ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact hx3
    have hk3 : k = k % 3 + 3 * (k / 3) := by omega
    conv_lhs => rw [hk3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hy : g * x * g⁻¹ = x⁻¹ := by
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
    · exfalso
      apply hx1
      have hxk : x ^ k = 1 := by rw [hsplit, h0, zpow_zero]
      have h1' : g * x * g⁻¹ = 1 := hk.symm.trans hxk
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1']; simp
    · exfalso
      have hxk : x ^ k = x := by rw [hsplit, h1, zpow_one]
      exact hne (hk.symm.trans hxk)
    · have h2' : k % 3 = ((2 : ℕ) : ℤ) := by push_cast; omega
      have hxk : x ^ k = x⁻¹ := by
        rw [hsplit, h2', zpow_natCast]
        exact eq_inv_of_mul_eq_one_left hx2
      exact hk.symm.trans hxk
  intro q hq
  have hmemq : q ∈ Subgroup.zpowers x := by
    rw [hZ]
    exact hq
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmemq
  rw [hconj m, hy, inv_zpow]

theorem exists_inverting_of_simple {H : Type} [Group H] [Finite H] (C Q : Subgroup H)
    (hC : IsSimpleGroup C) (hnab : ∃ a b : C, a * b ≠ b * a) (hQC : Q ≤ C) (hQ3 : Nat.card Q = 3)
    (hidx : ¬ 3 ∣ Q.relIndex C) :
    ∃ n ∈ C, ∀ q ∈ Q, n * q * n⁻¹ = q⁻¹ := by
  by_contra hno
  have hPcard : Nat.card (Q.subgroupOf C) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv, hQ3]
  have hPp : IsPGroup 3 (Q.subgroupOf C) := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  obtain ⟨S, hSc⟩ : ∃ S : Sylow 3 ↥C, (S : Subgroup ↥C) = Q.subgroupOf C :=
    ⟨hPp.toSylow hidx, IsPGroup.toSylow_coe _ _⟩
  have hS : (S : Subgroup ↥C) ≤ CFSG.centerIn (G := ↥C) (Subgroup.normalizer (S : Subgroup ↥C)) := by
    intro x hx
    rw [hSc] at hx ⊢
    rw [CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨Subgroup.le_normalizer hx, ?_⟩
    intro h hh
    by_contra hcomm
    apply hno
    have hh' : h ∈ Subgroup.normalizer (Q.subgroupOf C) := hh
    have hxQ : (x : H) ∈ Q := Subgroup.mem_subgroupOf.mp hx
    have hx1 : (x : H) ≠ 1 := by
      intro h1
      apply hcomm
      have hx' : x = 1 := Subtype.ext (by simpa using h1)
      rw [hx', mul_one, one_mul]
    have hgQ : (h : H) * (x : H) * (h : H)⁻¹ ∈ Q := by
      have h1 : h * x * h⁻¹ ∈ Q.subgroupOf C := (Subgroup.mem_normalizer_iff.mp hh' x).mp hx
      simpa using Subgroup.mem_subgroupOf.mp h1
    have hne : (h : H) * (x : H) * (h : H)⁻¹ ≠ (x : H) := by
      intro heq
      apply hcomm
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact mul_inv_eq_iff_eq_mul.mp heq
    exact ⟨(h : H), h.2, inverts_of_card_three Q hQ3 hxQ hx1 hgQ hne⟩
  obtain ⟨N, hN, hcop, hquot⟩ :=
    CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer
      (G := ↥C) 3 S hS
  rcases hC.eq_bot_or_eq_top_of_normal N with hN1 | hNtop
  ·
    subst hN1
    have hC3 : IsPGroup 3 ↥C := hquot.of_equiv QuotientGroup.quotientBot
    have hnt : Nontrivial ↥C := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have hcen : Subgroup.center ↥C ≠ ⊥ := hC3.bot_lt_center.ne'
    rcases hC.eq_bot_or_eq_top_of_normal (Subgroup.center ↥C) with hz | hz
    · exact hcen hz
    · obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center ↥C := by
        rw [hz]
        exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  ·
    subst hNtop
    rw [Subgroup.card_top] at hcop
    have h3dvd : 3 ∣ Nat.card ↥C := by
      have h := Subgroup.card_subgroup_dvd_card (Q.subgroupOf C)
      rwa [hPcard] at h
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) dvd_rfl h3dvd hcop

end CFSG.RankThree.PartTwo.Sec21.FF84
