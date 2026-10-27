module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

theorem exists_normal_three_le_of_quasisimple {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    [hH : H.Normal] (hQ : CFSG.IsQuasisimple ↥H) (hZ : Nat.card ↥(Subgroup.center ↥H) = 3)
    (hC : Nat.card ↥(Subgroup.centralizer (H : Set G)) ∣ 3) :
    ∃ Z : Subgroup G, Z.Normal ∧ Nat.card ↥Z = 3 ∧
      ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → Z ≤ N := by
  classical
  set C : Subgroup G := Subgroup.centralizer (H : Set G) with hCdef
  set Zc : Subgroup G := (Subgroup.center ↥H).map H.subtype with hZc
  have hZcCard : Nat.card ↥Zc = 3 := by
    rw [← hZ, hZc]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).toEquiv).symm
  have hZcC : Zc ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro g hg
    have := (Subgroup.mem_center_iff.1 hz) ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hCcard : Nat.card ↥C = 3 := by
    have h1 : 3 ∣ Nat.card ↥C := hZcCard ▸ Subgroup.card_dvd_of_le hZcC
    exact Nat.dvd_antisymm hC h1
  have hZeqC : Zc = C := Subgroup.eq_of_le_of_card_ge hZcC (by omega)
  have hCnormal : C.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hCdef, Subgroup.mem_centralizer_iff] at hn ⊢
    intro h hh
    have h1 : g⁻¹ * h * g ∈ H := by simpa [mul_assoc] using hH.conj_mem h hh g⁻¹
    have h2 := hn _ h1
    calc h * (g * n * g⁻¹) = g * ((g⁻¹ * h * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * h * g)) * g⁻¹ := by rw [h2]
      _ = (g * n * g⁻¹) * h := by group
  refine ⟨Zc, hZeqC ▸ hCnormal, hZcCard, fun N hN hN1 => ?_⟩
  by_cases hM : N ⊓ H = ⊥
  ·
    have hNC : N ≤ C := by
      intro n hn
      rw [hCdef, Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 : n * h * n⁻¹ * h⁻¹ ∈ N ⊓ H := by
        refine ⟨?_, ?_⟩
        · have := N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) h)
          simpa [mul_assoc] using this
        · exact H.mul_mem (hH.conj_mem h hh n) (H.inv_mem hh)
      rw [hM, Subgroup.mem_bot] at h1
      have h2 : n * h = h * n := by
        have := congrArg (· * (h * n)) h1
        simpa [mul_assoc] using this
      exact h2.symm
    have hNcard : Nat.card ↥N ∣ 3 := hCcard ▸ Subgroup.card_dvd_of_le hNC
    have hN1' : Nat.card ↥N ≠ 1 := fun h => hN1 (Subgroup.card_eq_one.1 h)
    have hN3 : Nat.card ↥N = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hNcard with h | h
      · exact absurd h hN1'
      · exact h
    have hNeq : N = C := Subgroup.eq_of_le_of_card_ge hNC (by omega)
    rw [hZeqC, hNeq]
  ·
    have hM0 : (N.subgroupOf H).Normal := hN.subgroupOf H
    have hdich := CFSG.LocalCores.quasisimple_normal_subgroups hQ hM0
    suffices hcen : ∀ z ∈ Subgroup.center ↥H, (z : G) ∈ N by
      rintro _ ⟨z, hz, rfl⟩
      exact hcen z hz
    rcases hdich with htop | hle
    · intro z _
      have : (⟨(z : G), z.2⟩ : ↥H) ∈ N.subgroupOf H := by rw [htop]; exact Subgroup.mem_top _
      exact this
    · obtain ⟨⟨m, hmNH⟩, hm1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hM
      obtain ⟨hmN, hmH⟩ := hmNH
      have hm1 : m ≠ 1 := fun h => hm1' (Subtype.ext h)
      have hmM : (⟨m, hmH⟩ : ↥H) ∈ N.subgroupOf H := hmN
      have hM1 : N.subgroupOf H ≠ ⊥ := by
        intro h
        rw [h, Subgroup.mem_bot] at hmM
        exact hm1 (congrArg Subtype.val hmM)
      have hMcard : Nat.card ↥(N.subgroupOf H) ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le hle
      have hM1' : Nat.card ↥(N.subgroupOf H) ≠ 1 := fun h => hM1 (Subgroup.card_eq_one.1 h)
      have hM3 : Nat.card ↥(N.subgroupOf H) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hMcard with h | h
        · exact absurd h hM1'
        · exact h
      have hMeq : N.subgroupOf H = Subgroup.center ↥H :=
        Subgroup.eq_of_le_of_card_ge hle (by omega)
      intro z hz
      have : z ∈ N.subgroupOf H := by rw [hMeq]; exact hz
      exact this

end SzG11S

end G11

end CFSG.Quasithin
