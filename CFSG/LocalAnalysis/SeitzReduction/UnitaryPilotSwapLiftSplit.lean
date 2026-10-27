module

public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic

public section

open CFSG.Assembly.LowTwoRank

namespace CFSG.SeitzReduction.UnitaryPilot

theorem exists_section_statedSU_of_coprime
    {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) {m : ℕ} (hm : 2 ≤ m) (hmq : (m, p ^ f) ≠ (3, 2))
    {E : Type} [Group E] [Finite E] {π : E →* StatedSU m (p ^ f) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : Even m → p.Coprime (Nat.card π.ker)) :
    ∃ s : StatedSU m (p ^ f) F →* E, ∀ g, π (s g) = g := by
  by_cases he : Even m
  · set ψ := CFSG.LieType.Universal.Unitary.equivStatedSU hF m
    have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ ψ.symm.injective]
    obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_coprime hF
      he hm (π := ψ.symm.toMonoidHom.comp π) (ψ.symm.surjective.comp hπ) (hker ▸ hcen)
      (hker ▸ hC he)
    refine ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective ?_⟩
    exact hs (ψ.symm g)
  · have hm3 : 3 ≤ m := by
      rcases Nat.lt_or_ge m 3 with h | h
      · exact absurd ⟨1, by omega⟩ he
      · exact h
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · have h1 := Finite.one_lt_card (α := F)
        rw [hF, pow_zero, one_pow] at h1
        exact absurd h1 (lt_irrefl 1)
      · exact h
    exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central hF hf hm3
      he hmq hπ hcen

theorem oddCentralSplit_statedSU
    {F : Type} [Field F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hm : 2 ≤ m)
    (hmq : (m, 2 ^ f) ≠ (3, 2)) : OddCentralSplit (StatedSU m (2 ^ f) F) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul])
  intro E _ _ π hπ hcen hodd
  exact exists_section_statedSU_of_coprime hF hm hmq hπ hcen fun _ =>
    Nat.coprime_two_left.2 hodd

end CFSG.SeitzReduction.UnitaryPilot
