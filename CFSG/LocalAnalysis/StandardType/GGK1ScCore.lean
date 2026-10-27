module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggCenterPrime_of_coprime_card_ker {H R : Type} [Group H] [Group R] [Finite H]
    {q : H →* R} (hq : Function.Surjective q) (hZ : Subgroup.center R = ⊥)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime (Nat.card q.ker) p) :
    GGCenterPrime p R := by
  classical
  have := Fact.mk hp
  have hnp : ∀ z ∈ q.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have h1 : orderOf z ∣ Nat.card q.ker := Subgroup.orderOf_dvd_natCard _ hz
    have h2 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have h3 : orderOf z = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop.symm h2 h1
    rwa [orderOf_eq_one_iff] at h3
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnt := StdSubRestU.noTorsion_ker_of_section (q := q) hq hsplit hp hp2 hnp hψ hker hperf
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    have h1 : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 l]
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  have hzp : (z : L') ^ p = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz] at h
    exact congrArg Subtype.val h
  have h1 : z = 1 := Subtype.ext (hnt _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

end CFSG.StandardType

end
