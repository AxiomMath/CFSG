module

public import CFSG.RankThree.PartOne.Mult.Sporadic

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.SectionRank CFSG.Blueprint CFSG.RankThree.PartOne.Mult
open scoped commutatorElement

section Kernel

variable {E G : Type*} [Group E] [Group G] {p : ℕ} [Fact p.Prime]

theorem ker_eq_bot_of_isPGroup_of_sylow [Finite E] (π : E →* G) (hpg : IsPGroup p π.ker)
    (h : ∀ Cp : Sylow p π.ker, (Cp : Subgroup π.ker) = ⊥) : π.ker = ⊥ := by
  refine OddCover.eq_bot_of_forall_sylow_eq_bot _ fun r hr _ P => ?_
  by_cases hrp : r = p
  · subst hrp
    exact h P
  · obtain ⟨n, hn⟩ := hpg.exists_card_eq
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hdvd : Nat.card (P : Subgroup π.ker) ∣ Nat.card π.ker :=
      Subgroup.card_subgroup_dvd_card _
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    · exfalso
      rw [hk, hn] at hdvd
      exact hrp ((Nat.prime_dvd_prime_iff_eq hr Fact.out).1
        (hr.dvd_of_dvd_pow ((dvd_pow_self r hkpos.ne').trans hdvd)))

theorem kernelTrivial_of_sylow
    (h : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* G),
      Function.Surjective π → π.ker ≤ Subgroup.center E → ∀ Cp : Sylow p π.ker,
        (Cp : Subgroup π.ker) = ⊥) :
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* G),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup p π.ker → π.ker = ⊥ :=
  fun E _ _ _ π hπ hC hpg => ker_eq_bot_of_isPGroup_of_sylow π hpg (h E π hπ hC)

end Kernel

section Witness

variable {G : Type} [Group G] {p : ℕ}

theorem kernelTrivial_of_square (hp : p.Prime) [Finite G] {x y h : G} (hxp : x ^ p = 1)
    (hyp : y ^ p = 1) (hxy : x * y = y * x)
    (hQ : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 2) (hS : ¬ p ^ 3 ∣ Nat.card G)
    {a b c d : ℕ} (hx : h * x * h⁻¹ = x ^ a * y ^ c) (hy : h * y * h⁻¹ = x ^ b * y ^ d)
    (hdet : ((a * d - b * c : ℤ) : ZMod p) ≠ 1) :
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* G),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup p π.ker → π.ker = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  exact kernelTrivial_of_sylow fun E _ _ _ π hπ hC Cp =>
    sylow_kernel_eq_bot_of_square_witness π hπ hC hxp hyp hxy hQ hS hx hy hdet Cp

theorem kernelTrivial_of_cubic (hp : p.Prime) [Finite G] {x y h : G} (hxp : x ^ p = 1)
    (hyp : y ^ p = 1) (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hQ : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3) (hS : ¬ p ^ 4 ∣ Nat.card G)
    {a b c d k l μ : ℕ} (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l) (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
    (hdet : ((μ : ZMod p) * a - 1) * ((μ : ZMod p) * d - 1) - (μ : ZMod p) ^ 2 * b * c ≠ 0) :
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* G),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup p π.ker → π.ker = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  exact kernelTrivial_of_sylow fun E _ _ _ π hπ hC Cp =>
    OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hxp hyp hz1 hzx hzy hQ hS hhx hhy
      hhz hdet Cp

end Witness

theorem sporadicKernelTrivial_of_carrier {s : TauCeti.SporadicName} {p : ℕ}
    (h : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
      (π : E →* NativeSporadic.Carrier s), Function.Surjective π → π.ker ≤ Subgroup.center E →
        IsPGroup p π.ker → π.ker = ⊥) :
    SporadicKernelTrivial s p := by
  intro E _ _ _ S _ π hS hπ hC hpg
  obtain ⟨e⟩ := hS
  have hker : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  rw [← hker]
  exact h E _ (e.surjective.comp hπ) (hker ▸ hC) (hker ▸ hpg)

end CFSG.RankThree.PartOne.MultRes
