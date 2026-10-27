module

public import CFSG.RankThree.PartOne.Mult.PPart
public import CFSG.RankThree.LocalRank.AlternatingCentralExtension

public section

namespace CFSG.RankThree.PartOne.Mult

open Subgroup

theorem alternating_center_small_primes {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    {n : ℕ} (hn : 5 ≤ n) (e : K ⧸ center K ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : ¬ p ∣ Nat.card (center K) := by
  intro hpZ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hNn, π, hperf, -, hsurj, hker, hpg, hne⟩ := exists_central_p_extension (K := K) hpZ
  have : Group.IsPerfect (K ⧸ N) := hperf
  have hker' : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have h := LocalRank.perfect_central_prime_extension_alternating_ker_eq_bot
    (e.toMonoidHom.comp π) hn hp hp3 (e.surjective.comp hsurj) (hker' ▸ hker) (hker' ▸ hpg)
  exact hne (hker' ▸ h)

end CFSG.RankThree.PartOne.Mult
