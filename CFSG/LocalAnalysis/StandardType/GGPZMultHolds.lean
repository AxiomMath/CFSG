module

public import CFSG.LocalAnalysis.StandardType.GGPZMultA
public import CFSG.LocalAnalysis.StandardType.GGPZMultTwA
public import CFSG.LocalAnalysis.StandardType.GGPZMultD4
public import CFSG.LocalAnalysis.StandardType.GGPZRankTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pzm_not_dvd_succ {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : p ∣ r + 3) :
    ¬ p ∣ r + 1 := by
  intro h1
  have h := Nat.dvd_sub h3 h1
  have hsub : r + 3 - (r + 1) = 2 := by omega
  rw [hsub] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

theorem ggPZMultInput_holds :
    GGPZMultInput := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z h
  obtain ⟨hH, -, hJΛ, -, hJl, -, hrow, -⟩ := h
  have hbeta : p ∈ LargeEvenBeta 4 G := hH.1.1.2.2.2.2.2.1
  have hp2 : p ≠ 2 := hbeta.2.1
  have hperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  obtain ⟨hrowTN, -⟩ := hrow
  obtain ⟨tag, rk, n⟩ := labJ
  rcases hrowTN with ⟨ht, hpq, hpl, -⟩ | ⟨ht, hpq, hpl, -⟩ | ⟨hJe, hp3, -, -⟩ | ⟨hJe, hp3, -, -⟩
  · dsimp only at ht hpq hpl hJΛ hJl
    subst ht
    exact ggPZMult_A hp2 hJΛ hperf hJl (pzm_not_dvd_succ (Fact.out : p.Prime) hp2 hpl)
  · dsimp only at ht hpq hpl hJΛ hJl
    subst ht
    exact ggPZMult_twA hp2 hJΛ hperf hJl hpq (pzm_not_dvd_succ (Fact.out : p.Prime) hp2 hpl)
  · obtain ⟨rfl, rfl, rfl⟩ := hJe
    subst hp3
    exact ggPZMult_D4 hJΛ hperf hJl
  · obtain ⟨rfl, rfl, rfl⟩ := hJe
    subst hp3
    exact ggPZMult_D4 hJΛ hperf hJl

end CFSG.StandardType

end
