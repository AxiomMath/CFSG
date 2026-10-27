module

public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeOuterPrimeSupport

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Ree
open CFSG.ComponentClassification.CatalogueBSmallRee (Sylow_scalar_Frattini_outer_prime_support)

theorem Sylow_scalar_Frattini_coprime_automorphism_subgroups_cyclic {G Ω : Type*} [Group G]
    [Finite G] [MulAction G Ω] [Finite Ω] [MulAction.IsPretransitive G Ω] [FaithfulSMul G Ω]
    (hΩ : 3 ≤ Nat.card Ω) (ξ : Ω) {ℓ : ℕ} [Fact ℓ.Prime] (U : Sylow ℓ G)
    (hUξ : (U : Subgroup G) ≤ MulAction.stabilizer G ξ)
    (hUn : ((U : Subgroup G).subgroupOf (MulAction.stabilizer G ξ)).Normal)
    (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (U : Subgroup G), (u : G) • ω = ω')
    (w : G) (hw : w • ξ ≠ ξ) {n : ℕ} (hn : 1 ≤ n) {K : Type*} [Field K]
    (hK : Nat.card K = ℓ ^ n)
    (e : Additive ((U : Subgroup G) ⧸ frattini (U : Subgroup G)) ≃+ K)
    (hT : (((Subgroup.normalizer (((U : Subgroup G).map (MulAut.conj w).toMonoidHom :
        Subgroup G) : Set G)).subgroupOf (Subgroup.normalizer ((U : Subgroup G) : Set G))).map
          (U : Subgroup G).normalizerMonoidHom).map (frattiniScalarRep e) = scalarAddAut K)
    {p : ℕ} (hp : p.Prime) (hpG : ¬ p ∣ Nat.card G) :
    ∀ P : Subgroup (MulAut G), IsPGroup p P → IsCyclic P := by
  intro P hP
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨⟨R, hRn, hRp, hRcyc, -⟩, -⟩ :=
    Sylow_scalar_Frattini_outer_prime_support hΩ ξ U hUξ hUn htr w hw hn hK e hT
  have hℓG : ℓ ∣ Nat.card G := by
    have h1 : Nat.card ((U : Subgroup G) ⧸ frattini (U : Subgroup G)) = ℓ ^ n := by
      rw [← hK]
      exact Nat.card_congr (Additive.toMul.symm.trans e.toEquiv)
    have h2 := Subgroup.card_quotient_dvd_card (frattini (U : Subgroup G))
    rw [h1] at h2
    exact (dvd_pow_self ℓ (by omega)).trans
      (h2.trans (Subgroup.card_subgroup_dvd_card (U : Subgroup G)))
  have hpℓ : p ≠ ℓ := fun h => hpG (h ▸ hℓG)
  have hRcop : Nat.Coprime (Nat.card R) p := by
    obtain ⟨b, hb⟩ := hRp.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_left b ((Nat.coprime_primes hℓ hp).2 hpℓ.symm)
  refine isCyclic_of_isPGroup_of_outer hp hpG (fun Q hQ => ?_) hP
  exact isCyclic_of_injective _
    (injective_comp_of_isPGroup (QuotientGroup.mk' R) (by rw [QuotientGroup.ker_mk']; exact hRcop)
      hQ)

end CFSG.RankThree.Automorphisms
