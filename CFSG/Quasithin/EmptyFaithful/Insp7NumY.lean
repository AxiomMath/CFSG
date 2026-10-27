module


import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Aut
import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.Quasithin.EmptyFaithful.Insp7NumT

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Insp7

theorem numFactAt_of_centralizer_nine {F : ∀ (L : Type) [Group L], Prop} {t : ℕ}
    (ht : Nat.Coprime 9 t)
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      Subgroup.center L = ⊥ ∧ Nat.card (Outer L) ∣ t ∧
        ∀ z : L, z * z = 1 → z ≠ 1 → ¬ 9 ∣ Nat.card (Subgroup.centralizer ({z} : Set L))) :
    NumFactAt F := by
  intro L _ _ hq hFL z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ _ _ _ _ hC9
  obtain ⟨hZ, hA, hcz⟩ := hF L hq hFL
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  have hdvd := card_centralizer_dvd hZ ρ hρ hinn z ž hž
  have h9 : 9 ∣ Nat.card (Subgroup.centralizer ({ž} : Set Gc)) := ⟨Nat.card Ŝ, hC9⟩
  have h9' : 9 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) * t :=
    (h9.trans hdvd).trans (Nat.mul_dvd_mul_left _ hA)
  exact hcz z hz2 hz1 (ht.dvd_of_dvd_mul_right h9')

theorem numFactAt_sp44 : NumFactAt (fun L _ => StatedClassicalModel L .PSp 2 2 2) := by
  refine numFactAt_of_centralizer_nine (t := 4) (by norm_num) ?_
  intro L _ _ _ hL
  obtain ⟨-, K, _, hfin, hKcard, ⟨e⟩⟩ := hL
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hKcard
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have h1 : ∀ q : StatedProj (StatedSp 2 K), e x * q = q * e x := fun q => by
      have := Subgroup.mem_center_iff.mp hx (e.symm q)
      have h2 := congrArg e this
      simp only [map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2.symm
    exact e.injective (by rw [map_one]; exact CFSG.QuasithinUnique.Id2519.USp4.eq_one_of_central h1)
  ·
    have h := (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.outer_card_dvd
      (K := K) (r := 2) Nat.prime_two (f := 2) (by norm_num) hKcard le_rfl).1
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    norm_num at h
    exact h
  ·
    intro z hz2 hz1 h9
    have hs2 : e z ^ 2 = 1 := by rw [sq, ← map_mul, hz2, map_one]
    have hcard : Nat.card (Subgroup.centralizer ({z} : Set L)) =
        Nat.card (Subgroup.centralizer ({e z} : Set (StatedProj (StatedSp 2 K)))) := by
      rw [← map_centralizer_singleton_mulEquiv e z]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv
    rw [hcard] at h9
    have hone := CFSG.QuasithinUnique.Id2519.USp4.eq_one_of_centralizes_of_nine_dvd hK4 h9 hs2
      (fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp hk).symm)
    exact hz1 (e.injective (by rw [hone, map_one]))

end Insp7

end CFSG.Quasithin
