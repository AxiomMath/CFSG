module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumT

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Insp7

theorem numFactAt_of_centralizer_dvd {F : ∀ (L : Type) [Group L], Prop} {t : ℕ} (S : Finset ℕ)
    (hS : ∀ c ∈ S, ¬ 9 ∣ c * t)
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      Subgroup.center L = ⊥ ∧ Nat.card (Outer L) ∣ t ∧
        ∀ z : L, z * z = 1 → z ≠ 1 →
          Nat.card (Subgroup.centralizer ({z} : Set L)) ∈ S) :
    NumFactAt F := by
  intro L _ _ hq hFL z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ _ _ _ _ hC9
  obtain ⟨hZ, hA, hcz⟩ := hF L hq hFL
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  have hdvd := card_centralizer_dvd hZ ρ hρ hinn z ž hž
  have h9 : 9 ∣ Nat.card (Subgroup.centralizer ({ž} : Set Gc)) := ⟨Nat.card Ŝ, hC9⟩
  exact hS _ (hcz z hz2 hz1) ((h9.trans hdvd).trans (Nat.mul_dvd_mul_left _ hA))

theorem numFactAt_of_model_dvd {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥) {t : ℕ}
    (hA : Nat.card (Outer X) ∣ t) (S : Finset ℕ) (hS : ∀ c ∈ S, ¬ 9 ∣ c * t)
    (hc : ∀ x : X, orderOf x = 2 → Nat.card (Subgroup.centralizer ({x} : Set X)) ∈ S) :
    NumFactAt (fun L _ => Nonempty (L ≃* X)) := by
  refine numFactAt_of_centralizer_dvd S hS (fun L _ _ _ ⟨e⟩ => ⟨?_, ?_, ?_⟩)
  · have h1 : (Subgroup.center L).map e.toMonoidHom = Subgroup.center X := Subgroup.map_center_eq e
    rw [hZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact hA
  · intro z hz2 hz1
    have hz2' : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
    have hz1' : e z ≠ 1 := fun h => hz1 (e.injective (by rw [h, map_one]))
    have hord : orderOf (e z) = 2 := orderOf_eq_prime (by rwa [sq]) hz1'
    have hcard : Nat.card (Subgroup.centralizer ({z} : Set L)) =
        Nat.card (Subgroup.centralizer ({e z} : Set X)) := by
      rw [← map_centralizer_singleton_mulEquiv e z]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv
    rw [hcard]
    exact hc (e z) hord

end Insp7

end CFSG.Quasithin
