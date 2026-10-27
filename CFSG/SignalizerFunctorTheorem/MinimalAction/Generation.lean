module

public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryGeneration

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_elemAbelian_nine {E P S : Subgroup G}
    (hE : IsElemAbelian 3 E) (hE9 : 9 ≤ Nat.card E)
    (hP : Nat.Coprime 3 (Nat.card P))
    (hEP : E ≤ Subgroup.normalizer (P : Set G))
    (hSE : S ≤ E) (hS : Nat.card S = 3)
    (hfree : ∀ s ∈ E, s ∉ S → ∀ g ∈ P, s * g = g * s → g = 1) :
    P ≤ Subgroup.centralizer (S : Set G) := by
  let : CommGroup E := { (inferInstance : Group E) with mul_comm := hE.1.is_comm.comm }
  let := CFSG.SignalizerFunctor.Helpers.conjugationAction E P hEP
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_order_generation 3 1
    Nat.prime_three E (fun x => Subtype.ext (hE.2 x x.2)) (by simpa using hE9) P hP
  have hS' : Nat.card (S.subgroupOf E) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSE).toEquiv).trans hS
  have htop : (⊤ : Subgroup P) ≤ (Subgroup.centralizer (S : Set G)).comap P.subtype := by
    refine le_of_eq_of_le hgen.symm (iSup₂_le fun T hT g hg => ?_)
    have hcomm : ∀ t ∈ T, (t : G) * g = g * t := by
      intro t ht
      have h := congrArg (fun x : P => (x : G)) ((FixedPoints.mem_subgroup _ _ _).mp hg ⟨t, ht⟩)
      change (t : G) * g * (t : G)⁻¹ = g at h
      exact mul_inv_eq_iff_eq_mul.mp h
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    by_cases hle : T ≤ S.subgroupOf E
    · have hT3 : Nat.card T = 3 := by simpa using hT
      have heq : T = S.subgroupOf E :=
        Subgroup.eq_of_le_of_card_ge hle (hS'.trans hT3.symm).le
      intro s hs
      have hsS : s ∈ S := hs
      have hmem : (⟨s, hSE hsS⟩ : E) ∈ T := by
        rw [heq]
        exact Subgroup.mem_subgroupOf.mpr hsS
      exact hcomm ⟨s, hSE hsS⟩ hmem
    · obtain ⟨t, ht, htS⟩ := IsConcreteLE.not_le_iff_exists.mp hle
      have hg1 : (g : G) = 1 :=
        hfree t t.2 (fun h => htS (Subgroup.mem_subgroupOf.mpr h)) g g.2 (hcomm t ht)
      intro s hs
      change s * (g : G) = (g : G) * s
      rw [hg1, mul_one, one_mul]
  intro x hx
  exact htop (Subgroup.mem_top (⟨x, hx⟩ : P))

end CFSG.SignalizerFunctorTheorem.MinimalAction
