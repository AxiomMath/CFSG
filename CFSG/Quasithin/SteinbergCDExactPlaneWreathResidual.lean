module

public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAlt3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathFitting

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Wreath

variable {H : Type*} [Group H]

section Wreath

variable [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))}

theorem le_normalizer_of_conj_mem_of_finite {L K : Subgroup H}
    (hK : ∀ k ∈ K, ∀ y ∈ L, k * y * k⁻¹ ∈ L) : K ≤ normalizer ((L : Subgroup H) : Set H) := by
  intro k hk
  apply RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj k).injective])
  rintro _ ⟨y, hy, rfl⟩
  exact hK k hk y hy

theorem mem_normalizer_centralizer_of_mem_normalizer {L : Subgroup H} {x : H}
    (hx : x ∈ normalizer ((L : Subgroup H) : Set H)) :
    x ∈ normalizer ((centralizer ((L : Subgroup H) : Set H) : Subgroup H) : Set H) := by
  apply le_normalizer_of_conj_mem_of_finite (K := zpowers x) _ (mem_zpowers x)
  intro k hk c hc
  have hkL : k ∈ normalizer ((L : Subgroup H) : Set H) :=
    (zpowers_le.mpr hx) hk
  rw [mem_centralizer_iff] at hc ⊢
  intro u hu
  have hu' : k⁻¹ * u * k⁻¹⁻¹ ∈ L :=
    (mem_normalizer_iff.mp ((normalizer ((L : Subgroup H) : Set H)).inv_mem hkL) u).mp hu
  have h1 := hc _ hu'
  calc u * (k * c * k⁻¹) = k * ((k⁻¹ * u * k⁻¹⁻¹) * c) * k⁻¹ := by group
    _ = k * (c * (k⁻¹ * u * k⁻¹⁻¹)) * k⁻¹ := by rw [h1]
    _ = k * c * k⁻¹ * u := by group

end Wreath

end SteinbergCD

open Subgroup SteinbergCD CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Wreath

end CFSG.Quasithin
