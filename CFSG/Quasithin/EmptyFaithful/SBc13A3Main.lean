module

public import CFSG.Quasithin.EmptyFaithful.SBc13A3Core
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc13

section Sub

variable {G : Type} [Group G] [Finite G]

theorem core_sub_prime_A3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₁ K R : Subgroup G}
    {a₁ a₂ x : G} (hrank : CFSG.Open.pRank p (⊤ : Subgroup ↥G₁) ≤ 2) (hKG : K ≤ G₁)
    (hR2 : IsPGroup 2 ↥R) (hRn : ∀ g ∈ G₁, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hRK : R ≤ K)
    (ha₁K : a₁ ∈ K) (ha₂K : a₂ ∈ K) (ha₁p : a₁ ^ p = 1) (ha₂p : a₂ ^ p = 1)
    (ha₁R : a₁ ∉ R) (ha₂R : a₂ ∉ R) (hcomm : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ ∈ R)
    (hind : ∀ m : ℤ, a₁ ^ m * a₂⁻¹ ∈ R → False) (hxG : x ∈ G₁) (hxp : x ^ p = 1) (hxK : x ∉ K)
    (hxa₁ : ∃ n : ℤ, x * a₁ * x⁻¹ * (a₁ ^ n)⁻¹ ∈ R)
    (hxa₂ : ∃ n : ℤ, x * a₂ * x⁻¹ * (a₂ ^ n)⁻¹ ∈ R) : False := by
  have hmem : ∀ (S : Subgroup G) (y : ↥G₁), y ∈ S.subgroupOf G₁ ↔ (y : G) ∈ S :=
    fun S y => Subgroup.mem_subgroupOf
  refine core_prime_A3 (Y := ↥G₁) (K := K.subgroupOf G₁) (R := R.subgroupOf G₁)
    (a₁ := ⟨a₁, hKG ha₁K⟩) (a₂ := ⟨a₂, hKG ha₂K⟩) (x := ⟨x, hxG⟩) hp hp2 hrank
    (hR2.comap_of_injective G₁.subtype G₁.subtype_injective)
    (fun g r hr => (hmem R _).mpr (by simpa using hRn _ g.2 _ ((hmem R r).mp hr)))
    (fun r hr => (hmem K r).mpr (hRK ((hmem R r).mp hr)))
    ((hmem K _).mpr ha₁K) ((hmem K _).mpr ha₂K)
    (Subtype.ext (by simpa using ha₁p)) (Subtype.ext (by simpa using ha₂p))
    (fun h => ha₁R ((hmem R _).mp h)) (fun h => ha₂R ((hmem R _).mp h))
    ((hmem R _).mpr (by simpa using hcomm))
    (fun m h => hind m (by simpa using (hmem R _).mp h))
    (Subtype.ext (by simpa using hxp)) (fun h => hxK ((hmem K _).mp h))
    (by
      obtain ⟨n, hn⟩ := hxa₁
      exact ⟨n, (hmem R _).mpr (by simpa using hn)⟩)
    (by
      obtain ⟨n, hn⟩ := hxa₂
      exact ⟨n, (hmem R _).mpr (by simpa using hn)⟩)

end Sub

end SBc13

end CFSG.Quasithin
