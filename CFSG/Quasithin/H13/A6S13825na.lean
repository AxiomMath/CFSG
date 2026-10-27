module

public import CFSG.Quasithin.H13.A6S13825o
public import CFSG.Quasithin.H13.A6S13825u

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative
open L13825

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}
  {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem inducesTransvMod_of_comm {h : G} (hh : h ∈ H) (hne : sigmaH hH ⟨h, hh⟩ ≠ 1)
    {r : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))}
    (hr : ∀ v, sigmaH hH ⟨h, hh⟩ v * v⁻¹ = 1 ∨ sigmaH hH ⟨h, hh⟩ v * v⁻¹ = r) :
    InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V) := by
  obtain ⟨u₀, rfl⟩ := InternalSec.secMk_surjective _ r
  refine ⟨fun hall => hne ((A6Mod.secAct_eq_one_iff _ _ _).2 hall), (u₀ : G), fun x hx => ?_⟩
  have key : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
      (Setup.rho _ H (le_normalizer_conjClosure S.V3 H) ⟨h, hh⟩ ⟨x, hx⟩ * ⟨x, hx⟩⁻¹) =
      sigmaH hH ⟨h, hh⟩ (InternalSec.secMk _ ⟨x, hx⟩) * (InternalSec.secMk _ ⟨x, hx⟩)⁻¹ := by
    rw [map_mul, map_inv]
    rfl
  rcases hr (InternalSec.secMk _ ⟨x, hx⟩) with h1 | h1
  · left
    rw [← key] at h1
    have := (A6Mod.secMk_eq_one_iff _).1 h1
    simpa [Setup.rho_apply_coe] using this
  · right
    rw [← key, ← mul_inv_eq_one, ← map_inv, ← map_mul] at h1
    have := (A6Mod.secMk_eq_one_iff _).1 h1
    simpa [Setup.rho_apply_coe] using this

end Setting4

end CFSG.Quasithin.H13.A6
