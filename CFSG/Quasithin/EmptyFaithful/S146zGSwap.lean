module

public import CFSG.Quasithin.EmptyFaithful.S146zClaim

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeC

section Swap

variable {G : Type} [Group G] [Finite G]

theorem swap_count {Z U UK Up : Subgroup G} {b : G} (hU : IsPGroup 2 U) (hUKU : UK ≤ U)
    (hZK : Z ≤ UK) (hinf : UK ⊓ Up = Z) (hbZ : b ∈ Subgroup.normalizer (Z : Set G))
    (hb2 : b * b = 1) (hswap : conjSub b UK = Up) (hrk : mIdx UK Z = 6) :
    6 ≤ mIdx U (centralizerMod Z U (Subgroup.zpowers b)) := by
  classical
  set C := centralizerMod Z U (Subgroup.zpowers b) with hC
  have hCUK : C ⊓ UK ≤ Z := by
    rintro x ⟨hxC, hxK⟩
    obtain ⟨-, -, hcomm⟩ := (mem_centralizerMod_zpowers_iff hb2).mp hxC
    have h1 : b * x * b⁻¹ ∈ Up := by rw [← hswap]; exact mul_mem_conjSub hxK
    have h2 : b * x * b⁻¹ ∈ UK := by
      have e : b * x * b⁻¹ = (b * x * b⁻¹ * x⁻¹) * x := by group
      rw [e]; exact UK.mul_mem (hZK hcomm) hxK
    have h3 : b * x * b⁻¹ ∈ Z := hinf ▸ ⟨h2, h1⟩
    have h4 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbZ) _).mp h3
    have e : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
    rwa [e] at h4
  have h1 : mIdx UK Z ≤ mIdx UK (C ⊓ UK) := mIdx_anti_of_le (X := UK) hCUK
  have h2 : mIdx UK (C ⊓ UK) ≤ mIdx U C := mIdx_inf_le_mIdx hU hUKU
  omega

end Swap

end CFSG.Quasithin.ThreeC
