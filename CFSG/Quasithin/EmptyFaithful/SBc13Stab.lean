module

public import CFSG.Quasithin.EmptyFaithful.S146Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc13

variable {G : Type} [Group G]

@[expose] def zStab (T : Subgroup G) (z' : G) : Subgroup G where
  carrier := {x | x ∈ mcOf T ∧ x * z' * x⁻¹ * z'⁻¹ ∈ quasithinOmegaOneCenter T}
  one_mem' := ⟨(mcOf T).one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxG, hx⟩ ⟨hyG, hy⟩
    refine ⟨(mcOf T).mul_mem hxG hyG, ?_⟩
    have e : x * y * z' * (x * y)⁻¹ * z'⁻¹ =
        (x * (y * z' * y⁻¹ * z'⁻¹) * x⁻¹) * (x * z' * x⁻¹ * z'⁻¹) := by group
    have hc : x * (y * z' * y⁻¹ * z'⁻¹) * x⁻¹ = y * z' * y⁻¹ * z'⁻¹ := by
      have h1 := S146T.comm_Z hxG hy
      calc x * (y * z' * y⁻¹ * z'⁻¹) * x⁻¹ = ((y * z' * y⁻¹ * z'⁻¹) * x) * x⁻¹ := by rw [h1]
        _ = y * z' * y⁻¹ * z'⁻¹ := by group
    rw [e, hc]
    exact (quasithinOmegaOneCenter T).mul_mem hy hx
  inv_mem' := by
    rintro x ⟨hxG, hx⟩
    refine ⟨(mcOf T).inv_mem hxG, ?_⟩
    have e : x⁻¹ * z' * x⁻¹⁻¹ * z'⁻¹ = x⁻¹ * (x * z' * x⁻¹ * z'⁻¹)⁻¹ * x := by group
    have hc : x⁻¹ * (x * z' * x⁻¹ * z'⁻¹)⁻¹ * x = (x * z' * x⁻¹ * z'⁻¹)⁻¹ := by
      have h1 := S146T.comm_Z ((mcOf T).inv_mem hxG) ((quasithinOmegaOneCenter T).inv_mem hx)
      calc x⁻¹ * (x * z' * x⁻¹ * z'⁻¹)⁻¹ * x = ((x * z' * x⁻¹ * z'⁻¹)⁻¹ * x⁻¹) * x := by rw [h1]
        _ = (x * z' * x⁻¹ * z'⁻¹)⁻¹ := by group
    rw [e, hc]
    exact (quasithinOmegaOneCenter T).inv_mem hx

theorem mem_zStab {T : Subgroup G} {z' x : G} :
    x ∈ zStab T z' ↔ x ∈ mcOf T ∧ x * z' * x⁻¹ * z'⁻¹ ∈ quasithinOmegaOneCenter T := Iff.rfl

theorem mem_zStab_of_commute {T : Subgroup G} {z' x : G} (hx : x ∈ mcOf T)
    (hc : x * z' = z' * x) : x ∈ zStab T z' := by
  refine ⟨hx, ?_⟩
  have e : x * z' * x⁻¹ * z'⁻¹ = 1 := by
    rw [hc]
    group
  rw [e]
  exact (quasithinOmegaOneCenter T).one_mem

end SBc13

end CFSG.Quasithin
