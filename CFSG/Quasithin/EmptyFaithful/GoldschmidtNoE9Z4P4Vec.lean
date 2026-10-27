module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4V
public import CFSG.Quasithin.EmptyFaithful.S146zHWsub

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Vec

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem mem_of_clsU_mem_Wsub {T V L V₁ Vp : Subgroup G} (h : HypF91 T V L V₁ Vp H)
    {X : Subgroup G} (hXU : X ≤ conjClosure Vp H) (hVX : V₁ ≤ X) {u : G}
    (hu : u ∈ conjClosure Vp H) (hw : clsU h hu ∈ Wsub h X) : u ∈ X := by
  obtain ⟨x, hx, hxX, hxu⟩ := exists_clsU_of_mem_Wsub h hXU hw
  have h1 : x⁻¹ * u ∈ V₁ := (clsU_eq_iff h hx hu).mp hxu
  have e : u = x * (x⁻¹ * u) := by group
  rw [e]
  exact X.mul_mem hxX (hVX h1)

theorem exists_VZ_decomp (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c) :
    ∃ (v : G) (hvV : v ∈ VZ T M), v ∉ quasithinOmegaOneCenter T ∧
      ∃ (a c : UMod h), a ∈ kOf (rhoH h) ∧ a ≠ 1 ∧
        (∀ x : G, x ∈ T → ∀ hx : x ∈ H, rhoH h ⟨x, hx⟩ a = a) ∧ c ∈ fixV (rhoH h).range ∧
          clsU h (le_conjClosure (VZ T M) H hvV) = a * c := by
  obtain ⟨v, hvV, hvZ⟩ := S.exists_mem_VZ_not_mem_Z
  have hvU : v ∈ conjClosure (VZ T M) H := le_conjClosure _ _ hvV
  obtain ⟨a, ha, c, hc, hvac⟩ := hsplit (clsU h hvU)
  refine ⟨v, hvV, hvZ, a, c, ha, ?_, ?_, hc, hvac⟩
  · intro ha1
    refine S.false_of_comm_mem_Z hH hvV hvZ fun y hy => ?_
    have hcy : rhoH h ⟨y, hy⟩ c = c := hc _ ⟨⟨y, hy⟩, rfl⟩
    have hfix : rhoH h ⟨y, hy⟩ (clsU h hvU) = clsU h hvU := by
      rw [hvac, ha1, one_mul]
      exact hcy
    exact (rhoH_clsU_eq_iff h ⟨y, hy⟩ hvU).mp hfix
  · intro x hxT hxH
    have hfix : rhoH h ⟨x, hxH⟩ (clsU h hvU) = clsU h hvU :=
      (rhoH_clsU_eq_iff h ⟨x, hxH⟩ hvU).mpr (S.conj_mem_mul_Z hxT hvV)
    have hcx : rhoH h ⟨x, hxH⟩ c = c := hc _ ⟨⟨x, hxH⟩, rfl⟩
    rw [hvac, map_mul, hcx] at hfix
    exact mul_right_cancel hfix

end Vec

end CFSG.Quasithin
