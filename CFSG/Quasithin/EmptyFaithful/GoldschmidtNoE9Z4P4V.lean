module

public import CFSG.Quasithin.EmptyFaithful.S146ThreeB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section V

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.exists_mem_VZ_not_mem_Z (S : Setting146 G T M) :
    ∃ v ∈ VZ T M, v ∉ quasithinOmegaOneCenter T := by
  by_contra hcon
  push Not at hcon
  have hle : VZ T M ≤ quasithinOmegaOneCenter T := fun v hv => hcon v hv
  have h1 := Subgroup.card_le_of_le hle
  rw [S.hyp.rank_two, S.card_Z] at h1
  omega

theorem Setting146.false_of_comm_mem_Z (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {v : G} (hvV : v ∈ VZ T M) (hvZ : v ∉ quasithinOmegaOneCenter T)
    (hcomm : ∀ y ∈ H, y * v * y⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T) : False := by
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hfwd : ∀ y ∈ H, ∀ x ∈ VZ T M, y * x * y⁻¹ ∈ VZ T M := by
    intro y hy x hx
    by_cases hxZ : x ∈ quasithinOmegaOneCenter T
    · rw [S146T.conj_Z (hHG hy) hxZ]
      exact hZV hxZ
    · have hxv : x * v⁻¹ ∈ quasithinOmegaOneCenter T :=
        S146T.mul_inv_mem_of_card hZV S.hyp.rank_two S.card_Z hx hvV hxZ hvZ
      have e : y * x * y⁻¹ = (y * (x * v⁻¹) * y⁻¹) * ((y * v * y⁻¹ * v⁻¹) * v) := by group
      rw [e, S146T.conj_Z (hHG hy) hxv]
      exact (VZ T M).mul_mem (hZV hxv) ((VZ T M).mul_mem (hZV (hcomm y hy)) hvV)
  apply hH.2
  intro y hy
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hfwd y hy x hx, fun hx => ?_⟩
    have := hfwd y⁻¹ (H.inv_mem hy) _ hx
    simpa [mul_assoc] using this
  rwa [S.hyp1281.normalizer_VZ] at hyN

end V

end CFSG.Quasithin
