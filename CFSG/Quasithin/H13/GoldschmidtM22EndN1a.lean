module

public import CFSG.Quasithin.H13.GoldschmidtM22EndCtx

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

section Elem

variable (h : Hyp6Sec2 G T M L V) (h6210 : Stmt6_2_10)
include h h6210

theorem isElemAbelianMod_UU (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    IsElemAbelianMod (UU T L V) (quasithinOmegaOneCenter T) := by
  have hUO := UU_le_pCore h h6210
  have hcomm := commutator_UU_le h h6210
  have hc : ∀ u ∈ UU T L V, ∀ v ∈ UU T L V,
      u * v * u⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T := fun u hu v hv => by
    have := hcomm (Subgroup.commutator_mem_commutator hu (hUO hv))
    rwa [commutatorElement_def] at this
  have hsq : ∀ u ∈ UU T L V, u ^ 2 ∈ quasithinOmegaOneCenter T := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      have hz2 : z * z = 1 := by
        rw [← pow_two]
        exact h.toHyp611.isElemAbelian.2 z (Subgroup.mem_inf.mp hz).1
      have : (y * z * y⁻¹) ^ 2 = 1 := by
        rw [pow_two, show y * z * y⁻¹ * (y * z * y⁻¹) = y * (z * z) * y⁻¹ by group, hz2]
        group
      rw [this]
      exact Subgroup.one_mem _
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxU : x ∈ UU T L V := hx
      have hyU : y ∈ UU T L V := hy
      have hcz : x⁻¹ * y⁻¹ * x * y ∈ quasithinOmegaOneCenter T := by
        have := hc x⁻¹ ((UU T L V).inv_mem hxU) y⁻¹ ((UU T L V).inv_mem hyU)
        simpa using this
      have hyH : y ∈ HH T := UU_le_HH h hZ hyU
      have hconj : y⁻¹ * (x⁻¹ * y⁻¹ * x * y)⁻¹ * y ∈ quasithinOmegaOneCenter T := by
        have := (Subgroup.mem_normalizer_iff.mp (HH_le_normalizer_Z T ((HH T).inv_mem hyH))
          ((x⁻¹ * y⁻¹ * x * y)⁻¹)).mp ((quasithinOmegaOneCenter T).inv_mem hcz)
        simpa using this
      have e : (x * y) ^ 2 = x ^ 2 * y ^ 2 * (y⁻¹ * (x⁻¹ * y⁻¹ * x * y)⁻¹ * y) := by
        simp only [pow_two]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ihx ihy) hconj
    | inv x hx ihx =>
      have : x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ihx
  exact fun u hu v hv => ⟨hc u hu v hv, hsq u hu⟩

end Elem

end CFSG.Quasithin.H13.GM22
