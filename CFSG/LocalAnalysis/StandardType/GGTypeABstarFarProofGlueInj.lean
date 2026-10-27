module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueVec

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Inj

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem GGFarCtx.permAut₁_injective (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    Function.Injective hC.permAut₁ := by
  rw [injective_iff_map_eq_one]
  intro π hπ
  obtain ⟨τ, hτ, hvec⟩ := hC.exists_vecs₁
  ext k
  obtain ⟨z, hz_mem, hz_act⟩ := hvec k
  have hm : 3 ≤ n + 1 := le_trans hC.three_le (Nat.le_succ n)
  have hconj : φ₁ (slPerm hC.two π) * z * (φ₁ (slPerm hC.two π))⁻¹ = z := by
    have hfix : hC.permAut₁ π ⟨z, hz_mem⟩ = ⟨z, hz_mem⟩ := by rw [hπ]; rfl
    have hcoe := congrArg (fun w : ↥Bs => (w : G)) hfix
    simpa [GGFarCtx.permAut₁_apply] using hcoe
  exact congrArg Fin.val (ggActsVec_perm_fix hC.lifts.ker₁ hC.two hm hτ hz_act hconj)

theorem GGFarCtx.permAut₂_injective (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    Function.Injective hC.permAut₂ := by
  rw [injective_iff_map_eq_one]
  intro π hπ
  obtain ⟨τ, hτ, hvec⟩ := hC.exists_vecs₂
  ext k
  obtain ⟨z, hz_mem, hz_act⟩ := hvec k
  have hm : 3 ≤ n + 1 := le_trans hC.three_le (Nat.le_succ n)
  have hconj : φ₂ (slPerm hC.two π) * z * (φ₂ (slPerm hC.two π))⁻¹ = z := by
    have hfix : hC.permAut₂ π ⟨z, hz_mem⟩ = ⟨z, hz_mem⟩ := by rw [hπ]; rfl
    have hcoe := congrArg (fun w : ↥Bs => (w : G)) hfix
    simpa [GGFarCtx.permAut₂_apply] using hcoe
  exact congrArg Fin.val (ggActsVec_perm_fix hC.lifts.ker₂ hC.two hm hτ hz_act hconj)

theorem GGFarCtx.permAut₂_swap_ne_x (hC : GGFarCtx p Bs φ₁ φ₂ x y) {j : Fin n}
    (hj : j.val + 1 = n) :
    hC.permAut₂ (Equiv.swap j.castSucc j.succ) ⟨x, hC.x_mem⟩ ≠ ⟨x, hC.x_mem⟩ := by
  intro hfix
  obtain ⟨τ, hτ, hxvec⟩ := hC.exists_x_vec
  have hm : 3 ≤ n + 1 := le_trans hC.three_le (Nat.le_succ n)
  have hconj : φ₂ (slPerm hC.two (Equiv.swap j.castSucc j.succ)) * x *
      (φ₂ (slPerm hC.two (Equiv.swap j.castSucc j.succ)))⁻¹ = x := by
    have hcoe := congrArg (fun w : ↥Bs => (w : G)) hfix
    simpa [GGFarCtx.permAut₂_apply] using hcoe
  have hlast := ggActsVec_perm_fix hC.lifts.ker₂ hC.two hm hτ hxvec hconj
  have hjs : j.succ = Fin.last n := Fin.ext (by simp [Fin.succ, hj])
  rw [← hjs, Equiv.swap_apply_right] at hlast
  have hv : j.castSucc.val = j.succ.val := congrArg Fin.val hlast
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

end Inj

end CFSG.StandardType
