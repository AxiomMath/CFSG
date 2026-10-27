module

public import CFSG.RankThree.PartOne.U5LIFT.Ctx
public import CFSG.RankThree.PartOne.LSTD.Basic

public section

namespace CFSG.RankThree.PartOne.U5LIFT

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.LSTD

theorem perm_eq_one_of_scalar {K : Type} [Field K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 5)
    (ρ : Equiv.Perm (Fin 5))
    (h : ∀ v ∈ torusVec 5 5 K, ∃ c : Kˣ, ∀ j, v (ρ j) = c * v j) : ρ = 1 := by
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, ρ k ≠ k := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  have hm : ∀ k a b : Fin 5, ∃ m, m ≠ k ∧ m ≠ a ∧ m ≠ b := by decide
  obtain ⟨m, hmk, hmρ, hmρ'⟩ := hm k (ρ k) (ρ.symm k)
  have hkm : k ≠ m := hmk.symm
  obtain ⟨c, hc⟩ := h _ (torusElt_mem hkm hζ.pow_eq_one)
  have h1 := hc k
  rw [torusElt_apply_other hk hmρ.symm, torusElt_apply_left hkm] at h1
  have hk' : ρ.symm k ≠ k := fun h' => hk (by
    have := congrArg ρ h'
    rw [Equiv.apply_symm_apply] at this
    exact this.symm)
  have h2 := hc (ρ.symm k)
  rw [Equiv.apply_symm_apply, torusElt_apply_left hkm, torusElt_apply_other hk' hmρ'.symm,
    mul_one] at h2
  have h3 : ζ * ζ = 1 := by
    rw [← h2] at h1
    exact (by rw [mul_comm]; exact h1.symm)
  apply hζ.pow_ne_one_of_pos_of_lt (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : 2 < 5)
  rw [pow_two]
  exact h3

namespace U5Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  {K : Type} [Field K] (C : U5Ctx A c L E f K)

structure PermData (C : U5Ctx A c L E f K) where
  g : unitarySU 2 f K 5
  τ : Equiv.Perm (Fin 5)
  hperm : NormPerm 5 (g : GL (Fin 5) K) τ
  hwE : C.φ g ∈ Subgroup.normalizer (E : Set G)

namespace PermData

variable {C} (P Q : C.PermData)

@[expose] def t : MulAut E := E.normalizerMonoidHom ⟨C.φ P.g, P.hwE⟩

theorem coe_t_apply (e : E) : ((P.t e : E) : G) = C.φ P.g * e * (C.φ P.g)⁻¹ := rfl

@[expose] def mul : C.PermData where
  g := P.g * Q.g
  τ := P.τ * Q.τ
  hperm := P.hperm.mul Q.hperm
  hwE := by
    rw [map_mul]
    exact Subgroup.mul_mem _ P.hwE Q.hwE

theorem t_mul : (P.mul Q).t = P.t * Q.t := by
  refine MulEquiv.ext fun e => Subtype.ext ?_
  show C.φ (P.g * Q.g) * e * (C.φ (P.g * Q.g))⁻¹ = _
  rw [map_mul]
  show _ = ((P.t (Q.t e) : E) : G)
  rw [coe_t_apply, coe_t_apply]
  group

variable (C) in
@[expose] def one : C.PermData where
  g := 1
  τ := 1
  hperm := by simpa using NormPerm.one (n := 5) (K := K) (p := 5)
  hwE := by simp

variable (C) in
theorem t_one : (PermData.one C).t = 1 := by
  refine MulEquiv.ext fun e => Subtype.ext ?_
  show C.φ 1 * e * (C.φ 1)⁻¹ = e
  simp

theorem t_eq_iff (C : U5Ctx A c L E f K) (P Q : C.PermData) : P.t = Q.t ↔ P.τ = Q.τ := by
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := C.exists_unit_root
    have hρ : P.τ⁻¹ * Q.τ = 1 := by
      refine perm_eq_one_of_scalar hζ _ fun v hv => ?_
      have hxT : diagU v ∈ torusSU 5 5 K := mem_torusSU_iff.mpr ⟨v, hv.1, hv.2, rfl⟩
      have hxΓ := C.torus_le _ hxT
      have hmem : C.φ ⟨diagU v, hxΓ⟩ ∈ E := (C.phi_mem_E_iff _).mpr hxT
      have h1 := congrArg (fun φ : MulAut E => ((φ ⟨C.φ ⟨diagU v, hxΓ⟩, hmem⟩ : E) : G)) h
      simp only [coe_t_apply] at h1
      have h2 : C.φ ((Q.g * ⟨diagU v, hxΓ⟩ * Q.g⁻¹)⁻¹ * (P.g * ⟨diagU v, hxΓ⟩ * P.g⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        have h1' : C.φ P.g * C.φ ⟨diagU v, hxΓ⟩ * (C.φ P.g)⁻¹ =
            C.φ Q.g * C.φ ⟨diagU v, hxΓ⟩ * (C.φ Q.g)⁻¹ := h1
        rw [h1']
        group
      obtain ⟨κ, hκ⟩ := exists_of_mem_scalarsU (C.φ_ker _ h2)
      refine ⟨κ, fun j => ?_⟩
      have h3 : (P.g : GL (Fin 5) K) * diagU v * (P.g : GL (Fin 5) K)⁻¹ =
          (Q.g : GL (Fin 5) K) * diagU v * (Q.g : GL (Fin 5) K)⁻¹ * diagU (fun _ => κ) := by
        have h4 := hκ
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
        calc (P.g : GL (Fin 5) K) * diagU v * (P.g : GL (Fin 5) K)⁻¹
            = ((Q.g : GL (Fin 5) K) * diagU v * (Q.g : GL (Fin 5) K)⁻¹) *
              (((Q.g : GL (Fin 5) K) * diagU v * (Q.g : GL (Fin 5) K)⁻¹)⁻¹ *
                ((P.g : GL (Fin 5) K) * diagU v * (P.g : GL (Fin 5) K)⁻¹)) := by group
          _ = _ := by
            congr 1
      rw [P.hperm.conj_diagU hv, Q.hperm.conj_diagU hv, diagU_mul] at h3
      have h5 := congrFun (diagU_injective h3) (Q.τ j)
      simp only [Function.comp_apply, Pi.mul_apply] at h5
      rw [mul_comm]
      simpa using h5
    have : P.τ = Q.τ := by
      have h6 := congrArg (fun σ => P.τ * σ) hρ
      simpa using h6.symm
    exact this
  · intro h
    refine MulEquiv.ext fun e => Subtype.ext ?_
    obtain ⟨x, hx, i, hei⟩ := C.exists_decomp e.2
    rw [coe_t_apply, coe_t_apply, hei, C.conj_phi_mul_zpow, C.conj_phi_mul_zpow]
    congr 2
    apply Subtype.ext
    obtain ⟨v, hv1, hv2, hvx⟩ := mem_torusSU_iff.mp hx
    have hv : v ∈ torusVec 5 5 K := ⟨hv1, hv2⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hvx, P.hperm.conj_diagU hv, Q.hperm.conj_diagU hv, h]

end PermData

end U5Ctx

end CFSG.RankThree.PartOne.U5LIFT
