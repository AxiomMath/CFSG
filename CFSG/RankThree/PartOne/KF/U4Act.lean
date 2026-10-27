module

public import CFSG.RankThree.PartOne.KF.U4Refl

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.Sec12Three
  CFSG.LocalAnalysis.ComponentInitial

namespace U4Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] (C : U4Ctx p A c L E f K)

structure PermData (C : U4Ctx p A c L E f K) where
  g : unitarySU 2 f K 4
  τ : Equiv.Perm (Fin 4)
  hperm : NormPerm p (g : GL (Fin 4) K) τ
  hwE : C.phi g ∈ Subgroup.normalizer (E : Set G)

namespace PermData

variable {C} (P Q : C.PermData)

@[expose] def t : MulAut E := E.normalizerMonoidHom ⟨C.phi P.g, P.hwE⟩

theorem coe_t_apply (e : E) : ((P.t e : E) : G) = C.phi P.g * e * (C.phi P.g)⁻¹ := rfl

@[expose] def mul : C.PermData where
  g := P.g * Q.g
  τ := P.τ * Q.τ
  hperm := P.hperm.mul Q.hperm
  hwE := by
    rw [map_mul]
    exact Subgroup.mul_mem _ P.hwE Q.hwE

theorem t_mul : (P.mul Q).t = P.t * Q.t := by
  refine MulEquiv.ext fun e => Subtype.ext ?_
  show C.phi (P.g * Q.g) * e * (C.phi (P.g * Q.g))⁻¹ = _
  rw [map_mul]
  show _ = ((P.t (Q.t e) : E) : G)
  rw [coe_t_apply, coe_t_apply]
  group

variable (C) in
@[expose] def one : C.PermData where
  g := 1
  τ := 1
  hperm := by simpa using NormPerm.one (n := 4) (K := K) (p := p)
  hwE := by simp

variable (C) in
theorem t_one : (PermData.one C).t = 1 := by
  refine MulEquiv.ext fun e => Subtype.ext ?_
  show C.phi 1 * e * (C.phi 1)⁻¹ = e
  simp

@[expose] def pow : ℕ → C.PermData
  | 0 => one C
  | n + 1 => (pow n).mul P

theorem τ_pow (n : ℕ) : (P.pow n).τ = P.τ ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (P.pow n).τ * P.τ = _
    rw [ih, pow_succ]

theorem t_pow (n : ℕ) : (P.pow n).t = P.t ^ n := by
  induction n with
  | zero => exact t_one C
  | succ n ih =>
    show ((P.pow n).mul P).t = _
    rw [t_mul, ih, pow_succ]

theorem t_eq_iff (C : U4Ctx p A c L E f K) (P Q : C.PermData) : P.t = Q.t ↔ P.τ = Q.τ := by
  constructor
  · intro h
    refine NormPerm.eq_of_conj_eq C.hdist P.hperm Q.hperm fun x hx => ?_
    have hxΓ := C.torus_le x hx
    have hmem : C.phi ⟨x, hxΓ⟩ ∈ E := (C.phi_mem_E_iff _).mpr hx
    have h1 := congrArg (fun φ : MulAut E => ((φ ⟨C.phi ⟨x, hxΓ⟩, hmem⟩ : E) : G)) h
    simp only [coe_t_apply] at h1
    have h2 : C.phi (P.g * ⟨x, hxΓ⟩ * P.g⁻¹) = C.phi (Q.g * ⟨x, hxΓ⟩ * Q.g⁻¹) := by
      simpa [map_mul, map_inv] using h1
    have h3 := congrArg (fun y : unitarySU 2 f K 4 => (y : GL (Fin 4) K))
      (C.phi_injective h2)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h3
  · intro h
    refine MulEquiv.ext fun e => Subtype.ext ?_
    obtain ⟨x, hx, i, hei⟩ := C.exists_decomp e.2
    rw [coe_t_apply, coe_t_apply, hei, C.conj_phi_mul_zpow, C.conj_phi_mul_zpow]
    congr 2
    apply Subtype.ext
    obtain ⟨v, hv1, hv2, hvx⟩ := mem_torusSU_iff.mp hx
    have hv : v ∈ torusVec p 4 K := ⟨hv1, hv2⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hvx, P.hperm.conj_diagU hv, Q.hperm.conj_diagU hv, h]

theorem orderOf_t : orderOf P.t = orderOf P.τ := by
  have key : ∀ n : ℕ, P.t ^ n = 1 ↔ P.τ ^ n = 1 := by
    intro n
    have h := t_eq_iff C (P.pow n) (one C)
    rw [t_pow, τ_pow, t_one C] at h
    exact h
  refine Nat.dvd_antisymm ?_ ?_
  · exact orderOf_dvd_of_pow_eq_one ((key _).mpr (pow_orderOf_eq_one _))
  · exact orderOf_dvd_of_pow_eq_one ((key _).mp (pow_orderOf_eq_one _))

end PermData

end U4Ctx

end CFSG.RankThree.PartOne.KFU
