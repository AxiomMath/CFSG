module

public import CFSG.Sporadic.SuzRecog.ModelBase
public import Certificates.Data.SuzModelGroupsInputs

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.ModelGroups

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.Model

section Conj

variable {G : Type*} [Group G]

@[expose] def conjMap (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_conjMap {g x : G} {H : Subgroup G} : x ∈ conjMap g H ↔ g⁻¹ * x * g ∈ H := by
  rw [conjMap, mem_map_equiv, MulAut.conj_symm_apply]

theorem conjMap_one (H : Subgroup G) : conjMap 1 H = H := by
  ext x
  rw [mem_conjMap, inv_one, one_mul, mul_one]

theorem conjMap_mul (g h : G) (H : Subgroup G) : conjMap (g * h) H = conjMap g (conjMap h H) := by
  ext x
  rw [mem_conjMap, mem_conjMap, mem_conjMap, mul_inv_rev]
  simp only [mul_assoc]

theorem conjMap_zpowers (g x : G) : conjMap g (zpowers x) = zpowers (g * x * g⁻¹) := by
  rw [conjMap, MonoidHom.map_zpowers]
  rfl

@[expose] def conjSetStab (𝒮 : Set (Subgroup G)) : Subgroup G where
  carrier := {g | conjMap g '' 𝒮 = 𝒮}
  mul_mem' {g h} hg hh := by
    change conjMap (g * h) '' 𝒮 = 𝒮
    change conjMap g '' 𝒮 = 𝒮 at hg
    change conjMap h '' 𝒮 = 𝒮 at hh
    rw [show conjMap (g * h) = conjMap g ∘ conjMap h from funext (conjMap_mul g h),
      Set.image_comp, hh, hg]
  one_mem' := by
    change conjMap 1 '' 𝒮 = 𝒮
    rw [show conjMap (1 : G) = id from funext conjMap_one, Set.image_id]
  inv_mem' {g} hg := by
    change conjMap g⁻¹ '' 𝒮 = 𝒮
    change conjMap g '' 𝒮 = 𝒮 at hg
    conv_lhs => rw [← hg]
    rw [← Set.image_comp, show conjMap g⁻¹ ∘ conjMap g = id from
      funext fun H => by rw [Function.comp_apply, ← conjMap_mul, inv_mul_cancel, conjMap_one]; rfl,
      Set.image_id]

theorem mem_conjSetStab {𝒮 : Set (Subgroup G)} {g : G} :
    g ∈ conjSetStab 𝒮 ↔ conjMap g '' 𝒮 = 𝒮 := Iff.rfl

end Conj

@[expose] def rho2 : Equiv.Perm (Fin 1782) := w0 * rho1 * w0⁻¹

@[expose] def Nrho1 : Subgroup (Equiv.Perm (Fin 1782)) :=
  normalizer (zpowers rho1 : Set (Equiv.Perm (Fin 1782))) ⊓ suzM

@[expose] def pairStab : Subgroup (Equiv.Perm (Fin 1782)) :=
  conjSetStab {zpowers rho1, zpowers rho2} ⊓ suzM

@[expose] def triStab (u : Equiv.Perm (Fin 1782)) : Subgroup (Equiv.Perm (Fin 1782)) :=
  conjSetStab {zpowers rho1, zpowers rho2, zpowers u} ⊓ suzM

@[expose] def s1 : Equiv.Perm (Fin 1782) := permC 1782 ModelGroupsData.s1Arr

@[expose] def s2 : Equiv.Perm (Fin 1782) := permC 1782 ModelGroupsData.s2Arr

end CFSG.Sporadic.SuzRecog.ModelGroups
