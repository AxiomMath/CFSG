module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open MulAction

section Sigma

variable {G : Type*} [Group G] {Y : Type*} [MulAction G Y] [IsPretransitive G Y] (y₀ : Y)

@[expose] def StabConj (α : MulAut G) (j : G) : Prop :=
  ∀ h : G, h • y₀ = y₀ ↔ (j⁻¹ * α h * j) • y₀ = y₀

@[expose] def sigmaFun (α : MulAut G) (j : G) (y : Y) : Y :=
  (α (Classical.choose (exists_smul_eq G y₀ y)) * j) • y₀

variable {y₀}

theorem sigmaFun_smul {α : MulAut G} {j : G} (hα : StabConj y₀ α j) (g : G) :
    sigmaFun y₀ α j (g • y₀) = (α g * j) • y₀ := by
  have hg' := Classical.choose_spec (exists_smul_eq G y₀ (g • y₀))
  set g' := Classical.choose (exists_smul_eq G y₀ (g • y₀))
  have h1 : (g⁻¹ * g') • y₀ = y₀ := by rw [mul_smul, hg', inv_smul_smul]
  have h2 := (hα _).1 h1
  show (α g' * j) • y₀ = (α g * j) • y₀
  have e : α g' * j = (α g * j) * (j⁻¹ * α (g⁻¹ * g') * j) := by
    rw [map_mul, map_inv]
    group
  rw [e, mul_smul, h2]

theorem sigmaFun_equivariant {α : MulAut G} {j : G} (hα : StabConj y₀ α j) (h : G) (y : Y) :
    sigmaFun y₀ α j (h • y) = α h • sigmaFun y₀ α j y := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G y₀ y
  rw [← mul_smul, sigmaFun_smul hα, sigmaFun_smul hα, ← mul_smul, map_mul, mul_assoc]

omit [IsPretransitive G Y] in
theorem stabConj_mul {α β : MulAut G} {j k : G} (hα : StabConj y₀ α j) (hβ : StabConj y₀ β k) :
    StabConj y₀ (α * β) (α k * j) := by
  intro h
  rw [hβ h, hα]
  have e : j⁻¹ * α (k⁻¹ * β h * k) * j = (α k * j)⁻¹ * (α * β) h * (α k * j) := by
    rw [map_mul, map_mul, map_inv, MulAut.mul_apply]
    group
  rw [e]

omit [IsPretransitive G Y] in
theorem stabConj_one : StabConj y₀ (1 : MulAut G) 1 := by
  intro h
  rw [MulAut.one_apply, inv_one, one_mul, mul_one]

theorem sigmaFun_comp {α β : MulAut G} {j k : G} (hα : StabConj y₀ α j)
    (hβ : StabConj y₀ β k) (y : Y) :
    sigmaFun y₀ α j (sigmaFun y₀ β k y) = sigmaFun y₀ (α * β) (α k * j) y := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G y₀ y
  rw [sigmaFun_smul hβ, sigmaFun_smul hα, sigmaFun_smul (stabConj_mul hα hβ), map_mul,
    MulAut.mul_apply, mul_assoc]

theorem sigmaFun_one (y : Y) : sigmaFun y₀ (1 : MulAut G) 1 y = y := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G y₀ y
  rw [sigmaFun_smul stabConj_one, MulAut.one_apply, mul_one]

@[expose] def SelfNormalizing (y₀ : Y) : Prop :=
  ∀ g : G, (∀ h : G, h • y₀ = y₀ ↔ (g⁻¹ * h * g) • y₀ = y₀) → g • y₀ = y₀

theorem sigmaFun_indep (hN : SelfNormalizing (G := G) y₀) {α : MulAut G} {j j' : G}
    (hα : StabConj y₀ α j) (hα' : StabConj y₀ α j') : sigmaFun y₀ α j = sigmaFun y₀ α j' := by
  have hn : (j⁻¹ * j') • y₀ = y₀ := by
    refine hN _ fun x => ?_
    have e1 : x = j⁻¹ * α (α.symm (j * x * j⁻¹)) * j := by
      rw [MulEquiv.apply_symm_apply]
      group
    have e2 : (j⁻¹ * j')⁻¹ * x * (j⁻¹ * j') =
        j'⁻¹ * α (α.symm (j * x * j⁻¹)) * j' := by
      rw [MulEquiv.apply_symm_apply]
      group
    rw [e2]
    conv_lhs => rw [e1]
    rw [← hα, hα']
  funext y
  obtain ⟨g, rfl⟩ := exists_smul_eq G y₀ y
  rw [sigmaFun_smul hα, sigmaFun_smul hα']
  rw [show α g * j' = (α g * j) * (j⁻¹ * j') by group, mul_smul (α g * j), hn]

theorem sigmaFun_conj (g : G) (y : Y) : sigmaFun y₀ (MulAut.conj g) g y = g • y := by
  have hc : StabConj y₀ (MulAut.conj g) g := by
    intro h
    rw [MulAut.conj_apply]
    group
  obtain ⟨g', rfl⟩ := exists_smul_eq G y₀ y
  rw [sigmaFun_smul hc, MulAut.conj_apply, ← mul_smul]
  group

end Sigma

section Hom

variable {G : Type*} [Group G] {Y : Type*} [MulAction G Y] [IsPretransitive G Y] {y₀ : Y}
  (hN : SelfNormalizing (G := G) y₀) (hex : ∀ α : MulAut G, ∃ j, StabConj y₀ α j)

@[expose] def sigma (α : MulAut G) : Y → Y := sigmaFun y₀ α (Classical.choose (hex α))

include hN in
theorem sigma_eq {α : MulAut G} {j : G} (hα : StabConj y₀ α j) :
    sigma hex α = sigmaFun y₀ α j :=
  sigmaFun_indep hN (Classical.choose_spec (hex α)) hα

include hN in
theorem sigma_mul (α β : MulAut G) (y : Y) :
    sigma hex (α * β) y = sigma hex α (sigma hex β y) := by
  rw [sigma_eq hN hex (stabConj_mul (Classical.choose_spec (hex α))
    (Classical.choose_spec (hex β))),
    ← sigmaFun_comp (Classical.choose_spec (hex α)) (Classical.choose_spec (hex β))]
  rfl

include hN in
theorem sigma_one (y : Y) : sigma hex 1 y = y := by
  rw [sigma_eq hN hex stabConj_one, sigmaFun_one]

@[expose] def sigmaHom : MulAut G →* Equiv.Perm Y where
  toFun α :=
    { toFun := sigma hex α
      invFun := sigma hex α⁻¹
      left_inv := fun y => by rw [← sigma_mul hN hex, inv_mul_cancel, sigma_one hN hex]
      right_inv := fun y => by rw [← sigma_mul hN hex, mul_inv_cancel, sigma_one hN hex] }
  map_one' := Equiv.ext fun y => sigma_one hN hex y
  map_mul' α β := Equiv.ext fun y => sigma_mul hN hex α β y

theorem sigmaHom_apply (α : MulAut G) (y : Y) : sigmaHom hN hex α y = sigma hex α y := rfl

include hN in
theorem sigmaHom_equivariant (α : MulAut G) (h : G) (y : Y) :
    sigmaHom hN hex α (h • y) = α h • sigmaHom hN hex α y := by
  rw [sigmaHom_apply, sigmaHom_apply, sigma_eq hN hex (Classical.choose_spec (hex α))]
  exact sigmaFun_equivariant (Classical.choose_spec (hex α)) h y

include hN in
theorem sigmaHom_conj (g : G) (y : Y) : sigmaHom hN hex (MulAut.conj g) y = g • y := by
  have hc : StabConj y₀ (MulAut.conj g) g := by
    intro h
    rw [MulAut.conj_apply]
    group
  rw [sigmaHom_apply, sigma_eq hN hex hc, sigmaFun_conj]

end Hom

end CFSG.Sporadic.J4Schreier
