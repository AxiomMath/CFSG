
module


public import CFSG.Monster.B.TwoA.Sp8.Orth8Forms
public import CFSG.Monster.B.TwoA.Sp8.Orth8Pairs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def cOrbit :
    Set Dfull := {y | ∃ x ∈ Xgrp, x * cQ * x⁻¹ = y}

theorem mem_cOrbit_iff
    {y : Dfull} : y ∈ cOrbit ↔ ∃ v : V8, qPoly v = 0 ∧ cQ * Psi v = y := by
  rw [cOrbit, orbit_cQ]
  rfl

theorem cOrbit_two_transitive
    {y₁ y₂ y₃ y₄ : Dfull} (h1 : y₁ ∈ cOrbit) (h2 : y₂ ∈ cOrbit)
    (h3 : y₃ ∈ cOrbit) (h4 : y₄ ∈ cOrbit) (h12 : y₁ ≠ y₂) (h34 : y₃ ≠ y₄) :
    ∃ x ∈ Xgrp, x * y₁ * x⁻¹ = y₃ ∧ x * y₂ * x⁻¹ = y₄ := by
  obtain ⟨v₁, hv₁, rfl⟩ := mem_cOrbit_iff.1 h1
  obtain ⟨v₂, hv₂, rfl⟩ := mem_cOrbit_iff.1 h2
  obtain ⟨v₃, hv₃, rfl⟩ := mem_cOrbit_iff.1 h3
  obtain ⟨v₄, hv₄, rfl⟩ := mem_cOrbit_iff.1 h4
  exact orbit_two_transitive hv₁ hv₂ (fun h => h12 (h ▸ rfl)) hv₃ hv₄ (fun h => h34 (h ▸ rfl))

theorem fix_cOrbit_iff
    (x : Xgrp) :
    (∀ y ∈ cOrbit, (x : Dfull) * y * (x : Dfull)⁻¹ = y) ↔ (x : Dfull) ∈ Lgrp := by
  rw [← fix_orbit_iff]
  constructor
  · intro h v hv
    exact h _ (mem_cOrbit_iff.2 ⟨v, hv, rfl⟩)
  · intro h y hy
    obtain ⟨v, hv, rfl⟩ := mem_cOrbit_iff.1 hy
    exact h v hv

theorem short_orthogonal_eight_centralizer :
    Function.Surjective rhoXSp ∧ rhoXSp.ker = Lgrp.subgroupOf Xgrp ∧
    (P4.subgroupOf Xgrp).map rhoX = TauCeti.QuadraticMap.orthogonalGroup qForm ∧
    p4Proj.ker = Lgrp.subgroupOf P4 ∧
    Nonempty (TauCeti.QuadraticMap.orthogonalGroup qForm ≃*
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1)) ∧
    Nonempty (P4 ⧸ Lgrp.subgroupOf P4 ≃*
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1)) ∧
    (P4.subgroupOf Xgrp).index = 120 ∧ Nat.card P4 = 13247740725166080 ∧
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1)) = 394813440 ∧
    (∀ y₁ ∈ cOrbit, ∀ y₂ ∈ cOrbit, ∀ y₃ ∈ cOrbit, ∀ y₄ ∈ cOrbit, y₁ ≠ y₂ → y₃ ≠ y₄ →
      ∃ x ∈ Xgrp, x * y₁ * x⁻¹ = y₃ ∧ x * y₂ * x⁻¹ = y₄) ∧
    (∀ x : Xgrp, (∀ y ∈ cOrbit, (x : Dfull) * y * (x : Dfull)⁻¹ = y) ↔ (x : Dfull) ∈ Lgrp) ∧
    cOrbit = (fun v => cQ * Psi v) '' {v : V8 | qPoly v = 0} ∧
    minusForms = qv '' {v : V8 | qPoly v = 0} ∧ minusForms.ncard = 120 ∧
    Function.Injective qv ∧
    (∀ (x : Xgrp) (v w : V8), qPoly v = 0 →
      (x : Dfull) * (cQ * Psi v) * (x : Dfull)⁻¹ = cQ * Psi w →
        qv w = (qv v).comp (rhoX x).symm.toLinearMap) :=
  ⟨rhoXSp_surjective, ker_rhoXSp, map_P4, ker_p4Proj, ⟨orthMinusEquiv⟩,
    ⟨p4QuotEquiv.trans orthMinusEquiv⟩, index_P4, natCard_P4, natCard_orthMinus,
    fun _ h1 _ h2 _ h3 _ h4 h12 h34 => cOrbit_two_transitive h1 h2 h3 h4 h12 h34, fix_cOrbit_iff,
    orbit_cQ, minusForms_eq, ncard_minusForms, qv_injective, fun x _ _ hv h => qv_conj x hv h⟩

end CFSG.Monster.B.TwoA.Sp8
