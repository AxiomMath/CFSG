module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
public import Mathlib.RepresentationTheory.Submodule
import Mathlib.Algebra.Field.ZMod
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

/-!
# Invariant complements for odd-order actions over `ZMod 2`
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

/-- Maschke complement for a finite odd-order group acting linearly over
`ZMod 2`. -/
public theorem exists_isCompl_invariant_of_odd_group
    {A V : Type*} [Group A] [Fintype A]
    [AddCommGroup V] [Module (ZMod 2) V]
    (hAodd : Odd (Fintype.card A))
    (rho : Representation (ZMod 2) A V)
    (U : Submodule (ZMod 2) V)
    (hU : ∀ a : A, ∀ v ∈ U, rho a v ∈ U) :
    ∃ W, IsCompl U W ∧ ∀ a : A, ∀ v ∈ W, rho a v ∈ W := by
  classical
  have hUinv : U ∈ rho.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact hU a
  let Upack : rho.invtSubmodule := ⟨U, hUinv⟩
  let instAdd : AddCommGroup rho.asModule :=
    Representation.instAddCommGroupAsModule rho
  let _ : AddCommGroup rho.asModule := instAdd
  let instMod : Module (MonoidAlgebra (ZMod 2) A) rho.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rho
  let _ : Module (MonoidAlgebra (ZMod 2) A) rho.asModule := instMod
  have : NeZero (Fintype.card A : ZMod 2) := by
    constructor
    intro hzero
    have hdiv : 2 ∣ Fintype.card A :=
      (ZMod.natCast_eq_zero_iff (Fintype.card A) 2).1 hzero
    exact hAodd.not_two_dvd_nat hdiv
  let Umod : @Submodule (MonoidAlgebra (ZMod 2) A) rho.asModule _
      instAdd.toAddCommMonoid instMod :=
    rho.mapSubmodule Upack
  obtain ⟨Wmod, hUWmod⟩ := @MonoidAlgebra.Submodule.exists_isCompl'
    (ZMod 2) inferInstance A inferInstance inferInstance rho.asModule
      instAdd instMod inferInstance Umod
  let Wpack : rho.invtSubmodule := rho.mapSubmodule.symm Wmod
  let W : Submodule (ZMod 2) V := Wpack
  refine ⟨W, ?_, ?_⟩
  · have hcompl_pack : IsCompl Upack Wpack := by
      exact (rho.mapSubmodule.isCompl_iff).2
        (by simpa [Umod, Wpack] using hUWmod)
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    constructor
    · simpa [Upack, W] using congrArg Subtype.val hcompl_pack.1
    · simpa [Upack, W] using congrArg Subtype.val hcompl_pack.2
  · intro a v hv
    have hmem := (Representation.mem_invtSubmodule (ρ := rho)).1 Wpack.2 a
    exact
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (rho a)).1 hmem v
        (by simpa [W] using hv)

/-- Maschke complement, transported from `ZMod 2` submodules back to
subgroups of an elementary abelian `2`-group. -/
public theorem exists_isCompl_invariant_subgroup_of_odd_group
    {A G : Type*} [Group A] [Fintype A]
    [Group G] [IsElementaryAbelian 2 G] [MulDistribMulAction A G]
    (hAodd : Odd (Fintype.card A))
    (U : Subgroup G)
    (hU : ∀ a : A, ∀ g : G, g ∈ U → a • g ∈ U) :
    ∃ W : Subgroup G, IsCompl U W ∧
      ∀ a : A, ∀ g : G, g ∈ W → a • g ∈ W := by
  classical
  let e : Subgroup G ≃o Submodule (ZMod 2) (Additive G) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := 2))
  let rho :=
    Theory.Representation.ofElementaryAbelianAction (A := A) (G := G) (p := 2)
  have hUmod : ∀ a : A, ∀ v ∈ e U, rho a v ∈ e U := by
    intro a v hv
    change Additive.toMul v ∈ U at hv
    change Additive.toMul (rho a v) ∈ U
    simpa [rho] using hU a (Additive.toMul v) hv
  obtain ⟨Wmod, hUWmod, hWmod⟩ :=
    exists_isCompl_invariant_of_odd_group hAodd rho (e U) hUmod
  let W : Subgroup G := e.symm Wmod
  refine ⟨W, ?_, ?_⟩
  · apply e.isCompl_iff.mpr
    simpa [W] using hUWmod
  · intro a g hg
    have hgmod : Additive.ofMul g ∈ Wmod := by
      simpa [W, e] using hg
    have hsmul := hWmod a (Additive.ofMul g) hgmod
    simpa [W, e, rho] using hsmul
/-- An invariant subgroup of an elementary abelian `2`-group has an invariant
complement inside any larger invariant subgroup. -/
public theorem exists_isCompl_invariant_subgroup_within
    {A G : Type*} [Group A] [Fintype A]
    [Group G] [IsElementaryAbelian 2 G] [MulDistribMulAction A G]
    (hAodd : Odd (Fintype.card A))
    (U V : Subgroup G) (hVU : V ≤ U)
    (hU : ∀ a : A, ∀ g : G, g ∈ U → a • g ∈ U)
    (hV : ∀ a : A, ∀ g : G, g ∈ V → a • g ∈ V) :
    ∃ W : Subgroup G, W ≤ U ∧
      (∀ a : A, ∀ g : G, g ∈ W → a • g ∈ W) ∧
      V ⊓ W = ⊥ ∧ V ⊔ W = U := by
  classical
  let _ : IsInvariant A G U := ⟨by
    intro a g
    constructor
    · exact hU a g
    · intro hg
      have hback := hU a⁻¹ (a • g) hg
      simpa [smul_smul] using hback⟩
  let _ : IsInvariant A G V := ⟨by
    intro a g
    constructor
    · exact hV a g
    · intro hg
      have hback := hV a⁻¹ (a • g) hg
      simpa [smul_smul] using hback⟩
  let VU : Subgroup U := V.subgroupOf U
  let _ : IsInvariant A U VU := by
    dsimp [VU]
    exact isInvariant_subgroupOf V U
  let _ : IsElementaryAbelian 2 U := by
    refine
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_ }
    intro u
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 G) u
  obtain ⟨WU, hVWU, hWU_forward⟩ :=
    exists_isCompl_invariant_subgroup_of_odd_group hAodd VU (by
      intro a u hu
      exact (IsInvariant.invariant (A := A) (G := U) (H := VU) a u).1 hu)
  let _ : IsInvariant A U WU := ⟨by
    intro a u
    constructor
    · exact hWU_forward a u
    · intro hu
      have hback := hWU_forward a⁻¹ (a • u) hu
      simpa [smul_smul] using hback⟩
  let W : Subgroup G := WU.map U.subtype
  have hVU_map : VU.map U.subtype = V := by
    dsimp [VU]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVU]
  have hWU_map : WU.map U.subtype = W := rfl
  have hmap_top : (⊤ : Subgroup U).map U.subtype = U := by
    ext g
    constructor
    · rintro ⟨u, _hu, rfl⟩
      exact u.property
    · intro hg
      exact ⟨⟨g, hg⟩, trivial, rfl⟩
  refine ⟨W, Subgroup.map_subtype_le WU, ?_, ?_, ?_⟩
  · intro a g hg
    exact (isInvariant_map_subtype U WU).invariant a g |>.mp hg
  · have hinf : VU ⊓ WU = ⊥ := disjoint_iff.mp hVWU.1
    calc
      V ⊓ W = VU.map U.subtype ⊓ WU.map U.subtype := by
        rw [hVU_map, hWU_map]
      _ = (VU ⊓ WU).map U.subtype :=
        (Subgroup.map_inf_eq VU WU U.subtype U.subtype_injective).symm
      _ = ⊥ := by rw [hinf]; simp
  · have hsup : VU ⊔ WU = ⊤ := codisjoint_iff.mp hVWU.2
    calc
      V ⊔ W = VU.map U.subtype ⊔ WU.map U.subtype := by
        rw [hVU_map, hWU_map]
      _ = (VU ⊔ WU).map U.subtype := by rw [Subgroup.map_sup]
      _ = U := by rw [hsup, hmap_top]
end Higman
end External
end CFSG.BenderSuzuki
