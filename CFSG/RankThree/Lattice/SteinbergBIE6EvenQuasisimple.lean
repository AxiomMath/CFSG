module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBridge
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups
open scoped Pointwise

namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)

theorem simpleOrbit_i₀_mem_orbits : D.simpleOrbit D.i₀ ∈ D.orbits := by
  refine ⟨D.i₀, ?_, rfl⟩
  exact D.mem_support_iff_component.2 (Or.inl Relation.ReflTransGen.refl)

theorem three_lt_card_orbitField {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) :
    3 < Nat.card (D.orbitField O) := by
  have hO' := D.mem_gen_orbits.2 hO
  have h := D.gen.card_orbitField hO'
  have hd := D.gen.orbitCard_pos hO'
  rw [show D.gen.orbitField O = D.orbitField O from rfl] at h
  rw [h]
  have hq : 4 ≤ D.gen.q := by
    rw [GenFixedRootDatum.q, D.gen_e]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ D.f := Nat.pow_le_pow_right (by norm_num) D.two_le_f
  calc 3 < 4 := by norm_num
    _ ≤ D.gen.q := hq
    _ = D.gen.q ^ 1 := (pow_one _).symm
    _ ≤ D.gen.q ^ GenFixedRootDatum.orbitCard O :=
      Nat.pow_le_pow_right (by omega) hd

theorem isPerfect_orbitGroup : Group.IsPerfect D.orbitGroup := by
  have h := D.gen.isPerfect_orbitGroup_of_card fun O hO =>
    D.three_lt_card_orbitField (D.mem_gen_orbits.1 hO)
  rwa [D.gen_orbitGroup] at h

theorem finite_orbitGroup : Finite D.orbitGroup := by
  have h := D.gen.finite_orbitGroup
  rwa [D.gen_orbitGroup] at h

theorem isQuasisimple_orbitGroup : CFSG.IsQuasisimple D.orbitGroup := by
  have h := D.gen.isQuasisimple_orbitGroup_of_isPerfect
    (D.mem_gen_orbits.2 D.simpleOrbit_i₀_mem_orbits) (by
      rw [D.gen_orbitGroup]
      exact D.isPerfect_orbitGroup)
  rwa [D.gen_orbitGroup] at h

end E6EvenFixedRootDatum

end CFSG.RankThree.Lattice
