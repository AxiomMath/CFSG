module

public import CFSG.Monster.B.Geometry.ChamberCoverAction

public section

namespace CFSG.Monster.B.Geometry

namespace ChamberSystem

variable {I C : Type*} {X : ChamberSystem I C} {c₀ : C}

theorem finite_liftPair [Finite (X.Cover c₀)] (hX : X.Connected) : Finite (X.LiftPair c₀) :=
  Finite.of_injective _ (liftPerm_injective (c₀ := c₀) hX)

theorem pi2_le_liftSubgroup (H : Subgroup X.typeAut) : X.pi2 c₀ ≤ X.liftSubgroup c₀ H := by
  intro z hz
  change X.liftProj c₀ z ∈ H
  rw [MonoidHom.mem_ker.mp hz]
  exact one_mem H

theorem ker_liftProj_subgroupComap (H : Subgroup X.typeAut) :
    ((X.liftProj c₀).subgroupComap H).ker = (X.pi2 c₀).subgroupOf (X.liftSubgroup c₀ H) := by
  ext z
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subtype.ext_iff]
  rfl

theorem nonempty_liftSubgroup_quotient_mulEquiv (hX : X.Connected) (H : Subgroup X.typeAut) :
    Nonempty (X.liftSubgroup c₀ H ⧸ (X.pi2 c₀).subgroupOf (X.liftSubgroup c₀ H) ≃* H) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_liftProj_subgroupComap H).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((X.liftProj c₀).subgroupComap_surjective H (liftProj_surjective hX)))⟩

theorem natCard_liftSubgroup (hX : X.Connected) (H : Subgroup X.typeAut) :
    Nat.card (X.liftSubgroup c₀ H) = Nat.card H * Nat.card (X.pi2 c₀) := by
  obtain ⟨e⟩ := nonempty_liftSubgroup_quotient_mulEquiv (c₀ := c₀) hX H
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((X.pi2 c₀).subgroupOf (X.liftSubgroup c₀ H)), Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pi2_le_liftSubgroup H)).toEquiv]

theorem exists_liftSubgroup_smul_eq (hX : X.Connected) (H : Subgroup X.typeAut)
    (htr : ∀ x y : C, ∃ h ∈ H, (h : Equiv.Perm C) x = y) (A A' : X.Cover c₀) :
    ∃ z ∈ X.liftSubgroup c₀ H, z • A = A' := by
  obtain ⟨h, hh, hhA⟩ := htr (X.coverProj c₀ A) (X.coverProj c₀ A')
  obtain ⟨u, rfl⟩ := liftProj_surjective (c₀ := c₀) hX h
  have hfib : X.coverProj c₀ (u • A) = X.coverProj c₀ A' := by
    rw [coverProj_smul]
    exact hhA
  obtain ⟨v, hv, hvu⟩ := exists_ker_smul_eq hfib
  refine ⟨v * u, ?_, by rw [mul_smul, hvu]⟩
  change X.liftProj c₀ (v * u) ∈ H
  rw [map_mul, MonoidHom.mem_ker.mp hv, one_mul]
  exact hh

theorem natCard_stabilizer_liftSubgroup (hX : X.Connected) (H : Subgroup X.typeAut)
    (a : X.Cover c₀) :
    Nat.card (MulAction.stabilizer (X.liftSubgroup c₀ H) a) =
      Nat.card (MulAction.stabilizer H (X.coverProj c₀ a)) := by
  have hb := bijOn_liftProj_stabilizer hX H (isResidueIso_empty (X.coverProj c₀) a)
  rw [residue_empty, residue_empty] at hb
  simp only [Set.image_singleton, Set.singleton_eq_singleton_iff] at hb
  have e1 : ↥(MulAction.stabilizer (X.liftSubgroup c₀ H) a) ≃
      ↥{z : X.LiftPair c₀ | z ∈ X.liftSubgroup c₀ H ∧ z • a = a} :=
    { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : ↥(MulAction.stabilizer H (X.coverProj c₀ a)) ≃
      ↥{h : X.typeAut | h ∈ H ∧ (h : Equiv.Perm C) (X.coverProj c₀ a) = X.coverProj c₀ a} :=
    { toFun := fun h => ⟨h.1.1, h.1.2, h.2⟩
      invFun := fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2]
  exact Nat.card_congr (hb.equiv _)

theorem natCard_liftSubgroup_eq [Finite (X.Cover c₀)] (hX : X.Connected) (H : Subgroup X.typeAut)
    (htr : ∀ x y : C, ∃ h ∈ H, (h : Equiv.Perm C) x = y) (c : C) :
    Nat.card (X.liftSubgroup c₀ H) =
      Nat.card (MulAction.stabilizer H c) * Nat.card (X.Cover c₀) := by
  obtain ⟨a, rfl⟩ := coverProj_surjective (c₀ := c₀) hX c
  have : MulAction.IsPretransitive (X.liftSubgroup c₀ H) (X.Cover c₀) :=
    ⟨fun A A' => by
      obtain ⟨z, hz, h⟩ := exists_liftSubgroup_smul_eq hX H htr A A'
      exact ⟨⟨z, hz⟩, h⟩⟩
  rw [← natCard_stabilizer_liftSubgroup hX H a,
    ← (MulAction.stabilizer (X.liftSubgroup c₀ H) a).card_mul_index,
    MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ]

end ChamberSystem

end CFSG.Monster.B.Geometry
