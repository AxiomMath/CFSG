module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofRee
import CFSG.LieType.SteinbergBRParabolicResidualImage

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LieType.Ree

namespace ReeF4ThreeLocalProof

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem centralizer_conj_eq_map (g y : Γ) :
    Subgroup.centralizer ({g * y * g⁻¹} : Set Γ) =
      (Subgroup.centralizer ({y} : Set Γ)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    have h1 : (g⁻¹ * x * g) * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
    have h2 : y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
    rw [h1, h2, hx]
  · rintro ⟨u, hu, rfl⟩
    have h1 : g * u * g⁻¹ * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by group
    have h2 : g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
    rw [h1, h2, hu]

theorem inSubgroup_perfectResidual_centralizer_conj (g y : Γ) :
    inSubgroup perfectResidual (Subgroup.centralizer ({g * y * g⁻¹} : Set Γ)) =
      (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set Γ))).map
        (MulAut.conj g).toMonoidHom := by
  rw [centralizer_conj_eq_map]
  exact (CFSG.LieType.SteinbergBR.BlockPar.map_perfectResidual_subgroup _ _).symm

theorem isoSUThree_perfectResidual_centralizer_conj {q : ℕ} (g y : Γ)
    (h : IsoSUThree (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set Γ))) q) :
    IsoSUThree (inSubgroup perfectResidual (Subgroup.centralizer ({g * y * g⁻¹} : Set Γ))) q := by
  obtain ⟨F, hF, hFf, hFc, ⟨e⟩⟩ := h
  rw [inSubgroup_perfectResidual_centralizer_conj]
  exact ⟨F, hF, hFf, hFc, ⟨(Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩⟩

end ReeF4ThreeLocalProof

open ReeF4ThreeLocalProof


@[expose] def ReeF4OrderThreeConj : Prop :=
  ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], 1 ≤ a →
    Nat.card K = 2 ^ (2 * a + 1) → ∀ y y' : ReeTag.F4.reeGamma K a, orderOf y = 3 →
      orderOf y' = 3 → ∃ g : ReeTag.F4.reeGamma K a, g * y * g⁻¹ = y'

@[expose] def ReeF4CentThreeSome : Prop :=
  ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], 1 ≤ a →
    Nat.card K = 2 ^ (2 * a + 1) → ∃ y : ReeTag.F4.reeGamma K a, orderOf y = 3 ∧
      IsoSUThree (inSubgroup perfectResidual
        (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)))) (2 ^ (2 * a + 1))

theorem kF83ReeCentThree_of (h1 : ReeF4OrderThreeConj) (h2 : ReeF4CentThreeSome) :
    KF83ReeCentThree := by
  intro a K _ _ _ ha hK y hy
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨y₀, hy₀, hiso⟩ := h2 a K ha hK
  obtain ⟨g, rfl⟩ := h1 a K ha hK y₀ y hy₀ hy
  exact isoSUThree_perfectResidual_centralizer_conj g y₀ hiso

theorem kF83ReeF4_of_conj_some (h1 : ReeF4OrderThreeConj) (h2 : ReeF4CentThreeSome) :
    Item83Proof.KF83ReeF4 :=
  kF83ReeF4_of (kF83ReeCentThree_of h1 h2)

end CFSG.RankThree.PartTwo.Sec8
