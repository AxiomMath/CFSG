module

public import CFSG.Monster.Existence.ELevelBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

@[expose] noncomputable def uC : Cgen :=
  ⟨uStar, rhoEquiv_mem_Cgen (DQ_mem_centralizer (deltaPair 0 2))⟩

@[expose] noncomputable def uBar : Cbar := kappa uC

@[expose] noncomputable def uA : CfullA := inclGenA uC

@[expose] noncomputable def uHatA : DA := iotaA uBar

theorem uHatA_eq : uHatA = piA uA := rfl

theorem centralizer_uHatA_le_range
    (hNF : ∀ c : CfullA, (c * uA * c⁻¹ = uA ∨ c * uA * c⁻¹ = uA * tStarA) →
      (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen) :
    Subgroup.centralizer {uHatA} ≤ iotaA.range := by
  intro y hy
  obtain ⟨c, rfl⟩ := piA_surjective y
  rw [Subgroup.mem_centralizer_singleton_iff, uHatA_eq] at hy
  have h1 : piA ((c * uA * c⁻¹) * uA⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy]
    group
  rcases (piA_eq_one_iff _).1 h1 with h | h
  · have hcu : c * uA * c⁻¹ = uA := mul_inv_eq_one.1 h
    exact ⟨kappa ⟨c, hNF c (Or.inl hcu)⟩, rfl⟩
  · have hcu : c * uA * c⁻¹ = tStarA * uA := mul_inv_eq_iff_eq_mul.1 h
    have hcomm : tStarA * uA = uA * tStarA :=
      (Subgroup.mem_center_iff.1 tStarA_mem_center uA).symm
    exact ⟨kappa ⟨c, hNF c (Or.inr (hcu.trans hcomm))⟩, rfl⟩

theorem centralizer_uHatA_eq_map
    (hNF : ∀ c : CfullA, (c * uA * c⁻¹ = uA ∨ c * uA * c⁻¹ = uA * tStarA) →
      (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen) :
    Subgroup.centralizer {uHatA} = (Subgroup.centralizer {uBar}).map iotaA := by
  apply le_antisymm
  · intro y hy
    obtain ⟨b, rfl⟩ := centralizer_uHatA_le_range hNF hy
    refine ⟨b, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply iotaA_injective
    rw [map_mul, map_mul]
    exact hy
  · rintro _ ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [uHatA, ← map_mul, ← map_mul, hb]

noncomputable def centralizerUHatEquiv
    (hNF : ∀ c : CfullA, (c * uA * c⁻¹ = uA ∨ c * uA * c⁻¹ = uA * tStarA) →
      (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen) :
    Subgroup.centralizer {uHatA} ≃* Subgroup.centralizer {uBar} :=
  (MulEquiv.subgroupCongr (centralizer_uHatA_eq_map hNF)).trans
    ((Subgroup.equivMapOfInjective _ iotaA iotaA_injective).symm)

noncomputable def centralizerMulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (a : X) :
    Subgroup.centralizer {a} ≃* Subgroup.centralizer {φ a} :=
  (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
        MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hb]
      · intro hy
        refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
        apply φ.injective
        rw [map_mul, map_mul, φ.apply_symm_apply, hy]))

theorem uA_mul_self : uA * uA = 1 :=
  Subtype.ext (rhoEquiv_mul_self_DQ (deltaPair 0 2))

theorem uC_mul_self : uC * uC = 1 :=
  Subtype.ext (rhoEquiv_mul_self_DQ (deltaPair 0 2))

theorem uBar_ne_one : uBar ≠ 1 := by
  intro h
  rcases (kappa_eq_one_iff uC).1 h with h1 | h1
  · have h2 : rhoEquiv rTwo = rhoEquiv 1 :=
      (congrArg Subtype.val h1).trans Short.rhoEquiv_one.symm
    exact ne_one_of_isShortCoord isShortCoord_rTwo (rhoEquiv_injective h2)
  · have h2 : uStar = tStar := congrArg Subtype.val h1
    have h3 : rhoEquiv rOneTwo = rhoEquiv 1 := by
      rw [← uStar_mul_tStar, h2, Short.rhoEquiv_one]
      exact rhoEquiv_mul_self_DQ (deltaPair 0 1)
    exact ne_one_of_isShortCoord isShortCoord_rOneTwo (rhoEquiv_injective h3)

theorem orderOf_uBar : orderOf uBar = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ uBar_ne_one
  rw [sq, uBar, ← map_mul, uC_mul_self, map_one]

theorem orderOf_uHatA : orderOf uHatA = 2 := by
  rw [uHatA, orderOf_injective iotaA iotaA_injective]
  exact orderOf_uBar

theorem nonempty_DA_equiv_B_of
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B))
    (hNF : ∀ c : CfullA, (c * uA * c⁻¹ = uA ∨ c * uA * c⁻¹ = uA * tStarA) →
      (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen)
    (φ : Cbar ≃* Blueprint.NativeSporadic.B)
    (hφ : Matrix.rank ((φ uBar).val.val - 1) = 1860) :
    Nonempty (DA ≃* Blueprint.NativeSporadic.B) := by
  have : IsSimpleGroup DA := isSimpleGroup_DA
  have hφo : orderOf (φ uBar) = 2 :=
    (@MulEquiv.orderOf_eq _ _ _ Units.instMonoid φ uBar).trans orderOf_uBar
  refine hStroth (φ uBar) hφo hφ DA uHatA orderOf_uHatA ?_
  exact ⟨(centralizerUHatEquiv hNF).trans
    (@centralizerMulEquiv Cbar Blueprint.NativeSporadic.B _ Units.instGroup φ uBar)⟩

end CFSG.Monster.Existence
