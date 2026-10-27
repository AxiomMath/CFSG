module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase

public section

namespace CFSG.Quasithin.H13.F431.D4q.StdLoc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.Quasithin.H13.F431.D4q.Loc CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Defs

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] noncomputable def La : Subgroup (Cm σ) :=
  (d4Ma K σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

end Defs

section Basic

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

@[expose] noncomputable def x2C : Cm σ :=
  ⟨d4x₂ K 1, (d4x_long_mem σ (map_one σ)).1⟩

@[expose] noncomputable def x5C : Cm σ :=
  ⟨d4x₅ K 1, (d4x_long_mem σ (map_one σ)).2.1⟩

theorem x2C_mem_La : x2C σ ∈ La σ := d4x₂_mem_d4Ma σ (map_one σ)

theorem comm_zC_tC (hσ : ∀ c, σ (σ (σ c)) = c) : zC σ * tC σ hσ = tC σ hσ * zC σ :=
  Subtype.ext (commute_d4x₄_d4x₆ σ 1 1).symm.eq

theorem La_le_cent_tC (hσ : ∀ c, σ (σ (σ c)) = c) :
    La σ ≤ Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) := fun g hg => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tC σ hσ]
  exact (d4Ma_commute_d4x₄ σ _ hg 1).symm

end Basic

section SL2

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) {f : ℕ} (hf : 2 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ c = c ^ 2 ^ f)

include hK hσq in
theorem card_orbitField_one (hf1 : 1 ≤ f) :
    Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) = 2 ^ f := by
  have hσ := ringEquiv_cube_d4 σ (sigma_cube_of_card_d4 σ hK hσq)
  have hk : Nat.card (d4k K σ) = 2 ^ f := card_d4k_of_card σ hf1 hK hσq
  obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ
  rw [hL2]
  exact hk

include hf hK hσq in
theorem La_facts : commutator ↥(La σ) = ⊤ ∧ IsSimpleGroup ↥(La σ) := by
  have hσ := ringEquiv_cube_d4 σ (sigma_cube_of_card_d4 σ hK hσq)
  have hcard := card_orbitField_one σ hK hσq (by omega)
  have h4 : 4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) := Subtype.finite
  obtain ⟨hperf, hsimp, -⟩ := sl2_facts_d4
    ((Subgroup.subgroupOfEquivOfLe (d4Ma_le σ hσ)).trans (d4MaEquiv σ hσ)) h4
  exact ⟨hperf, hsimp⟩

include hf hK hσq in
theorem not_isSolvable_La : ¬ Group.IsSolvable ↥(La σ) := by
  obtain ⟨hperf, hsimp⟩ := La_facts σ hf hK hσq
  have : Nontrivial ↥(La σ) := hsimp.toNontrivial
  have : Group.IsPerfect ↥(La σ) := ⟨hperf⟩
  exact Group.IsPerfect.not_isSolvable ↥(La σ)

theorem normal_centralizer_subgroupOf {G : Type*} [Group G] {X V : Subgroup G}
    (hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V) :
    ((Subgroup.centralizer (V : Set G)).subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
  intro v hv
  have hv' : (g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹ ∈ V := hVn _ (X.inv_mem g.2) v hv
  have h := hn _ hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc v * ((g : G) * (n : G) * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹) * (n : G)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((n : G) * ((g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹)) * (g : G)⁻¹ := by rw [h]
    _ = (g : G) * (n : G) * (g : G)⁻¹ * v := by group

include hf hK hσq in
theorem isSolvable_La_inf_cent {V : Subgroup (Cm σ)}
    (hN : ∀ l ∈ La σ, ∀ v ∈ V, l * v * l⁻¹ ∈ V) (hx5 : x5C σ ∈ V) :
    Group.IsSolvable ↥(La σ ⊓ Subgroup.centralizer (V : Set (Cm σ))) := by
  obtain ⟨-, hsimp⟩ := La_facts σ hf hK hσq
  have hnorm : ((Subgroup.centralizer (V : Set (Cm σ))).subgroupOf (La σ)).Normal :=
    normal_centralizer_subgroupOf hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Subgroup.centralizer (V : Set (Cm σ))).subgroupOf (La σ)) with h | h
  · refine Group.isSolvable_of_comm (fun a b => ?_)
    have ha : (⟨a.1, a.2.1⟩ : ↥(La σ)) ∈
        (Subgroup.centralizer (V : Set (Cm σ))).subgroupOf (La σ) := a.2.2
    rw [h, Subgroup.mem_bot] at ha
    have ha1 : (⟨a.1, a.2.1⟩ : ↥(La σ)).1 = (1 : ↥(La σ)).1 := congrArg Subtype.val ha
    have ha2 : a = 1 := Subtype.ext ha1
    rw [ha2, one_mul, mul_one]
  · exfalso
    have h1 : (⟨x2C σ, x2C_mem_La σ⟩ : ↥(La σ)) ∈
        (Subgroup.centralizer (V : Set (Cm σ))).subgroupOf (La σ) := h ▸ Subgroup.mem_top _
    have h2 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 h1) (x5C σ) hx5
    have h3 : ⁅d4x₅ K 1, d4x₂ K 1⁆ = 1 := by
      refine commutatorElement_eq_one_iff_mul_comm.2 ?_
      exact congrArg Subtype.val h2
    rw [comm_d4x₅_d4x₂, mul_one] at h3
    exact zC_ne_one σ (Subtype.ext h3)

end SL2

end CFSG.Quasithin.H13.F431.D4q.StdLoc
