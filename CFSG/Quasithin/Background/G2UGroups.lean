module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
public import Certificates.Certificate8064

public section

namespace CFSG.Quasithin.G2U

open Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem card_rootGroup : Nat.card rootGroup = 12096 :=
  Certificates.certificate8064.1

theorem card_graphD : Nat.card graphD = 6048 :=
  Certificates.certificate8064.2.1

theorem graphD_snd_eq_one
    {g : GL (Fin 14) (ZMod 2) × GL (Fin 3) F9} (hg : g ∈ graphD)
    (h : g.1 = 1) : g.2 = 1 :=
  Certificates.certificate8064.2.2.1 g hg h

theorem graphD_fst_eq_one
    {g : GL (Fin 14) (ZMod 2) × GL (Fin 3) F9} (hg : g ∈ graphD)
    (h : g.2 = 1) : g.1 = 1 :=
  Certificates.certificate8064.2.2.2 g hg h

theorem map_fst_graphD : graphD.map (MonoidHom.fst _ _) = derivedJ := by
  rw [graphD, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem map_snd_graphD : graphD.map (MonoidHom.snd _ _) = unitaryS := by
  rw [graphD, MonoidHom.map_closure, Set.image_pair]
  rfl

noncomputable def graphDEquivJ : graphD ≃* derivedJ :=
  (MulEquiv.ofBijective ((MonoidHom.fst _ _).subgroupMap graphD)
    ⟨(injective_iff_map_eq_one _).mpr fun x hx => by
      have h1 : x.1.1 = 1 := congrArg Subtype.val hx
      exact Subtype.ext (Prod.ext h1 (graphD_snd_eq_one x.2 h1)),
      MonoidHom.subgroupMap_surjective _ _⟩).trans (MulEquiv.subgroupCongr map_fst_graphD)

noncomputable def graphDEquivS : graphD ≃* unitaryS :=
  (MulEquiv.ofBijective ((MonoidHom.snd _ _).subgroupMap graphD)
    ⟨(injective_iff_map_eq_one _).mpr fun x hx => by
      have h2 : x.1.2 = 1 := congrArg Subtype.val hx
      exact Subtype.ext (Prod.ext (graphD_fst_eq_one x.2 h2) h2),
      MonoidHom.subgroupMap_surjective _ _⟩).trans (MulEquiv.subgroupCongr map_snd_graphD)

theorem card_derivedJ : Nat.card derivedJ = 6048 :=
  (Nat.card_congr graphDEquivJ.toEquiv).symm.trans card_graphD

private theorem mem_statedSU_of_codes (m mi : List ℕ) (h1 : mul3 m mi = id3)
    (h2 : mul3 mi m = id3)
    (h : ((dec3 m).map (· ^ 3))ᵀ * dec3 m = 1 ∧ (dec3 m).det = 1) :
    unit3 m mi h1 h2 ∈ StatedSU 3 3 F9 := by
  rw [← SetLike.mem_coe, LinearGroups.UnitaryThreeOverNine.coe_statedSU card_F9]
  exact h

theorem unitaryS_eq : unitaryS = StatedSU 3 3 F9 := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [unitaryS, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact mem_statedSU_of_codes _ _ _ _ (by rw [Matrix.det_fin_three]; decide)
    · exact mem_statedSU_of_codes _ _ _ _ (by rw [Matrix.det_fin_three]; decide)
  · rw [LinearGroups.UnitaryThreeOverNine.card_statedSU card_F9,
      ← Nat.card_congr graphDEquivS.toEquiv, card_graphD]

noncomputable def derivedJEquiv : derivedJ ≃* StatedSU 3 3 F9 :=
  (graphDEquivJ.symm.trans graphDEquivS).trans (MulEquiv.subgroupCongr unitaryS_eq)

theorem gen_mem_rootGroup : gen0 ∈ rootGroup ∧ gen1 ∈ rootGroup ∧ gen2 ∈ rootGroup ∧
    gen3 ∈ rootGroup :=
  ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩

theorem cU_eq : cU = ⁅gen0, gen1⁆ := by
  rw [commutatorElement_def, gen0, gen1, invol_inv, invol_inv, cU, pow_two, ← gen0, ← gen1]
  group

theorem dU_eq : dU = ⁅gen2, gen3⁆ := by
  rw [commutatorElement_def, gen2, gen3, invol_inv, invol_inv, dU, pow_two, ← gen2, ← gen3]
  group

theorem derivedJ_le_commutator : derivedJ ≤ ⁅rootGroup, rootGroup⁆ := by
  obtain ⟨h0, h1, h2, h3⟩ := gen_mem_rootGroup
  have hc : cU ∈ ⁅rootGroup, rootGroup⁆ := by
    rw [cU_eq]
    exact Subgroup.commutator_mem_commutator h0 h1
  have hd : dU ∈ ⁅rootGroup, rootGroup⁆ := by
    rw [dU_eq]
    exact Subgroup.commutator_mem_commutator h2 h3
  rw [derivedJ, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact pow_mem hc 2
  · exact mul_mem (pow_mem hc 3) hd

theorem derivedJ_le_rootGroup : derivedJ ≤ rootGroup :=
  derivedJ_le_commutator.trans (Subgroup.commutator_le_self _)

private theorem commutator_eq_squares {G : Type*} [Group G] (x y : G) :
    ⁅x, y⁆ = (x * y) * (x * y) * ((y⁻¹ * x⁻¹ * y) * (y⁻¹ * x⁻¹ * y)) * (y⁻¹ * y⁻¹) := by
  rw [commutatorElement_def]
  group

theorem index_derivedJ
    : (derivedJ.subgroupOf rootGroup).index = 2 := by
  have h := Subgroup.card_mul_index (derivedJ.subgroupOf rootGroup)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe derivedJ_le_rootGroup).toEquiv,
    card_derivedJ, card_rootGroup] at h
  omega

theorem commutator_rootGroup_le
    : ⁅rootGroup, rootGroup⁆ ≤ derivedJ := by
  set H := derivedJ.subgroupOf rootGroup
  have hsq : ∀ x : rootGroup, x * x ∈ H := Subgroup.mul_self_mem_of_index_two index_derivedJ
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  have hmem : ⁅(⟨g, hg⟩ : rootGroup), ⟨g', hg'⟩⁆ ∈ H := by
    rw [commutator_eq_squares]
    exact mul_mem (mul_mem (hsq _) (hsq _)) (hsq _)
  exact Subgroup.mem_subgroupOf.mp hmem

theorem commutator_rootGroup_eq
    : ⁅rootGroup, rootGroup⁆ = derivedJ :=
  le_antisymm commutator_rootGroup_le derivedJ_le_commutator

noncomputable def commutatorRootGroupEquiv
    : ↥⁅rootGroup, rootGroup⁆ ≃* StatedSU 3 3 F9 :=
  (MulEquiv.subgroupCongr commutator_rootGroup_eq).trans derivedJEquiv

end CFSG.Quasithin.G2U
