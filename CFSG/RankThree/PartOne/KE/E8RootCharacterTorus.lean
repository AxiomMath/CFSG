module

public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

@[expose] def cartanInvE8 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

theorem cartanInvE8_mul : cartanInvE8 * Tag.E8.cartan = 1 := by
  decide +kernel

theorem rootDiagUnit_E8_mem_torusGroup {M : Type} [Field M] (a : Fin Tag.E8.rank → Mˣ) :
    rootDiagUnit Tag.E8 a ∈ torusGroup Tag.E8 M := by
  rw [rootDiagUnit_eq_list_prod_torusElt (K := M) cartanInvE8_mul a]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_torusGroup i _

theorem rootDiagUnit_E8_mem_adjointGroup {M : Type} [Field M] (a : Fin Tag.E8.rank → Mˣ) :
    rootDiagUnit Tag.E8 a ∈ adjointGroup Tag.E8 M := by
  rw [rootDiagUnit_eq_list_prod_torusElt (K := M) cartanInvE8_mul a]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_adjointGroup i _

theorem E8_root_character_torus_mulEquiv (M : Type) [Field M] :
    ∃ e : (Fin Tag.E8.rank → Mˣ) ≃* ↥(torusGroup Tag.E8 M),
      ∀ a, ((e a : ↥(torusGroup Tag.E8 M)) : ModGL Tag.E8 M) = rootDiagUnit Tag.E8 a := by
  let f : (Fin Tag.E8.rank → Mˣ) →* ↥(torusGroup Tag.E8 M) :=
    (rootDiagUnitHom Tag.E8 M).codRestrict (torusGroup Tag.E8 M) fun a =>
      rootDiagUnit_E8_mem_torusGroup a
  have hbij : Function.Bijective f := by
    refine ⟨fun a b hab => rootDiagUnit_injective (congrArg Subtype.val hab), fun h => ?_⟩
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup h.2
    exact ⟨a, Subtype.ext ha.symm⟩
  exact ⟨MulEquiv.ofBijective f hbij, fun a => rfl⟩

theorem E8_entrywiseFixedGroup_eq_fixedFieldImage (M : Type) [Field M] [Finite M]
    (σ : M ≃+* M) : entrywiseFixedGroup Tag.E8 σ = fixedFieldImage Tag.E8 σ := by
  refine le_antisymm ?_ fixedFieldImage_le
  intro g hg
  have hmul : g ∈ (entrywiseFixedTorus Tag.E8 σ : Set (ModGL Tag.E8 M)) *
      (fixedFieldImage Tag.E8 σ : Set (ModGL Tag.E8 M)) := by
    rw [← coe_entrywiseFixedGroup_eq_mul]
    exact hg
  obtain ⟨h, hh, j, hj, rfl⟩ := hmul
  refine mul_mem ?_ hj
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hσa : ∀ i, σ (a i : M) = a i := by
    have hF' : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E8 a) =
        rootDiagUnit Tag.E8 a := (Subgroup.mem_inf.1 hhΓ).2
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E8 a) =
        rootDiagUnit Tag.E8 (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom a)
    have h1 := rootDiagUnit_injective (h0.symm.trans hF')
    intro i
    exact congrArg Units.val (congrFun h1 i)
  let a' : Fin Tag.E8.rank → (fixSubfield σ)ˣ := fun i =>
    Units.mk0 (⟨(a i : M), hσa i⟩ : fixSubfield σ) (fun h0 => (a i).ne_zero
      (congrArg Subtype.val h0))
  have ha' : (fun i => Units.map (fixSubfield σ).subtype.toMonoidHom (a' i)) = a := by
    funext i
    exact Units.ext rfl
  refine ⟨rootDiagUnit Tag.E8 a', ?_, ?_⟩
  · exact rootDiagUnit_E8_mem_adjointGroup a'
  · rw [baseChangeGL_rootDiagUnit, ha']

end CFSG.RankThree.PartOne.KE
