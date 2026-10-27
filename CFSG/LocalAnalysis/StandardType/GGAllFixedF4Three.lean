module

public import CFSG.LocalAnalysis.StandardType.GGAllFixedExceptionalToral
public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UF4
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved
public import CFSG.LieType.SeitzGeneration.ExcHighThree.RegularSolvable

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.StandardType.ExcFramesHalf
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.SeitzGeneration.ExcHighThree

section Certificates


theorem f4_three_adjoint_full_centralizer_solvable
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K ^ 2 - 1)
    (A : Subgroup (adjointGroup .F4 K))
    (hA : IsElemAbelian 3 A) (hcard : 3 ^ 3 ≤ Nat.card A)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup .F4 K))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup .F4 K))) := by
  classical
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Finite (adjointGroup .F4 K) := by
    have : Finite (ModGL .F4 K) := finite_modGL
    exact Subtype.finite
  let ι := (baseChangeGL (τ := .F4) (algebraMap K L)).comp (adjointGroup .F4 K).subtype
  have hι : Function.Injective ι :=
    (baseChangeGL_injective (algebraMap K L)).comp (adjointGroup .F4 K).subtype_injective
  by_cases hT : IsToralSubgroup .F4 L (A.map ι)
  · exact adjoint_full_toral_centralizer_solvable
      (Or.inl rfl) Nat.prime_three (by decide) h3 A hA.2 hT hNPC
  · have hlt : Nat.card A < 3 ^ 4 := by
      by_contra hn
      have hn' : 3 ^ 4 ≤ Nat.card A := by omega
      apply hT
      exact TableCRes.utoralAt_F4_three hn' K (A.map ι)
        (by
          rintro _ ⟨a, ha, rfl⟩
          exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ a.2)
        (hA.map ι) (Subgroup.card_map_of_injective hι)
    obtain ⟨k, hk⟩ :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_card_eq_of_isElemAbelian
        Nat.prime_three hA
    have hk3 : k = 3 := by
      have hlo : 3 ≤ k := (Nat.pow_le_pow_iff_right (by decide)).1 (hk ▸ hcard)
      have hhi : k < 4 := (Nat.pow_lt_pow_iff_right (by decide)).1 (hk ▸ hlt)
      omega
    have hc : Nat.card A = 3 ^ 3 := hk3 ▸ hk
    have hD : IsEmpty (LangPlaneData .F4 K A) := ⟨fun D => hT (by
      let cbar := baseChangeGL (τ := .F4) (algebraMap K L)
        (D.c : ModGL .F4 K)
      refine ⟨cbar⁻¹ * D.g0, ?_, ?_⟩
      · exact mul_mem
          ((adjointGroup .F4 L).inv_mem
            (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ D.c.2)) D.hg0C
      · rintro _ ⟨a, ha, rfl⟩
        have hm := diagMap_mem_torusGroup D ha
        rw [diagMap_apply] at hm
        convert hm using 1
        simp only [ι, MonoidHom.comp_apply, Subgroup.coe_mul, Subgroup.coe_inv,
          map_mul, map_inv, cbar]
        group
        rfl)⟩
    have hK3 : ¬ 3 ∣ Nat.card K := by
      intro hd
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨f, -, hf⟩ := FiniteField.card K 2
      rw [Nat.card_eq_fintype_card, hf] at hd
      exact (by decide : (3 : ℕ) ≠ 2)
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
          (Nat.prime_three.dvd_of_dvd_pow hd))
    obtain ⟨P, hPA, hPc⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_subgroup_card_sq_le Nat.prime_three hc
    obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three K hK3 P
        (fun x hx => hA.2 x (hPA hx)) hPc
    let D : LangPlaneData .F4 K P := ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩
    have hreg :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.not_kills_of_le_nonToral_F4
        hK3 hA hc hD hPA hPc D
    have : Group.IsSolvable ↥(Subgroup.centralizer (P : Set (adjointGroup .F4 K))) :=
      isSolvable_centralizer_of_regular D hreg
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (Subgroup.centralizer_le hPA))

theorem ggFixedSubgroup_isSolvable_of_recipe_F4Three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K ^ 2 - 1)
    (E : Subgroup (MulAut (TableBF4.RecipeGroup K)))
    (hEI : (E : Set (MulAut (TableBF4.RecipeGroup K))) ⊆ TableBF4.RecipeID K)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 3 ≤ Nat.card E)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have hinner : E ≤ (MulAut.conj : TableBF4.RecipeGroup K →*
      MulAut (TableBF4.RecipeGroup K)).range := fun a ha =>
    TableBF4.idImage_subset_inn K (hEI ha)
  let eR := TableBF4.recipeEquiv K
  let E' : Subgroup (MulAut (adjointGroup .F4 K)) := E.map (MulAut.congr eR).toMonoidHom
  have hE'range : E' ≤ (MulAut.conj : adjointGroup .F4 K →*
      MulAut (adjointGroup .F4 K)).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg⟩ := hinner ha
    refine ⟨eR g, ?_⟩
    rw [← hg]
    exact (mulAut_congr_conj eR g).symm
  let A : Subgroup (adjointGroup .F4 K) := E'.comap (MulAut.conj :
    adjointGroup .F4 K →* MulAut (adjointGroup .F4 K))
  have hconj : Function.Injective (MulAut.conj : adjointGroup .F4 K →*
      MulAut (adjointGroup .F4 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hAmap : A.map (MulAut.conj : adjointGroup .F4 K →*
      MulAut (adjointGroup .F4 K)) = E' := Subgroup.map_comap_eq_self hE'range
  have hA : IsElemAbelian 3 A := (hE.map (MulAut.congr eR).toMonoidHom).comap hconj
  have hAcard : 3 ^ 3 ≤ Nat.card A := by
    have h1 : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.congr eR).injective
    have h2 : Nat.card A = Nat.card E' := by
      rw [← hAmap]
      exact (Subgroup.card_map_of_injective hconj).symm
    rwa [h2, h1]
  have hfix : ggFixedSubgroup E' =
      Subgroup.centralizer (A : Set (adjointGroup .F4 K)) := by
    rw [← hAmap, ggFixedSubgroup_map_conj_eq_centralizer]
  have hmapFix : ggFixedSubgroup E' = (ggFixedSubgroup E).map eR.toMonoidHom :=
    ggFixedSubgroup_map_congr eR E
  let eF : ↥(ggFixedSubgroup E) ≃* ↥(ggFixedSubgroup E') :=
    ((ggFixedSubgroup E).equivMapOfInjective eR.toMonoidHom eR.injective).trans
      (MulEquiv.subgroupCongr hmapFix.symm)
  let C : Subgroup (adjointGroup .F4 K) :=
    Subgroup.centralizer (A : Set (adjointGroup .F4 K))
  let eC : ↥(ggFixedSubgroup E) ≃* ↥C :=
    eF.trans (MulEquiv.subgroupCongr hfix)
  have hNPC_C : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥C) :=
    CFSG.hasNormalPComplement_of_equiv 3 eC.commutatorCongr hNPC
  have hsolvC : Group.IsSolvable ↥C :=
    f4_three_adjoint_full_centralizer_solvable (K := K) h3 A hA hAcard hNPC_C
  have hsolvE' : Group.IsSolvable ↥(ggFixedSubgroup E') := by
    rw [hfix]
    exact hsolvC
  have : Group.IsSolvable ↥((ggFixedSubgroup E).map eR.toMonoidHom) := by
    rw [← hmapFix]
    exact hsolvE'
  exact Group.isSolvable_of_isSolvable_injective
    (f := eR.toMonoidHom.subgroupMap (ggFixedSubgroup E))
    (MonoidHom.subgroupMap_injective eR.toMonoidHom _ eR.injective)

theorem largeEvenLabelAll_F4Three_fullFixedSolvable
    {n : ℕ} (h3 : 3 ∣ (2 ^ n) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.F4, 0, n⟩ fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
        CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  change LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false Q at hQ
  refine recipeChevalley_and (P := fun R _ I _ =>
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
      IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
      CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E)) ?_ hQ
  intro K _ _ hK E hEI hE hcard hNPC
  have : CharP K 2 := charP_two_of_card hK
  have h3K : 3 ∣ Nat.card K ^ 2 - 1 := by
    rw [hK]
    exact h3
  exact ggFixedSubgroup_isSolvable_of_recipe_F4Three (K := K) h3K E hEI hE hcard hNPC

theorem isSolvable_inf_centralizer_of_F4Three_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      lab.tag = .F4 ∧ lab.rank = 0 ∧ p = 3 ∧ 3 ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian 3 (ggBeta (G := G) (L := X) θ hN).range ∧
        3 ^ 3 ≤ Nat.card (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .F4 ∧ lab.rank = 0 ∧ p = 3 ∧
      3 ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
      CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab hlab hs => by
      obtain ⟨htag, hrank, -, h3n⟩ := hs
      cases lab with
      | mk tag rank n =>
        cases htag
        cases hrank
        exact largeEvenLabelAll_F4Three_fullFixedSolvable (n := n) h3n)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hp3, -, hN, hEI, hE, hcard⟩, hrow⟩ := hP
  subst p
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE hcard
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

end Certificates

end CFSG.StandardType
