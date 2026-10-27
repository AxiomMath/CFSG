module

public import CFSG.LocalAnalysis.StandardType.GGAllFixedExceptionalToral
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
public import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof3
public import CFSG.LocalAnalysis.StandardType.GGAllFixedExceptionalRegular
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInj
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralCentHolds
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.LieType.Chevalley.E6Three.PositionCentralizer
public import CFSG.LieType.SpecialLinear.NormalizerLift.FieldGraph
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsNormal
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFacts
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bFrame
public import CFSG.Mathlib.GroupTheory.FiniteCentralizerImage
public import CFSG.Quasithin.H13.GoldschmidtC137H6Alg

public section
namespace CFSG.StandardType
open CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.ExcFramesHalf

theorem e6_three_nontoral_rank_four_inndiag_centralizer_commutative
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (A : Subgroup (ModGL .E6 K)) (hAI : A ≤ RecipeExcLang.inndiagGroup .E6 K)
    (hA : IsElemAbelian 3 A) (hcard : 3 ^ 4 ≤ Nat.card A)
    (hnt : ¬ IsToralSubgroup .E6 (AlgebraicClosure K)
      (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K))))) :
    IsMulCommutative ↥(RecipeExcLang.inndiagGroup .E6 K ⊓
      Subgroup.centralizer (A : Set (ModGL .E6 K))) := by
  classical
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Finite (ModGL .E6 K) := finite_modGL
  let ι := baseChangeGL (τ := .E6) (algebraMap K L)
  have hι : Function.Injective ι := baseChangeGL_injective (algebraMap K L)
  let E := A.map ι
  have hEadj : E ≤ adjointGroup .E6 L := by
    rintro _ ⟨a, ha, rfl⟩
    exact RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag _ (hAI ha)
  have hEab : IsElemAbelian 3 E := hA.map ι
  have hEcard : Nat.card E = Nat.card A := Subgroup.card_map_of_injective hι
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro hd
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hf] at hd
    exact (by decide : (3 : ℕ) ≠ 2)
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow hd))
  have hlt : Nat.card E < 3 ^ 5 := by
    by_contra h
    have h5 : 3 ^ 5 ≤ Nat.card E := by omega
    exact hnt (bigElemAbelianToralBar_E6_three K hK3 E hEadj
      (fun x hx y hy => hEab.comm hx hy) hEab.2 h5)
  obtain ⟨k, hk⟩ := hA.isPGroup.exists_card_eq
  have hk4 : k = 4 := by
    have hlo : 4 ≤ k := (Nat.pow_le_pow_iff_right (by decide)).1 (hk ▸ hcard)
    have hhi : k < 5 := (Nat.pow_lt_pow_iff_right (by decide)).1 (hk ▸ (hEcard ▸ hlt))
    omega
  have hcardE : Nat.card E = 3 ^ 4 := hEcard.trans (hk4 ▸ hk)
  obtain ⟨hcomm, -, -⟩ := ggL45E6NonToralThreeCent_holds K E hEadj hEab hnt hcardE
  let C := RecipeExcLang.inndiagGroup .E6 K ⊓
    Subgroup.centralizer (A : Set (ModGL .E6 K))
  have hCcomm : ∀ x y : C, x * y = y * x := by
    intro x y
    apply Subtype.ext
    apply hι
    change ι ((x : ModGL .E6 K) * (y : ModGL .E6 K)) =
      ι ((y : ModGL .E6 K) * (x : ModGL .E6 K))
    rw [map_mul, map_mul]
    have hx : ι (x : ModGL .E6 K) ∈ adjointGroup .E6 L :=
      RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag _ x.2.1
    have hy : ι (y : ModGL .E6 K) ∈ adjointGroup .E6 L :=
      RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag _ y.2.1
    apply hcomm _ hx _ hy
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ι ((Subgroup.mem_centralizer_iff.1 x.2.2 a ha).symm)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ι ((Subgroup.mem_centralizer_iff.1 y.2.2 a ha).symm)
  exact ⟨⟨hCcomm⟩⟩

section RankThree

theorem e6_three_rank_three_inndiag_full_centralizer_solvable
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K ^ 2 - 1)
    (A : Subgroup (ModGL .E6 K)) (hAI : A ≤ RecipeExcLang.inndiagGroup .E6 K)
    (hA : IsElemAbelian 3 A) (hcard : 3 ^ 3 ≤ Nat.card A)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(adjointGroup .E6 K ⊓
        Subgroup.centralizer (A : Set (ModGL .E6 K))))) :
    Group.IsSolvable ↥(adjointGroup .E6 K ⊓
      Subgroup.centralizer (A : Set (ModGL .E6 K))) := by
  classical
  by_cases hT : IsToralSubgroup .E6 (AlgebraicClosure K)
      (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
  · exact inndiag_full_toral_centralizer_solvable (Or.inr (Or.inl rfl))
      Nat.prime_three (by decide) h3 A hA.2 hT hNPC
  · by_cases h4 : 3 ^ 4 ≤ Nat.card A
    · have : IsMulCommutative ↥(RecipeExcLang.inndiagGroup .E6 K ⊓
          Subgroup.centralizer (A : Set (ModGL .E6 K))) :=
        e6_three_nontoral_rank_four_inndiag_centralizer_commutative A hAI hA h4 hT
      let C := adjointGroup .E6 K ⊓ Subgroup.centralizer (A : Set (ModGL .E6 K))
      let C' := RecipeExcLang.inndiagGroup .E6 K ⊓
        Subgroup.centralizer (A : Set (ModGL .E6 K))
      have hCC' : C ≤ C' := inf_le_inf RecipeExcLang.adjointGroup_le_inndiagGroup le_rfl
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hCC') (Subgroup.inclusion_injective hCC')
    · 
      have : Finite (ModGL .E6 K) := finite_modGL
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, hk⟩ := hA.isPGroup.exists_card_eq
      have hk3 : k = 3 := by
        have hlo : 3 ≤ k := (Nat.pow_le_pow_iff_right (by decide)).1 (hk ▸ hcard)
        have hhi : k < 4 := (Nat.pow_lt_pow_iff_right (by decide)).1 (hk ▸ lt_of_not_ge h4)
        omega
      have hcard3 : Nat.card A = 3 ^ 3 := hk3 ▸ hk
      exact CFSG.LieType.Chevalley.E6Three.PositionCentralizer.isSolvable_of_le_inndiag_centralizer_of_not_toral_three
        A hAI hA hcard3 hT _
        (inf_le_inf RecipeExcLang.adjointGroup_le_inndiagGroup le_rfl) hNPC

theorem ggFixedSubgroup_isSolvable_of_recipe_E6_three_rank_three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K ^ 2 - 1)
    (E : Subgroup (MulAut (TableBExc.RecipeGroup .E6 K)))
    (hEI : (E : Set (MulAut (TableBExc.RecipeGroup .E6 K))) ⊆ TableBExc.RecipeID .E6 K)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 3 ≤ Nat.card E)
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hKn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hKn
  let eR := TableBExc.recipeEquiv .E6 K
  let E' := E.map (MulAut.congr eR).toMonoidHom
  let ρ := RecipeExcLang.inndiagConj .E6 K
  have hρ : Function.Injective ρ :=
    RecipeExcLang.inndiagConj_injective_of_card_eq_two_pow hK
  have hErange : E' ≤ ρ.range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨w, hw⟩ := (E6ThreeModel.recipeID_iff_hatAut a).1 (hEI ha)
    refine ⟨⟨w, E6IDB.mem_hatGroup_iff_mem_inndiagGroup.1 w.2⟩, ?_⟩
    exact (E6IDB.hatAut_eq_inndiagConj w).symm.trans hw
  let A := (E'.comap ρ).map (RecipeExcLang.inndiagGroup .E6 K).subtype
  have hAI : A ≤ RecipeExcLang.inndiagGroup .E6 K := by
    rintro _ ⟨w, hw, rfl⟩
    exact w.2
  have hA : IsElemAbelian 3 A :=
    ((hE.map (MulAut.congr eR).toMonoidHom).comap hρ).map _
  have hcardA : Nat.card A = Nat.card E := by
    have h1 : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective (MulAut.congr eR).injective
    have h2 : Nat.card (E'.comap ρ) = Nat.card E' := by
      calc
        Nat.card (E'.comap ρ) = Nat.card ((E'.comap ρ).map ρ) :=
          (Subgroup.card_map_of_injective hρ).symm
        _ = Nat.card E' := congrArg
          (fun H : Subgroup (MulAut (adjointGroup .E6 K)) => Nat.card H)
          (Subgroup.map_comap_eq_self hErange)
    calc
      Nat.card A = Nat.card (E'.comap ρ) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      _ = Nat.card E := h2.trans h1
  let C := adjointGroup .E6 K ⊓ Subgroup.centralizer (A : Set (ModGL .E6 K))
  let ψ : ↥C →* ↥(ggFixedSubgroup E') :=
    { toFun := fun c => ⟨⟨(c : ModGL .E6 K), (Subgroup.mem_inf.1 c.2).1⟩, by
        rw [ggFixedSubgroup_eq_commonFixed]
        simp only [CFSG.GroupTheory.FixedCentralQuotientFamily.commonFixed, Subgroup.mem_iInf]
        intro a
        obtain ⟨w, hw⟩ := hErange a.2
        have hwA : (w : ModGL .E6 K) ∈ A :=
          Subgroup.mem_map.2 ⟨w, by change ρ w ∈ E'; rw [hw]; exact a.2, rfl⟩
        apply Subtype.ext
        change (((a : MulAut (adjointGroup .E6 K))
          ⟨(c : ModGL .E6 K), (Subgroup.mem_inf.1 c.2).1⟩) : ModGL .E6 K) = c
        rw [← hw]
        change (w : ModGL .E6 K) * c * (w : ModGL .E6 K)⁻¹ = c
        have h := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2 w hwA
        calc (w : ModGL .E6 K) * c * (w : ModGL .E6 K)⁻¹ =
            (c : ModGL .E6 K) * w * (w : ModGL .E6 K)⁻¹ := by rw [h]
          _ = c := by group⟩
      map_one' := by rfl
      map_mul' := by intro c d; rfl }
  have hψinj : Function.Injective ψ := by
    intro c d h
    exact Subtype.ext (congrArg (fun r : ↥(ggFixedSubgroup E') =>
      ((r : adjointGroup .E6 K) : ModGL .E6 K)) h)
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨r, hr⟩
    have hrfix : ∀ a ∈ E', a r = r := by
      rw [ggFixedSubgroup_eq_commonFixed] at hr
      simp only [CFSG.GroupTheory.FixedCentralQuotientFamily.commonFixed, Subgroup.mem_iInf] at hr
      exact fun a ha => hr ⟨a, ha⟩
    have hrcent : (r : ModGL .E6 K) ∈ Subgroup.centralizer (A : Set (ModGL .E6 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have h := congrArg (fun r : adjointGroup .E6 K => (r : ModGL .E6 K)) (hrfix (ρ w) hw)
      rw [RecipeExcLang.coe_inndiagConj] at h
      exact (mul_inv_eq_iff_eq_mul).1 h
    exact ⟨⟨r, r.2, hrcent⟩, rfl⟩
  let eC : ↥C ≃* ↥(ggFixedSubgroup E') := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hmapFix : ggFixedSubgroup E' = (ggFixedSubgroup E).map eR.toMonoidHom :=
    ggFixedSubgroup_map_congr eR E
  let eF : ↥(ggFixedSubgroup E) ≃* ↥(ggFixedSubgroup E') :=
    ((ggFixedSubgroup E).equivMapOfInjective eR.toMonoidHom eR.injective).trans
      (MulEquiv.subgroupCongr hmapFix.symm)
  have hNPC_C : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥C) :=
    CFSG.hasNormalPComplement_of_equiv 3 (eF.trans eC.symm).commutatorCongr hNPC
  have : Group.IsSolvable ↥C :=
    e6_three_rank_three_inndiag_full_centralizer_solvable h3 A hAI hA
      (hcardA.symm ▸ hcard) hNPC_C
  let e := eF.trans eC.symm
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem largeEvenLabelAll_E6_three_rank_three_fullFixedSolvable
    {n : ℕ} (h3 : 3 ∣ (2 ^ n) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.E6, 0, n⟩ fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
        CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  change LargeEvenRecipeChevalley Tag.E6.cartan (2 ^ n) false Q at hQ
  refine recipeChevalley_and (P := fun R _ I _ =>
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
      IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
      CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E)) ?_ hQ
  intro K _ _ hK E hEI hE hcard hNPC
  have : CharP K 2 := charP_two_of_card hK
  have h3K : 3 ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
  exact ggFixedSubgroup_isSolvable_of_recipe_E6_three_rank_three h3K E hEI hE hcard hNPC

theorem isSolvable_inf_centralizer_of_E6_three_rank_three_marking
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      lab.tag = .E6 ∧ lab.rank = 0 ∧ 3 ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian 3 (ggBeta (G := G) (L := X) θ hN).range ∧
        3 ^ 3 ≤ Nat.card (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .E6 ∧ lab.rank = 0 ∧ 3 ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
      CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab _ hs => by
      obtain ⟨htag, hrank, h3⟩ := hs
      cases lab with
      | mk tag rank n =>
        cases htag
        cases hrank
        exact largeEvenLabelAll_E6_three_rank_three_fullFixedSolvable h3)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, -, hN, hEI, hE, hcard⟩, hrow⟩ := hP
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE hcard
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

end RankThree

end CFSG.StandardType
