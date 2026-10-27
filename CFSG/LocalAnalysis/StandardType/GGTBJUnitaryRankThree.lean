module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryRankThreeCover
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitarySix
public import CFSG.LocalAnalysis.StandardType.GGTBJLE3Transport
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixReduced
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Line63.H5 CFSG.ClassicalGroups.UnitaryFlag

theorem ggTBJUnitaryRankThree_of_component
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 3, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 3, f⟩)
    (hInn : GGInnerDiagOn Bs X)
    {C : Subgroup G} (hCB : C ≤ Bs)
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer (C : Set G))) (hJX : J ≠ X) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hJXle : J ≤ X := hJ.1.trans inf_le_left
  have hf1 : 1 ≤ f := hΛ.1
  by_cases hf : f = 1
  ·
    exfalso
    subst hf
    have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpq)
    subst hp3
    have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
    obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
    obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨heq, -, -⟩ := hP₀
    subst lab
    dsimp only [LargeEvenRawDatum] at hraw
    obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
    let : Field F := hField
    let : Finite F := hFinite
    have hF : Nat.card F = 4 := by simpa using hFK
    have : CharP F 2 := charP_two_of_card (by simpa using hF : Nat.card F = 2 ^ 2)
    obtain ⟨hs, hna, θ, hP⟩ := hQ
    obtain ⟨-, hN, hBsI⟩ := hP
    obtain ⟨hNbar, φ, hM, hdiag⟩ :=
      exists_diagonal_cover_of_unitary_four_two_red hF hXperf θ hN hBs hBsI
    obtain ⟨S, hS2, hJblock, hJbarComp⟩ :=
      exists_block_unitarySix_reduced_component hF hBs hN hCB hJ hNbar φ hM hdiag
    have hS4 : 4 ≤ S.card := by
      by_contra hlt
      have hsol : Group.IsSolvable ↥((TableBUE.blockSU (K := F) (n := 1) S).map
          (((redMkL X).range).subtype.comp φ)) :=
        WitSU.isSolvable_map_blockSU_two_one hM.field _ (by omega) (by omega)
      have hsolJ : Group.IsSolvable
          ↥((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X)) := by
        rw [hJblock]
        exact hsol
      exact SmallU.not_isComponentOf_of_solvable hJbarComp hsolJ
    have hSle : S.card ≤ 4 := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ S
    have hSuniv : S = Finset.univ :=
      Finset.eq_univ_of_card S (by simpa only [Fintype.card_fin] using (by omega : S.card = 4))
    apply hJX
    refine eq_of_map_redMk_eq_redMkL_range hXperf hJXle ?_
    rw [hJblock, hSuniv, SUTorus.blockSU_univ, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ hM.surj, Subgroup.map_top, Subgroup.range_subtype]
  · have hf2 : 2 ≤ f := by omega
    obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
      exists_diagonal_cover_of_unitary_four hRig hBs hInn hf2 hpq hLab hΛ
    let : Field F := hField
    let : Finite F := hFinite
    let : CharP F 2 := hChar
    obtain ⟨S, hJblock, hS2⟩ := exists_block_of_diagonal_unitary_component (by norm_num : 2 ≤ 3)
      hf1 hpq hBs hN hF hM hdiag (SetLike.coe_subset_coe.mpr hCB) hJ
    have hSr : S.card ≤ 3 := by
      by_contra hSgt
      have hSle : S.card ≤ 4 := by
        simpa only [Fintype.card_fin] using Finset.card_le_univ S
      have hSuniv : S = Finset.univ :=
        Finset.eq_univ_of_card S (by simpa only [Fintype.card_fin] using (by omega : S.card = 4))
      apply hJX
      rw [hJblock, hSuniv, SUTorus.blockSU_univ, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
        MonoidHom.range_eq_top_of_surjective _ hM.surj, Subgroup.map_top, Subgroup.range_subtype]
    exact ggTBJUnitary_sideDatum_of_block (r := 3) hF hf1 hp2 hpq (by norm_num) hBs hSC hN hM
      hdiag S hS2 hSr (by omega) hJblock

private theorem ggRankThree_relabel {M : Type} [Group M] {lab : LargeEvenLabel}
    (htag : lab.tag = .twA ∨ lab.tag = .twD) (hr : lab.rank = 3)
    (hΛ : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab M) :
    LargeEvenInLambda2 (⟨.twA, 3, lab.n⟩ : LargeEvenLabel) ∧
      GGHasLabel (⟨.twA, 3, lab.n⟩ : LargeEvenLabel) M := by
  rcases lab with ⟨t, r, n⟩
  simp only at htag hr
  subst hr
  rcases htag with rfl | rfl
  · exact ⟨hΛ, hhas⟩
  · exact ⟨⟨hΛ.1, by norm_num, fun h => absurd h (by norm_num)⟩, hhas⟩

theorem ggTBJLeft_unitaryRankThree_of_label
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 3, f⟩) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  have hDB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  exact ggTBJUnitaryRankThree_of_component hRig hH hpq hLab hΛ hH.2.2.1.1 hDB
    hH.1.2.2.1.2.2.2.2.2.1 (ggResHyp_J_ne_L hH)

theorem ggTBJNbr_unitaryRankThree_of_label
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 3, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 3, f⟩) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hxD : x ∈ D := hH.1.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  have hcomp' : IsComponentOf J (K ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup G) : Set G)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hcomp
  exact ggTBJUnitaryRankThree_of_component hRig hH hpq hLab hΛ (hH.2.2.1.2 y K hnb)
    (Subgroup.zpowers_le.mpr hx) hcomp' (ggResHyp_J_ne_K hH)

theorem ggTBJLeftOn_unitaryRankThree
    (hRig : GGLabelRigidInput) :
    GGTBJLeftOn ggTBJUnitaryRankThreeLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hL _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨htag, hr, hpq⟩ := hP.1
  obtain ⟨hΛ', hhas'⟩ := ggRankThree_relabel htag hr hΛ hhas
  rcases ggTBJLeft_unitaryRankThree_of_label hRig hH hpq hhas' hΛ' with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJNbrOn_unitaryRankThree
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput) :
    GGTBJNbrOn ggTBJUnitaryRankThreeLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hK _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨htag, hr, hpq⟩ := hP.1
  obtain ⟨hΛ', hhas'⟩ := ggRankThree_relabel htag hr hΛ hhas
  rcases ggTBJNbr_unitaryRankThree_of_label hRig hI3 hH hpq hhas' hΛ' with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJOrderRestSplitAUnitSix_of_restUnitRankThree
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (h : GGTBJOrderRestSplitAUnitRankThreeInput) : GGTBJOrderRestSplitAUnitSixInput :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_unitaryRankThree hRig)
    (ggTBJNbrOn_unitaryRankThree hRig hI3) h

end CFSG.StandardType

end
