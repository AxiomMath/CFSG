module

public import CFSG.OddTranspositions.Reduction
public import CFSG.OddTranspositions.Transfer
public import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld

variable {Y : Type} [Group Y] [Finite Y] {D : Set Y}

theorem oddTranspNoSqE1Dich_of_classification
    (hC : AscNoSqDichotomy) :
    CFSG.RankThree.GF2n.Tim79a.OddTranspNoSqE1Dich := by
  intro Y _ _ D hcls hroot hdeg hgen hnc hsolv hchar hns
  have hclsG : ∃ d₀ : Y ⧸ Subgroup.center Y,
      QuotientGroup.mk' (Subgroup.center Y) '' D = {g | IsConj d₀ g} :=
    image_isClass_center hcls
  have hoddG : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp
      (QuotientGroup.mk' (Subgroup.center Y) '' D) :=
    image_isOddTransp_center hroot hnc hdeg
  have hgenG : Subgroup.closure (QuotientGroup.mk' (Subgroup.center Y) '' D) = ⊤ :=
    image_closure_eq_top_center hgen
  have hsolvG : ∀ N : Subgroup (Y ⧸ Subgroup.center Y),
      N.Normal → Group.IsSolvable N → N = ⊥ :=
    fun N hN hNsol => solvable_normal_eq_bot_quotient_center hsolv N hNsol
  have hEG : commutator (Y ⧸ Subgroup.center Y) = layer (Y ⧸ Subgroup.center Y) :=
    commutator_eq_layer hcls hroot hdeg hgen hnc hsolv hchar
  have hT2 : IsPGroup 2 ((Y ⧸ Subgroup.center Y) ⧸ layer (Y ⧸ Subgroup.center Y)) :=
    isPGroup_quotient_layer_of_solvable hcls hroot hdeg hgen hnc hsolv hchar
  have hns' : ¬ ∃ u ∈ QuotientGroup.mk' (Subgroup.center Y) '' D,
      ∃ v ∈ QuotientGroup.mk' (Subgroup.center Y) '' D,
        u ≠ v ∧ Commute u v ∧
          u * v ∈ QuotientGroup.mk' (Subgroup.center Y) '' D := hns
  rcases hC (Y ⧸ Subgroup.center Y) (QuotientGroup.mk' (Subgroup.center Y) '' D)
    hclsG hoddG hgenG hsolvG hEG hT2 hns' with hE1 | hT
  · exact Or.inl (noSqE1_of_center_quotient hcls hroot hdeg hsolv hE1)
  · refine Or.inr ?_
    have hset : {A : Subgroup (Y ⧸ Subgroup.center Y) |
          ∃ d ∈ D, A = Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center Y) d)} =
        {A : Subgroup (Y ⧸ Subgroup.center Y) |
          ∃ d ∈ QuotientGroup.mk' (Subgroup.center Y) '' D, A = Subgroup.zpowers d} := by
      ext A
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨QuotientGroup.mk' (Subgroup.center Y) d, ⟨d, hd, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨d, hd, rfl⟩, rfl⟩
        exact ⟨d, hd, rfl⟩
    rw [hset]
    exact hT


theorem ascNoSqDichotomy_of_inputs
    (hI1 : NoSqE1OrThreeTranspositions)
    (hSimple : ∀ (G : Type) [Group G] [Finite G] (D : Set G),
      (∃ d₀ : G, D = {g | IsConj d₀ g}) → (∀ d ∈ D, orderOf d = 2) →
      (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
      Subgroup.closure D = ⊤ → Subgroup.center G = ⊥ →
      (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
      commutator G = layer G → IsSimpleGroup (commutator G))
    (hI3 : ThreeTranspositionDichotomy) :
    AscNoSqDichotomy := by
  intro G _ _ D hcls hoddT hgen hsolv hEG hT2 hns
  by_cases hE1 : CFSG.RankThree.GF2n.Tim79a.NoSqE1 D
  · exact Or.inl hE1
  · refine Or.inr ?_
    have hprod : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) :=
      hI1 G D hcls hoddT hgen hsolv hEG hT2 hns hE1
    have hinv : ∀ d ∈ D, orderOf d = 2 := fun d hd => hoddT.1 d hd
    have hcenter : Subgroup.center G = ⊥ := by
      have hsolv' : Group.IsSolvable (Subgroup.center G) :=
        isSolvable_of_comm fun a b =>
          Subtype.ext (Subgroup.mem_center_iff.mp a.2 b).symm
      exact hsolv (Subgroup.center G) inferInstance hsolv'
    have hpair : CFSG.Blueprint.Fischer.Pair G D :=
      ⟨inferInstance, hcls, hinv, hprod, hgen⟩
    rcases hI3 G D hpair hcenter
      (hSimple G D hcls hinv hprod hgen hcenter hsolv hEG) with hE1' | hT
    · exact absurd hE1' hE1
    · exact hT

end CFSG.OddTranspositions
