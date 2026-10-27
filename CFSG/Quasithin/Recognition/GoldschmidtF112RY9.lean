module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two

public section

namespace CFSG.Quasithin

namespace F112R

open CFSG.Open CFSG.QuasithinUnique

section Swap

variable {X Y : Type} [Group X] [Group Y]

def ofSubgroupsSwapIso {P1 P2 : Subgroup X} {M1 M2 : Subgroup Y}
    (e : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M1 M2)) :
    (RankTwoAmalgam.ofSubgroups P2 P1).Iso (RankTwoAmalgam.ofSubgroups M2 M1) where
  φ1 := e.φ2
  φ12 := (MulEquiv.subgroupCongr (inf_comm P2 P1)).trans
    (e.φ12.trans (MulEquiv.subgroupCongr (inf_comm M1 M2)))
  φ2 := e.φ1
  comm1 g := by
    have h := congrArg Subtype.val (e.comm2 (MulEquiv.subgroupCongr (inf_comm P2 P1) g))
    exact Subtype.ext h
  comm2 g := by
    have h := congrArg Subtype.val (e.comm1 (MulEquiv.subgroupCongr (inf_comm P2 P1) g))
    exact Subtype.ext h

theorem isYAmalgamPair_swap {T M1 M2 : Subgroup Y} (h : IsYAmalgamPair T M1 M2) :
    IsYAmalgamPair T M2 M1 :=
  ⟨h.1, h.2.1.symm, fun M => (h.2.2 M).trans or_comm⟩

theorem isAmalgamOfGroup_ofSubgroups_swap {P1 P2 : Subgroup X} {P : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P1 P2) P) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P2 P1) P := by
  obtain ⟨Y, _, hP, T, M1, M2, hpair, ⟨e⟩⟩ := h
  exact ⟨Y, _, hP, T, M2, M1, isYAmalgamPair_swap hpair, ⟨ofSubgroupsSwapIso e⟩⟩

end Swap

section Defs

variable {G : Type} [Group G]

@[expose] def VA5 (L : Subgroup G) : Prop :=
  IsL2Quot 2 (oTwoQuot ↥L)

abbrev f112Amalgam (L1 L2 S : Subgroup G) : RankTwoAmalgam.{0} :=
  RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)

theorem isAmalgamOfGroup_f112Amalgam_swap {L1 L2 S : Subgroup G}
    {P : ∀ (Y : Type) [Group Y], Prop} (h : IsAmalgamOfGroup (f112Amalgam L1 L2 S) P) :
    IsAmalgamOfGroup (f112Amalgam L2 L1 S) P := by
  unfold f112Amalgam
  rw [bigB_comm L1 L2 S]
  exact isAmalgamOfGroup_ofSubgroups_swap h

@[expose] def PerfectOver (L1 L2 S : Subgroup G) : Prop :=
  perfectCore L1 = L1 ∧ perfectCore L2 = L2 ∧ S ≤ L1 ∧ S ≤ L2

@[expose] def G24Oriented (L1 L2 S : Subgroup G) : Prop :=
  (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
    IsSpecialPow 2 (2 ^ 2) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
    Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ 2) ^ 5

end Defs

@[expose] def IdA5A5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VA5 L1 → VA5 L2 →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 2) ∨
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over 2) ∨
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over 2)

@[expose] def IdS3A5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VS3 L1 → VA5 L2 →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 1) ∨
        IsU4ExtTwo 1 (f112Amalgam L1 L2 S) ∨
        IsParabolicAmalgamOfGroup (f112Amalgam L2 L1 S) (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∨
        IsParabolicAmalgamOfGroup (f112Amalgam L2 L1 S)
          (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2))

@[expose] def Y9L34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VA5 L1 → VA5 L2 →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 2) →
        (IsBlock2 L1 L1 ∧ IsLin2Type L1 2) ∧ (IsBlock2 L2 L2 ∧ IsLin2Type L2 2) ∧
          PerfectOver L1 L2 S

@[expose] def Y9Sp44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VA5 L1 → VA5 L2 →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over 2) →
        (IsBlock2 L1 L1 ∧ IsLin2Type L1 2) ∧ (IsBlock2 L2 L2 ∧ IsLin2Type L2 2) ∧
          PerfectOver L1 L2 S

@[expose] def Y9G24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VA5 L1 → VA5 L2 →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over 2) →
        (G24Oriented L1 L2 S ∨ G24Oriented L2 L1 S) ∧ PerfectOver L1 L2 S

@[expose] def Y9U42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VS3 L1 → VA5 L2 →
      (IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 1) ∨
          IsU4ExtTwo 1 (f112Amalgam L1 L2 S)) →
        (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
            centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
          IsSpecialPow 2 (2 ^ 1) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
          IsBlock2 L2 L2 ∧ IsOmega4MinusType L2 1 ∧ IsAltType L2 5

@[expose] def Y9J2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VA5 L1 → VS3 L2 →
      IsParabolicAmalgamOfGroup (f112Amalgam L1 L2 S) (fun Y _ => Nonempty (Y ≃* quasithinJ2)) →
        (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
            centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
          IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
          Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6

@[expose] def Y9AutJ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VA5 L1 → VS3 L2 →
      IsParabolicAmalgamOfGroup (f112Amalgam L1 L2 S)
          (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) →
        (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
            centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
          Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧
          IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
          Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6

section Assembly

variable {G : Type} [Group G]

theorem orient_of_imp {L1 L2 S : Subgroup G}
    (h : centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1 : Set G)) :
    centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
        centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1 : Set G) := fun h' => h'.elim id h

theorem PerfectOver.symm {L1 L2 S : Subgroup G} (h : PerfectOver L1 L2 S) : PerfectOver L2 L1 S :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem f112ConclC_of_symm {L1 L2 S : Subgroup G} (h12 : F112ListC L1 L2 S)
    (h21 : F112ListC L2 L1 S) (hp : PerfectOver L1 L2 S) : F112ConclC L1 L2 S := by
  by_cases hz : centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1 : Set G)
  · exact ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, orient_of_imp hz, h12, Or.inl hp⟩
  · have hz2 : centerOf S ≤ Subgroup.centralizer (L2 : Set G) := by
      by_contra hc
      exact hz fun h => absurd h hc
    exact ⟨L2, L1, Or.inr ⟨rfl, rfl⟩, fun _ => hz2, h21, Or.inl hp.symm⟩

theorem f112ConclC_of_A5A5 (hId : IdA5A5) (hL : Y9L34) (hS : Y9Sp44) (hG : Y9G24) :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VA5 L1 → VA5 L2 → F112ConclC L1 L2 S := by
  intro G _ _ L1 L2 S hF h1 h2
  rcases hId G L1 L2 S hF h1 h2 with hA | hA | hA
  · obtain ⟨⟨b1, l1⟩, ⟨b2, l2⟩, hp⟩ := hL G L1 L2 S hF h1 h2 hA
    exact f112ConclC_of_symm
      (Or.inl ⟨2, by norm_num, hA, Or.inl ⟨le_rfl, b1, l1, b2, l2⟩⟩)
      (Or.inl ⟨2, by norm_num, isAmalgamOfGroup_f112Amalgam_swap hA, Or.inl ⟨le_rfl, b2, l2, b1, l1⟩⟩)
      hp
  · obtain ⟨⟨b1, l1⟩, ⟨b2, l2⟩, hp⟩ := hS G L1 L2 S hF h1 h2 hA
    exact f112ConclC_of_symm
      (Or.inr (Or.inl ⟨2, by norm_num, hA, Or.inl ⟨le_rfl, b1, l1, b2, l2⟩⟩))
      (Or.inr (Or.inl ⟨2, by norm_num, isAmalgamOfGroup_f112Amalgam_swap hA,
        Or.inl ⟨le_rfl, b2, l2, b1, l1⟩⟩))
      hp
  · obtain ⟨ho | ho, hp⟩ := hG G L1 L2 S hF h1 h2 hA
    · obtain ⟨hz, hs, hc⟩ := ho
      exact ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, orient_of_imp hz,
        Or.inr (Or.inr (Or.inl ⟨2, by norm_num, hA, h1, h2, hs, hc⟩)), Or.inl hp⟩
    · obtain ⟨hz, hs, hc⟩ := ho
      exact ⟨L2, L1, Or.inr ⟨rfl, rfl⟩, fun h' => h'.elim hz id,
        Or.inr (Or.inr (Or.inl ⟨2, by norm_num, isAmalgamOfGroup_f112Amalgam_swap hA, h2, h1, hs,
          hc⟩)), Or.inl hp.symm⟩

theorem f112ConclC_of_S3A5 (hId : IdS3A5) (hU : Y9U42) (hJ : Y9J2) (hAJ : Y9AutJ2) :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VS3 L1 → VA5 L2 → F112ConclC L1 L2 S := by
  intro G _ _ L1 L2 S hF h1 h2
  have hq1 : IsL2Quot 1 (oTwoQuot ↥L1) := isL2Quot_one_iff_perm3.2 h1
  rcases hId G L1 L2 S hF h1 h2 with hA | hA | hA | hA
  · obtain ⟨hz, hs, hb, ho, ha⟩ := hU G L1 L2 S hF h1 h2 (Or.inl hA)
    refine ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, orient_of_imp hz, ?_, ?_⟩
    · iterate 5 right
      exact Or.inl ⟨1, le_rfl, Or.inl hA, hq1, hs, hb, h2, ho, fun _ => ha⟩
    · iterate 7 right
      exact Or.inl hA
  · obtain ⟨hz, hs, hb, ho, ha⟩ := hU G L1 L2 S hF h1 h2 (Or.inr hA)
    refine ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, orient_of_imp hz, ?_, ?_⟩
    · iterate 5 right
      exact Or.inl ⟨1, le_rfl, Or.inr hA, hq1, hs, hb, h2, ho, fun _ => ha⟩
    · iterate 13 right
      exact ⟨1, le_rfl, hA⟩
  · obtain ⟨hz, hq, hc⟩ := hJ G L2 L1 S hF.symm h2 h1 hA
    refine ⟨L2, L1, Or.inr ⟨rfl, rfl⟩, fun h' => h'.elim hz id, ?_, ?_⟩
    · iterate 9 right
      exact Or.inl ⟨hA, h2, hq, hq1, hc⟩
    · iterate 9 right
      exact Or.inl hA
  · obtain ⟨hz, h5, hq, hc⟩ := hAJ G L2 L1 S hF.symm h2 h1 hA
    refine ⟨L2, L1, Or.inr ⟨rfl, rfl⟩, fun h' => h'.elim hz id, ?_, ?_⟩
    · iterate 10 right
      exact Or.inl ⟨hA, h5, hq, h1, hc⟩
    · iterate 10 right
      exact Or.inl hA

theorem f112ConclC_of_A5S3_pair (hId : IdS3A5) (hU : Y9U42) (hJ : Y9J2) (hAJ : Y9AutJ2) :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → (VS3 L1 ∧ VA5 L2) ∨ (VA5 L1 ∧ VS3 L2) → F112ConclC L1 L2 S := by
  intro G _ _ L1 L2 S hF hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact f112ConclC_of_S3A5 hId hU hJ hAJ G L1 L2 S hF h1 h2
  · exact (f112ConclC_of_S3A5 hId hU hJ hAJ G L2 L1 S hF.symm h2 h1).symm

end Assembly

end F112R

end CFSG.Quasithin
