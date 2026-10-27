module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.HypSeventeenFiftyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem eM_le_evenRank (D : Data G) : eM D.M ≤ CFSG.Open.evenRank G := by
  unfold eM CFSG.Open.evenRank
  refine csSup_le ⟨CFSG.Open.pRank 3 D.M, 3, Nat.prime_three, by norm_num, rfl⟩ ?_
  rintro n ⟨p, hp, hp2, rfl⟩
  exact CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2 D.M D.maxLocal.1

theorem p42_alt2_of_ne
    {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V) {p : ℕ} (hp : p ∈ D.sig)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hne : conjClosure D.M L ≠ L) :
    P17_42_2 D L (conjClosure D.M L) p := by
  have hconcl : Concl17_42 D L (conjClosure D.M L) p := h42 L p hL hp
  have hsimple_of : IsSimpleGroup (Bar2 (conjClosure D.M L)) → conjClosure D.M L = L :=
    fun hsimp => conjClosure_eq_self_of_isSimpleGroup_bar2 hL hsimp
  have hnt : ¬ F08.Thin8 (conjClosure D.M L) := not_thin8_of_conjClosure_ne hL rfl hne
  rcases hconcl with h1 | h2 | h3 | h4 | h5
  · rcases h1 with hthin | ⟨n, hU3⟩ | hL3
    · exact absurd hthin hnt
    · exact absurd (hsimple_of
        (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3)) hne
    · exact absurd (hsimple_of
        (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3)) hne
  · exact h2
  · obtain ⟨n, hU5, -, -, -, -⟩ := h3
    exact absurd (hsimple_of
      (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5)) hne
  · obtain ⟨n, hSp4 | hG2, -, -, -, -, -⟩ := h4
    · exact absurd (hsimple_of
        (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp4)) hne
    · exact absurd (hsimple_of (uc22p22r_lieModel_isSimple_G2 hG2)) hne
  · obtain ⟨n, hU4, -, -, -⟩ := h5
    exact absurd (hsimple_of
      (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4)) hne

theorem conjSubgroup_mem_calC_and_ne {D : Data G} {L : Subgroup G} {x : G}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : conjClosure D.M L ≠ L) :
    CFSG.Quasithin.conjSubgroup L x ∈ calC D.M ∧ CFSG.Quasithin.conjSubgroup L x ≠ L := by
  constructor
  · change CFSG.Open.uniqueFourConj x L ∈ calC D.M
    exact uc22p22u_calC_conj (X := D.M) (M := D.M) (K := L) Subgroup.le_normalizer hL
      (m := x) hxM
  · intro hKL
    apply hne
    rw [hXsup]
    change L ⊔ CFSG.Quasithin.conjSubgroup L x = L
    rw [show CFSG.Quasithin.conjSubgroup L x = L from hKL, sup_idem]

private theorem nonempty_factor_of_prod {A B : Type} [Group A] [Group B]
    [IsSimpleGroup A] [IsSimpleGroup B] {n : ℕ} (hA : IsL2 A n) (hB : IsL2 B n ∨ IsU3 B n)
    {C : Subgroup (A × B)} (hCsub : C.IsSubnormal) (hCq : CFSG.Open.IsQuasisimple ↥C) :
    Nonempty (↥C ≃* A) ∨ Nonempty (↥C ≃* B) := by
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 (p := 2) (f := n) hA
  have hBnc : ∃ c d : B, c * d ≠ d * c := by
    rcases hB with hB2 | hB3
    · exact CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2
        (p := 2) (f := n) hB2
    · exact CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hB3
  exact uc22p22d_prod ‹IsSimpleGroup A› ‹IsSimpleGroup B› ⟨a, b, hab⟩ hBnc hCsub hCq

theorem bar2_isL2_or_isU3_of_p1642 {D : Data G} {p n : ℕ} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hLnM : (L.subgroupOf D.M).Normal) (hle : L ≤ Lp D p)
    (hn : P17_64_2 D p n) :
    IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n := by
  classical
  have hYM : Lp D p ≤ D.M := s13_Lp_le D.M p
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hL.1
  have hnormY : Lp D p ≤ normalizer (L : Set G) :=
    hYM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLnM)
  have hLnY : (L.subgroupOf (Lp D p)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hnormY
  let C : Subgroup (Bar2 (Lp D p)) :=
    (L.subgroupOf (Lp D p)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Lp D p)))
  have hCnormal : C.Normal := hLnY.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e1, -⟩ :=
    uc22p20d_bar2Equiv hle (CFSG.Open.IsSubnormal.step hle hLnY
      (CFSG.Open.IsSubnormal.refl (Lp D p)))
  obtain ⟨A, B, gA, gB, ⟨eAB⟩, hA2, hB⟩ : ∃ (A B : Type) (_ : Group A) (_ : Group B),
      Nonempty (Bar2 (Lp D p) ≃* A × B) ∧ IsL2 A n ∧ (IsL2 B n ∨ IsU3 B n) := by
    rcases hn with ⟨⟨A, B, gA, gB, e, hA2, hB2⟩, -⟩ | ⟨⟨A, B, gA, gB, e, hA2, hB3⟩, -⟩
    · exact ⟨A, B, gA, gB, e, hA2, Or.inl hB2⟩
    · exact ⟨A, B, gA, gB, e, hA2, Or.inr hB3⟩
  letI := gA
  letI := gB
  haveI : IsSimpleGroup A := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA2
  haveI : IsSimpleGroup B := by
    rcases hB with hB2 | hB3
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB2
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB3
  let C' : Subgroup (A × B) := C.map eAB.toMonoidHom
  have hC'sub : C'.IsSubnormal := hCnormal.isSubnormal.map eAB.surjective
  let e2 : ↥C ≃* ↥C' := Subgroup.equivMapOfInjective C eAB.toMonoidHom eAB.injective
  let eL : Bar2 L ≃* ↥C' := e1.trans e2
  have hC'q : CFSG.Open.IsQuasisimple ↥C' := CFSG.Open.IsQuasisimple.of_mulEquiv eL.symm hL.2.2
  rcases nonempty_factor_of_prod hA2 hB hC'sub hC'q with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl (LieModel.of_mulEquiv (eL.trans f).symm hA2)
  · rcases hB with hB2 | hB3
    · exact Or.inl (LieModel.of_mulEquiv (eL.trans f).symm hB2)
    · exact Or.inr (LieModel.of_mulEquiv (eL.trans f).symm hB3)

theorem exists_p1642_isL2_of_self
    {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V)
    (h641 : R17_64_1At D V₀ V) (h642 : R17_64_2At D V₀ V) (h643 : R17_64_3At D V₀ V)
    {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calLp D p)
    (hL0 : L ∈ calL0Star D p) (hthin : F08.Thin8 L) :
    ∃ m : ℕ, Hinf D.M = Lp D p ∧ P17_64_2 D p m ∧ IsPowTwo m ∧
      IsL2 (Bar2 L) m := by
  have h54 : Hyp1754 D p := hyp1754_of_thin_mem_calL0Star D h42 hp hL hL0 hthin
  have hHinf : Hinf D.M = Lp D p := h641 p h54
  obtain ⟨m, hm⟩ := h642 p h54
  have hpow : IsPowTwo m := (h643 p h54 m hm).1
  have hLle : L ≤ Lp D p := by
    rw [← hHinf]
    exact uc22p21c_le_Hinf hL.1.1.le hL.1.2.1
  have hL2m : IsL2 (Bar2 L) m := by
    rcases bar2_isL2_or_isU3_of_p1642 hL.1 (h54.2 L hL.1).1 hLle hm with h | hU3
    · exact h
    · exact absurd hthin (not_thin8_of_isU3 hU3)
  exact ⟨m, hHinf, hm, hpow, hL2m⟩

theorem ncard_eq_two_of_p42 {D : Data G} {L : Subgroup G} {x : G}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : conjClosure D.M L ≠ L) :
    (conjSetOf D.M L).ncard = 2 := by
  let K : Subgroup G := CFSG.Quasithin.conjSubgroup L x
  obtain ⟨hKcal, hKne⟩ := conjSubgroup_mem_calC_and_ne hL hxM hXsup hne
  have hKmem : K ∈ conjSetOf D.M L := ⟨x⁻¹, D.M.inv_mem hxM, rfl⟩
  have hXM : conjClosure D.M L ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.conjClosure_le hL.1.le
  have hLX : L ≤ conjClosure D.M L :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.le_conjClosure D.M L
  have hKX : K ≤ conjClosure D.M L := by
    rw [hXsup]
    exact le_sup_right
  have hXnormR : conjClosure D.M L ≤
      Subgroup.normalizer (CFSG.Quasithin.solvRad (conjClosure D.M L) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.Quasithin.solvRad_le _)).1
      (CFSG.Quasithin.solvRad_normal _)
  have hsubset := conjSetOf_subset_calC_conjClosure hL
  have hcompl : ∀ K' ∈ conjSetOf D.M L, K' = L ∨ K' = K := by
    intro K' hK'
    by_contra h
    push Not at h
    obtain ⟨hK'L, hK'K⟩ := h
    obtain ⟨g, hgM, rfl⟩ := hK'
    have hK'calX : L.map (MulAut.conj g).toMonoidHom ∈ calC (conjClosure D.M L) :=
      hsubset.2.2 _ ⟨g, hgM, rfl⟩
    have hLcalX : L ∈ calC (conjClosure D.M L) :=
      hsubset.2.2 L (self_mem_conjSetOf D.M L)
    have hKcalX : K ∈ calC (conjClosure D.M L) := hsubset.2.2 K hKmem
    have hK'Lc : ⁅L.map (MulAut.conj g).toMonoidHom, L⁆ ≤
        CFSG.Quasithin.solvRad (conjClosure D.M L) :=
      uc22p20e_comm_le_solvRad (uc22p20e_cComp_of_calC hK'calX)
        (uc22p20e_cComp_of_calC hLcalX) hK'L
    have hK'Kc : ⁅L.map (MulAut.conj g).toMonoidHom, K⁆ ≤
        CFSG.Quasithin.solvRad (conjClosure D.M L) :=
      uc22p20e_comm_le_solvRad (uc22p20e_cComp_of_calC hK'calX)
        (uc22p20e_cComp_of_calC hKcalX) hK'K
    have hLK' : ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≤
        CFSG.Quasithin.solvRad (conjClosure D.M L) := by
      rwa [Subgroup.commutator_comm]
    have hKK' : ⁅K, L.map (MulAut.conj g).toMonoidHom⁆ ≤
        CFSG.Quasithin.solvRad (conjClosure D.M L) := by
      rwa [Subgroup.commutator_comm]
    have hcomm : ⁅L ⊔ K, L.map (MulAut.conj g).toMonoidHom⁆ ≤
        CFSG.Quasithin.solvRad (conjClosure D.M L) :=
      CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize L K
        (L.map (MulAut.conj g).toMonoidHom) (CFSG.Quasithin.solvRad (conjClosure D.M L))
        hLK' hKK' (hLX.trans hXnormR) (hKX.trans hXnormR)
    have hK'Xcomm : ⁅L.map (MulAut.conj g).toMonoidHom, conjClosure D.M L⁆ ≤
        CFSG.Quasithin.solvRad (conjClosure D.M L) := by
      calc ⁅L.map (MulAut.conj g).toMonoidHom, conjClosure D.M L⁆
          = ⁅L.map (MulAut.conj g).toMonoidHom, L ⊔ K⁆ := by rw [hXsup]
        _ = ⁅L ⊔ K, L.map (MulAut.conj g).toMonoidHom⁆ := Subgroup.commutator_comm _ _
        _ ≤ CFSG.Quasithin.solvRad (conjClosure D.M L) := hcomm
    have hK'X : L.map (MulAut.conj g).toMonoidHom ≤ conjClosure D.M L :=
      le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf D.M L) => A)
        (L.map (MulAut.conj g).toMonoidHom) ⟨g, hgM, rfl⟩ le_rfl
    have hK'le : L.map (MulAut.conj g).toMonoidHom ≤
        CFSG.Quasithin.solvRad (conjClosure D.M L) := by
      have hperfect : ⁅L.map (MulAut.conj g).toMonoidHom,
          L.map (MulAut.conj g).toMonoidHom⁆ = L.map (MulAut.conj g).toMonoidHom :=
        hK'calX.2.1
      calc L.map (MulAut.conj g).toMonoidHom
          = ⁅L.map (MulAut.conj g).toMonoidHom, L.map (MulAut.conj g).toMonoidHom⁆ :=
            hperfect.symm
        _ ≤ ⁅L.map (MulAut.conj g).toMonoidHom, conjClosure D.M L⁆ :=
            Subgroup.commutator_mono le_rfl hK'X
        _ ≤ CFSG.Quasithin.solvRad (conjClosure D.M L) := hK'Xcomm
    haveI : Group.IsSolvable ↥(CFSG.Quasithin.solvRad (conjClosure D.M L)) :=
      CFSG.Quasithin.solvRad_isSolvable _
    exact CFSG.Quasithin.not_isSolvable_of_mem_cComp (uc22p20e_cComp_of_calC hK'calX)
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK'le)
        (Subgroup.inclusion_injective hK'le))
  have hsub : conjSetOf D.M L ⊆ {L, K} := by
    intro K' hK'
    rcases hcompl K' hK' with rfl | rfl <;> simp
  have hpair : ({L, K} : Set (Subgroup G)) ⊆ conjSetOf D.M L := by
    intro K' hK'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK'
    rcases hK' with h | h
    · rw [h]
      exact self_mem_conjSetOf D.M L
    · rw [h]
      exact hKmem
  have heq : conjSetOf D.M L = {L, K} := Set.Subset.antisymm hsub hpair
  rw [heq]
  exact Set.ncard_pair (Ne.symm hKne)

theorem exists_D3_of_p42 {D : Data G} (h8107 : F08.R8107 D) {L : Subgroup G} {x : G}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : conjClosure D.M L ≠ L) {n : ℕ} (hL2 : IsL2 (Bar2 L) n) :
    ∃ D₃ : Subgroup G, D₃ ≤ L ∧ Nat.card D₃ = 3 ∧
      D₃ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  let K : Subgroup G := CFSG.Quasithin.conjSubgroup L x
  obtain ⟨hKcal, hneK⟩ := conjSubgroup_mem_calC_and_ne hL hxM hXsup hne
  have hK2 : IsL2 (Bar2 K) n := by
    obtain ⟨e⟩ := uc22p20d_bar2_conj x⁻¹ L
    exact LieModel.of_mulEquiv e hL2
  have hLrank : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_isL2 hL2
  have hKrank : CFSG.Open.pRank 3 K = 1 := pRank_three_eq_one_of_isL2 hK2
  have hLthin : F08.Thin8 L := thin8_of_isL2 hL2
  have hKthin : F08.Thin8 K := thin8_of_isL2 hK2
  obtain ⟨D₃, hD₃L, -, hD₃card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
  rw [hLrank, pow_one] at hD₃card
  obtain ⟨A₂, hA₂K, -, hA₂card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) K
  rw [hKrank, pow_one] at hA₂card
  exact ⟨D₃, hD₃L, hD₃card,
    (h8107 L hL K hKcal (Ne.symm hneK) hLrank hKrank (Or.inl hLthin) (Or.inl hKthin)
      D₃ A₂ hD₃L hD₃card hA₂K hA₂card).1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
