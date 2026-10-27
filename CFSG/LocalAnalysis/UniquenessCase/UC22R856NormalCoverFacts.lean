module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425G2p
import CFSG.Quasithin.H13.A5W1620Ta
import CFSG.Quasithin.H13.A6S13821M22c
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Cover423G2
import CFSG.LargeExtraspecial.S5Gen2
import CFSG.Adapters.LieModelL3U3Torus
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.H13.KGFactJ2Row
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeSolv
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
import CFSG.GroupTheory.ThreeTranspositions.IndexEnd
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56U14CoverT
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56U14CoverBar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56U14CoverFacts
import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Lists
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsHolds
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3Holds
import CFSG.RankThree.PartTwo.Sec17.Item17Res10ProofGTwo
import CFSG.Adapters.RankThreeOutcomesReverse

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup


theorem not_isCoverShape_of_isSLThreePiAt
    {X : Type} [Group X] [Finite X] {q : ℕ} (hq : 2 ≤ q)
    (h : CFSG.RankThree.PartTwo.Sec4.IsSLThreePiAt X q) : ¬ IsCoverShape X := by
  intro hcov
  obtain ⟨K, _, _, hK⟩ := h
  have hquot : Nat.card (X ⧸ center X) = 360 ∨
      Nat.card (X ⧸ center X) = 2520 ∨ Nat.card (X ⧸ center X) = 443520 := by
    rcases hcov.2.2 with h | h | h
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv,
        CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
      norm_num [Nat.factorial]
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv,
        CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
      norm_num [Nat.factorial]
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv]
      exact Or.inr (Or.inr CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM22)
  rcases hK with ⟨hK, hmod, ⟨e⟩⟩ | ⟨hK, hmod, ⟨e⟩⟩
  · have hcenter : Nat.card (center X) = 3 := by
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (by omega)
    have hcard : Nat.card X = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hK]
    have hquotcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    rw [hcenter] at hquotcard
    rcases hquot with h360 | h2520 | hM22
    · rw [h360] at hquotcard
      exact (CFSG.Quasithin.H13.A5.sl3_su3_card_ne hq (n := 1080) (by omega)).1
        (hcard.symm.trans (by simpa using hquotcard))
    · rw [h2520] at hquotcard
      exact (CFSG.Quasithin.H13.A5.sl3_su3_card_ne hq (n := 7560) (by omega)).1
        (hcard.symm.trans (by simpa using hquotcard))
    · apply CFSG.Quasithin.H13.A6.HatM22.false_of_isSLEps3 (s := true) (q := q)
        (Or.inl (by simpa [hM22] using hquotcard))
      exact ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  · have hcenter : Nat.card (center X) = 3 := by
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact CFSG.Open.StatedCenterThree.card_center_statedSU_three hK (by omega)
    have hcard : Nat.card X = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK]
    have hquotcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    rw [hcenter] at hquotcard
    rcases hquot with h360 | h2520 | hM22
    · rw [h360] at hquotcard
      exact (CFSG.Quasithin.H13.A5.sl3_su3_card_ne hq (n := 1080) (by omega)).2
        (hcard.symm.trans (by simpa using hquotcard))
    · rw [h2520] at hquotcard
      exact (CFSG.Quasithin.H13.A5.sl3_su3_card_ne hq (n := 7560) (by omega)).2
        (hcard.symm.trans (by simpa using hquotcard))
    · apply CFSG.Quasithin.H13.A6.HatM22.false_of_isSLEps3 (s := false) (q := q)
        (Or.inl (by simpa [hM22] using hquotcard))
      exact ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩

section G2Facts


theorem isSLThreePiAt_centralizer_g2_of_not_three
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3) (hq : 4 ≤ p ^ f)
    (z : CFSG.Blueprint.Chevalley.adjointGroup .G2 F) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (J : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))
    (hJC : J ≤ centralizer ({z} : Set _)) (hJq : CFSG.IsQuasisimple J)
    (hJs : (J.subgroupOf (centralizer ({z} : Set _))).IsSubnormal) (hzJ : z ∈ J) :
    CFSG.RankThree.PartTwo.Sec4.IsSLThreePiAt J (p ^ f) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hF
  have hchar : ringChar F ≠ 3 := by rw [ringChar.eq F p]; exact hp3
  have h4 : 4 ≤ Nat.card F := hF ▸ hq
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds F hchar h4 z hz3 hz1
  let e := MulAut.conj g
  obtain ⟨hJC', hJs'⟩ := CFSG.RankThree.PartTwo.Sec4.Ronan148H.map_le_centralizer_isSubnormal e hJC hJs
  let eJ := J.equivMapOfInjective e.toMonoidHom e.injective
  have hJq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hJq
  have hz3' : e z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hz1' : e z ≠ 1 := by exact fun h => hz1 (e.injective (h.trans (map_one e).symm))
  have hzJ' : e z ∈ J.map e.toMonoidHom := mem_map.mpr ⟨z, hzJ, rfl⟩
  refine CFSG.RankThree.PartTwo.Sec4.Ronan148H.isSLThreePiAt_of_mulEquiv eJ ?_
  rcases hg with hS | hM
  · have h3 : p ^ f % 3 = 1 ∨ p ^ f % 3 = 2 := by
      have hnp : ¬ 3 ∣ p := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
      have hnf : ¬ 3 ∣ p ^ f := fun h => hnp (Nat.prime_three.dvd_of_dvd_pow h)
      omega
    rcases h3 with h1 | h2
    · have h := CFSG.RankThree.PartTwo.Sec4.Ronan148H.isSLThreePiAt_of_threeA_one
        (by rw [hF]; exact h1) hS hz3' hz1' hJC' hJq' hJs'
      rwa [hF] at h
    · exact CFSG.RankThree.PartTwo.Sec4.Ronan148H.isSLThreePiAt_of_threeA_two hF h2
        (by omega) hS hz3' hz1' hJC' hJq' hJs'
  · exact (CFSG.RankThree.PartTwo.Sec4.Ronan148H.false_of_threeB_odd hchar h4
      hM hz3' hz1' hJC' hJq' hzJ').elim

theorem not_isQuasisimple_subgroup_centralizer_g2_three
    {F : Type} [Field F] [Finite F] [CharP F 3]
    {z : CFSG.Blueprint.Chevalley.adjointGroup .G2 F} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {J : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)}
    (hJC : J ≤ centralizer ({z} : Set _))
    (hJn : (J.subgroupOf (centralizer ({z} : Set _))).Normal) : ¬ CFSG.IsQuasisimple J := by
  intro hJq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.isCharacteristicP_centralizer_g2_three hz1 hz3
  have eq := Subgroup.subgroupOfEquivOfLe hJC
  have hq : CFSG.IsQuasisimple (J.subgroupOf (centralizer ({z} : Set _))) :=
    CFSG.IsQuasisimple.of_mulEquiv eq hJq
  exact CFSG.LieType.Chevalley.RootWeightDatum.not_isComponent_of_isCharacteristicP hchar _
    ⟨hq, hJn.isSubnormal⟩


theorem kFactG2CentCover_holds : KFactG2CentCover := by
  intro K _ _ p f hp hmodel z hz J hJC hJn hzJ hcover
  have hc := hmodel.chevalleyExceptionalModel (by decide)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hc.2
  let J' := J.map e.toMonoidHom
  let eJ := J.equivMapOfInjective e.toMonoidHom e.injective
  have hJ'cov : IsCoverShape J' := IsCoverShape.of_mulEquiv eJ hcover
  have hJ'C : J' ≤ centralizer ({e z} : Set _) := by
    rintro a ⟨a0, ha0, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change e a0 * e z = e z * e a0
    exact (map_mul e a0 z).symm.trans
      ((congrArg e (mem_centralizer_singleton_iff.mp (hJC ha0))).trans (map_mul e z a0))
  have hJ's : (J'.subgroupOf (centralizer ({e z} : Set _))).IsSubnormal :=
    (CFSG.RankThree.PartTwo.Sec4.Ronan148H.map_le_centralizer_isSubnormal e hJC hJn.isSubnormal).2
  have hJ'n : (J'.subgroupOf (centralizer ({e z} : Set _))).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hJ'C]
    intro a ha
    obtain ⟨b, rfl⟩ := e.surjective a
    have hb : b ∈ centralizer ({z} : Set K) := by
      rw [mem_centralizer_singleton_iff] at ha ⊢
      exact e.injective (by simpa only [map_mul] using ha)
    have hbN := (normal_subgroupOf_iff_le_normalizer hJC).mp hJn hb
    exact Subgroup.le_normalizer_map e.toMonoidHom (mem_map.mpr ⟨b, hbN, rfl⟩)
  have hJ'q := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hcover.1
  have hz3 : e z ^ 3 = 1 := by rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  have hz1 : e z ≠ 1 := by
    intro h
    have hz1 : z = 1 := e.injective (h.trans (map_one e).symm)
    rw [hz1, orderOf_one] at hz
    omega
  have hzJ' : e z ∈ J' := mem_map.mpr ⟨z, hzJ, rfl⟩
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP F 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hp hc.1.2.1 hF
    exact not_isQuasisimple_subgroup_centralizer_g2_three hz3 hz1 hJ'C hJ'n hJ'q
  · have hq3 : 3 ≤ p ^ f := hc.1.2.2.2
    have hqne3 : p ^ f ≠ 3 := by
      intro heq
      have hd : 3 ∣ p ^ f := by rw [heq]
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow hd)).symm
    have hsl := isSLThreePiAt_centralizer_g2_of_not_three hp hc.1.2.1 hF hp3
      (by omega) (e z) hz3 hz1 J' hJ'C hJ'q hJ's hzJ'
    exact not_isCoverShape_of_isSLThreePiAt (by omega) hsl hJ'cov

end G2Facts

theorem isSolvable_outer_of_ker_eq_inner
    {K A : Type} [Group K] [Group A] [IsMulCommutative A]
    (Theta : MulAut K →* A)
    (hker : Theta.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) := by
  let F := QuotientGroup.lift (CFSG.ComponentClassification.OuterAutomorphisms.inner K) Theta hker.ge
  have hF : Function.Injective F :=
    (QuotientGroup.injective_lift_iff _ Theta hker.ge).2 hker.symm
  exact Group.isSolvable_of_isSolvable_injective hF

section G2Outer


theorem isSolvable_outer_adjointGroup_g2
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 3 ≤ Nat.card F) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) := by
  by_cases hp2 : p = 2
  · subst hp2
    have hf2 : 2 ≤ f := by
      by_contra h
      have h1 : f = 1 := by omega
      rw [h1] at hF
      norm_num at hF
      omega
    obtain ⟨Theta, -, -, hker, -⟩ :=
      (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf2 F hF).2
    have : IsCyclic (F ≃+* F) :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two F hF).2
    exact isSolvable_outer_of_ker_eq_inner Theta hker
  · by_cases hp3 : p = 3
    · subst hp3
      have : CharP F CFSG.LieType.Ree.ReeTag.G2.prime :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hF
      obtain ⟨Theta, -, -, hker⟩ :=
        (CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form hf F hF).2.2.1
      exact isSolvable_outer_of_ker_eq_inner Theta hker
    · obtain ⟨Theta, -, -, hker, -⟩ :=
        (CFSG.LieType.Chevalley.odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf F hF
          .G2 (Or.inr ⟨rfl, hp3⟩)).2
      have : IsCyclic (F ≃+* F) :=
        (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hF).2
      exact isSolvable_outer_of_ker_eq_inner Theta hker

end G2Outer

section OuterFacts


theorem kFactK332TypesOut_holds : KFactK332TypesOut := by
  intro K _ _ hK
  rcases hK with hU | ⟨p, f, hp, hG⟩ | hJ
  · have : IsSimpleGroup K := hU.isSimpleGroup_of_mem_classicalTags (by decide)
    have hcard : Nat.card K = 6048 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three (hU.statedClassicalModel (by decide))
    have hcenter : center K = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
      · exact h
      · have : IsMulCommutative K := (Subgroup.upperCentralSeries_one_eq_top_iff).mp
          (by simpa only [Subgroup.upperCentralSeries_one] using h)
        let : CommGroup K := { (inferInstance : Group K) with mul_comm := mul_comm' }
        have hprime := IsSimpleGroup.prime_card (α := K)
        rw [hcard] at hprime
        norm_num at hprime
    refine ⟨hcenter, ?_⟩
    apply CFSG.LargeExtraspecial.S5.isSolvable_of_card_le_two
    change Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) ≤ 2
    rw [hU.card_outer_psu3]
    norm_num
  · have hc := hG.chevalleyExceptionalModel (by decide)
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hc.2
    have hcenter : center K = ⊥ := by
      have hmap := Subgroup.map_center_eq e
      rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
    have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :=
      isSolvable_outer_adjointGroup_g2 hp hc.1.2.1 hF (hF ▸ hc.1.2.2.2)
    exact ⟨hcenter, Group.isSolvable_of_isSolvable_injective
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective⟩
  · obtain ⟨e⟩ := hJ
    have hcenter : center K = ⊥ := by
      have hmap := Subgroup.map_center_eq e
      rw [CFSG.Quasithin.H13.A5.KGJ2.center_carrier_j2] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
    have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (CFSG.Blueprint.NativeSporadic.Carrier .J2)) := by
      change Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        CFSG.Blueprint.NativeSporadic.J2)
      exact CFSG.Sporadic.Schreier.AT_J2_Schreier.2.2
    exact ⟨hcenter, Group.isSolvable_of_isSolvable_injective
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective⟩

end OuterFacts


open CFSG.Open Subgroup

section J2

theorem kFactJ2NoStrong_holds : KFactJ2NoStrong := by
  classical
  intro J _ _ hK hJ hr M hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup J := by
    obtain ⟨e⟩ := hJ
    exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have h3 : 3 ∣ Nat.card J := by
    rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_eq_of_j2 hJ]
    norm_num
  have hO3 : CFSG.pPrimeCore 3 J = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (CFSG.pPrimeCore 3 J) with h | h
    · exact h
    · have hc := CFSG.pPrimeCore_coprime_card (p := 3) (G := J)
      rw [h, Subgroup.card_top] at hc
      exact False.elim (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc) h3)
  have hMs : Group.IsSolvable M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.isSolvable_of_isStronglyPEmbedded_three
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds hK hO3 (by omega) hM
  obtain ⟨P, hPM⟩ := CFSG.GroupTheory.ThreeTranspositions.exists_sylow_le_of_isStronglyPEmbedded
    Nat.prime_three hM
  have hZcard := (CFSG.RankThree.PartTwo.Sec14.j2_sylow_facts
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 hJ P).1
  let Z : Subgroup J := (P : Subgroup J) ⊓ centralizer ((P : Subgroup J) : Set J)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hZcard])
  have hz1 : (z : J) ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hz
    norm_num at hz
  have hz3 : (z : J) ^ 3 = 1 := by
    exact congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
  have hzP : (z : J) ∈ (P : Subgroup J) := z.2.1
  have hPC : (P : Subgroup J) ≤ centralizer ({(z : J)} : Set J) := by
    intro p hp
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp z.2.2 p hp)
  have hCM : centralizer ({(z : J)} : Set J) ≤ M :=
    hM.centralizer_le hz1 hz3 (hPM hzP)
  have : Group.IsPerfect (centralizer ({(z : J)} : Set J)) :=
    CFSG.RankThree.PartTwo.KFacts.KS14.Native.j2_centralizer_isPerfect hJ hz1 ⟨P, hzP, hPC⟩
  have : Nontrivial (centralizer ({(z : J)} : Set J)) := by
    apply (Subgroup.nontrivial_iff_ne_bot _).mpr
    intro h
    have hmem := hPC hzP
    rw [h, mem_bot] at hmem
    exact hz1 hmem
  have : Group.IsSolvable (centralizer ({(z : J)} : Set J)) := by
    have := hMs
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCM)
  exact Group.IsPerfect.not_isSolvable (centralizer ({(z : J)} : Set J)) inferInstance

end J2

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
theorem weaklyClosed_normalizer_pPrimeBarImage
    {Γ : Type} [Group Γ] [Finite Γ] {Z : Subgroup Γ} (hZ : Nat.card Z = 3)
    (hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z (normalizer (Z : Set Γ))) :
    ∀ g : Γ ⧸ CFSG.pPrimeCore 3 Γ,
      (pPrimeBarImage Z).map (MulAut.conj g).toMonoidHom ≤ normalizer (pPrimeBarImage Z : Set _) →
      (pPrimeBarImage Z).map (MulAut.conj g).toMonoidHom = pPrimeBarImage Z := by
  obtain ⟨z, hz, hze⟩ := CFSG.RankThree.PartTwo.Sec4.Item432Proof.exists_zpowers_eq hZ
  have hwz : ∀ g : Γ, (zpowers z).map (MulAut.conj g).toMonoidHom ≤ normalizer (zpowers z : Set Γ) →
      (zpowers z).map (MulAut.conj g).toMonoidHom = zpowers z := by
    intro g hg
    rw [hze] at hg ⊢
    simpa only [CFSG.conjugate, inv_inv] using hwc g⁻¹ (by simpa only [CFSG.conjugate, inv_inv] using hg)
  let K : Subgroup Γ := ⊤
  let e : K ≃* Γ := Subgroup.topEquiv
  let ebar := QuotientGroup.congr (CFSG.pPrimeCore 3 K) (CFSG.pPrimeCore 3 Γ) e
    (CFSG.pPrimeCore_map_iso 3 e)
  have hwK := CFSG.RankThree.PartTwo.Sec17.Proof176.weaklyClosed_quot hz hwz
    (K := K) (show z ∈ K from mem_top z)
  have hm : ((zpowers (⟨z, mem_top z⟩ : K)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 K))).map ebar.toMonoidHom = pPrimeBarImage Z := by
    rw [map_map]
    have heq : ebar.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 K)) =
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)).comp e.toMonoidHom := by
      ext x
      rfl
    rw [heq, ← map_map, MonoidHom.map_zpowers]
    change (zpowers z).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)) = pPrimeBarImage Z
    rw [hze]
  have hwe := CFSG.RankThree.PartTwo.Sec17.Proof17Res10.weaklyClosed_map ebar hwK
  rwa [hm] at hwe

section Cases

theorem k332OutBar_of_coverCore_of_rows
    {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ} (h : CoverCore Z Q L N) :
    K332OutBar (normalClosure (pPrimeBarImage Z : Set (Γ ⧸ CFSG.pPrimeCore 3 Γ))) := by
  have hB := coverBar_of_coverCore h
  have hcomp := components_PL332 hB.kgroup hB.rank fun K hK =>
    CFSG.RankThree.PartTwo.Sec4.Item432Proof.isPGroup_center_of_isSubnormal hB.o3 hK.2
  have hrow := row332_of_rows CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.k33_holds k332Rows_holds
  have hmain := item332_of_row hrow _ hcomp hB.o3 _ hB.zcard
    (weaklyClosed_normalizer_pPrimeBarImage h.zcard h.wc)
  rcases hmain with h1 | (⟨p, f, hm⟩ | ⟨e⟩) | hJ
  · exact Or.inl h1
  · refine Or.inr (Or.inr (Or.inl ⟨p, f, hm.1.1, ?_⟩))
    exact Or.inr (Or.inl ⟨rfl, by decide, hm⟩)
  · obtain ⟨e⟩ := e
    refine Or.inr (Or.inl ?_)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Or.inl ⟨by decide,
      CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSU
        ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩ e⟩
  · exact Or.inr (Or.inr (Or.inr hJ))


end Cases

section Cover

theorem false_of_coverCore_of_rows
    {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ} (h : CoverCore Z Q L N) : False :=
  false_of_coverBar (coverBar_of_coverCore h) (k332OutBar_of_coverCore_of_rows h)
    UCK.kSch_holds kFactG2CentCover_holds kFactK332TypesOut_holds
    kFactGammaStrong kFactJ2NoStrong_holds

end Cover
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
