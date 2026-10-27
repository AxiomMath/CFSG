module

public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionListBound
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

abbrev ThreeCat : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Census3.TheoremThreeHyp G → Census3.TheoremThreeList G

theorem list_of_evenRank_le {S : Type} [Group S] [Finite S] (hT : ThreeCat) (hsimple : IsSimpleGroup S)
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hK : CFSG.IsKGroup S) (he : CFSG.Assembly.evenRank S ≤ 3) :
    Census3.TheoremThreeList S :=
  hT S ⟨hsimple, hnonab, hK, by rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]; exact he⟩

@[expose] def OddCentralCoverList : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsKGroup Y → Group.IsPerfect Y → CFSG.Assembly.evenRank Y ≤ 3 →
    ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      ∀ φ : Y →* S, Function.Surjective φ → φ.ker ≤ center Y → Odd (Nat.card φ.ker) →
        Census3.TheoremThreeList S

@[expose] def OddCentralCoverList3For (P : CFSGIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsKGroup Y → Group.IsPerfect Y → CFSG.Assembly.evenRank Y ≤ 3 →
    ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      ∀ φ : Y →* S, Function.Surjective φ → φ.ker ≤ center Y → IsPGroup 3 φ.ker → 3 ∣ Nat.card φ.ker →
        (∃ i : CFSGIndex, P i ∧ Nonempty (S ≃* i.Group)) → Census3.TheoremThreeList S

@[expose] def OddCentralCoverListFive : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsKGroup Y → Group.IsPerfect Y → CFSG.Assembly.evenRank Y ≤ 3 →
    Nat.card (center Y) = 5 → ∀ n : ℕ, 1 ≤ n → StatedClassicalModel (Y ⧸ center Y) .PSU 5 2 n →
      Census3.TheoremThreeList (Y ⧸ center Y)

theorem oddCentralCoverList3For_of_rank {P : CFSGIndex → Prop} (hT : ThreeCat)
    (h : OddCentralCoverRank3For P) : OddCentralCoverList3For P := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd hP
  have hSK : CFSG.IsKGroup S :=
    isKGroup_of_section hK ⊤ (φ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).toMonoidHom)
      (hφ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).surjective)
  exact list_of_evenRank_le hT inferInstance hnonab hSK (h Y hK hperf he S hnonab φ hφ hcent h3 h3dvd hP)

theorem oddCentralCoverList_of_split (h68 : Sec6EightMultipliers) (hbridge : TauCetiCatalogBridge)
    (hT : ThreeCat) (hAlt : OddCentralCoverList3For IsAlternatingIndex)
    (hSpor : OddCentralCoverList3For IsSporadicIndex) (hLie : OddCentralCoverList3For IsLieIndex)
    (h5 : OddCentralCoverListFive) : OddCentralCoverList := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent hodd
  obtain ⟨hker, hYq, ⟨hcongr⟩⟩ := central_cover_quasisimple hperf hnonab φ hφ hcent
  have hSK : CFSG.IsKGroup S :=
    isKGroup_of_section hK ⊤ (φ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).toMonoidHom)
      (hφ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).surjective)
  by_cases hbig : ∃ ℓ : ℕ, ℓ.Prime ∧ 3 < ℓ ∧ ℓ ∣ Nat.card φ.ker
  · obtain ⟨ℓ, hℓ, hℓ3, hdvd⟩ := hbig
    have hdvdZ : ℓ ∣ Nat.card (center Y) := by rw [hker]; exact hdvd
    obtain ⟨-, hc5, n, hn, hmodel⟩ := sec68_full h68 hbridge hK hYq he hℓ hℓ3 hdvdZ
    exact Census3.TheoremThreeList.of_mulEquiv hcongr (h5 Y hK hperf he hc5 n hn hmodel)
  · push Not at hbig
    have hne : Nat.card φ.ker ≠ 0 := Nat.card_pos.ne'
    have h3 : IsPGroup 3 φ.ker := by
      have hpow : Nat.card φ.ker = 3 ^ (Nat.card φ.ker).primeFactorsList.length := by
        refine Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) hne fun {d} hd hdd => ?_
        have hd2 : d ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdd)
        have := hbig d hd
        have := hd.two_le
        omega
      exact IsPGroup.of_card hpow
    by_cases hker1 : φ.ker = ⊥
    ·
      let eYS : Y ≃* S :=
        (QuotientGroup.quotientBot (G := Y)).symm.trans
          ((QuotientGroup.quotientMulEquivOfEq hker1).symm.trans
            (QuotientGroup.quotientKerEquivOfSurjective φ hφ))
      refine list_of_evenRank_le hT inferInstance hnonab hSK ?_
      rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank,
        ← Census3.twoLocalOddRank_eq_of_mulEquiv eYS,
        ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
      exact he
    have h3dvd : 3 ∣ Nat.card φ.ker := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h3
      rcases n with _ | n
      · exact absurd ((Subgroup.eq_bot_iff_card φ.ker).mpr (by simpa using hn)) hker1
      · rw [hn, pow_succ]
        exact dvd_mul_left 3 _
    let ψ : (⊤ : Subgroup Y) →* S := φ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).toMonoidHom
    have hψ : Function.Surjective ψ := hφ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).surjective
    let iso : ((⊤ : Subgroup Y) ⧸ ψ.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
    have hsimple : IsSimpleGroup ((⊤ : Subgroup Y) ⧸ ψ.ker) := iso.isSimpleGroup
    obtain ⟨i, ⟨e⟩⟩ := hK ⊤ ψ.ker hsimple
    have e' : S ≃* i.Group := iso.symm.trans e
    cases i with
    | cyclic p hp =>
      obtain ⟨a, b, hab⟩ := hnonab
      have hc : ∀ x y : (CFSGIndex.cyclic p hp).Group, x * y = y * x := fun x y => mul_comm x y
      exact absurd (e'.injective (by rw [map_mul, map_mul]; exact hc (e' a) (e' b))) hab
    | alternating n hn =>
      exact hAlt Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
        ⟨CFSGIndex.alternating n hn, by simp [IsAlternatingIndex], ⟨e'⟩⟩
    | lie d =>
      exact hLie Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
        ⟨CFSGIndex.lie d, by simp [IsLieIndex], ⟨e'⟩⟩
    | sporadic s =>
      exact hSpor Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
        ⟨CFSGIndex.sporadic s, by simp [IsSporadicIndex], ⟨e'⟩⟩

@[expose] def LowTwoRankSectionList : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsKGroup L → CFSG.Assembly.evenRank L ≤ 3 →
    ∀ (H : Subgroup L) (M : Type) [Group M] [Finite M], CFSG.IsQuasisimple M → ∀ π : H →* M,
      Function.Surjective π →
      (¬ ∃ U : Subgroup (M ⧸ center M), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (3 + 2)) →
        Census3.TheoremThreeList (M ⧸ center M) ∧
          ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ → ¬ ℓ ∣ Nat.card (center M)

@[expose] def LowTwoRankSectionListFor (P : CFSGIndex → Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsKGroup L → CFSG.Assembly.evenRank L ≤ 3 →
    ∀ (H : Subgroup L) (M : Type) [Group M] [Finite M], CFSG.IsQuasisimple M → ∀ π : H →* M,
      Function.Surjective π →
      (¬ ∃ U : Subgroup (M ⧸ center M), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (3 + 2)) →
      (∃ i : CFSGIndex, P i ∧ Nonempty ((M ⧸ center M) ≃* i.Group)) →
        Census3.TheoremThreeList (M ⧸ center M) ∧
          ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ → ¬ ℓ ∣ Nat.card (center M)

theorem lowTwoRankSectionListFor_of_rank {P : CFSGIndex → Prop} (hT : ThreeCat)
    (h : LowTwoRankSectionFor P) : LowTwoRankSectionListFor P := by
  intro L _ _ hK he H M _ _ hM π hπ hU hP
  obtain ⟨hrank, hcen⟩ := h L hK he H M hM π hπ hU hP
  have hMK : CFSG.IsKGroup M := isKGroup_of_section hK H π hπ
  have : IsSimpleGroup (M ⧸ center M) := hM.2.1
  exact ⟨list_of_evenRank_le hT hM.2.1 hM.2.2
    (CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hMK _) hrank, hcen⟩

theorem lowTwoRankSectionList_of_split (hAlt : LowTwoRankSectionListFor IsAlternatingIndex)
    (hSpor : LowTwoRankSectionListFor IsSporadicIndex) (hLie : LowTwoRankSectionListFor IsLieIndex) :
    LowTwoRankSectionList := by
  intro L _ _ hK he H M _ _ hM π hπ hU
  have : IsSimpleGroup (M ⧸ center M) := hM.2.1
  have hnonab : ∃ a b : M ⧸ center M, a * b ≠ b * a := hM.2.2
  have hπS : Function.Surjective ((QuotientGroup.mk' (center M)).comp π) :=
    (QuotientGroup.mk'_surjective _).comp hπ
  obtain ⟨i, ⟨e⟩⟩ := CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_isKGroup hK H
    (M ⧸ center M) ((QuotientGroup.mk' (center M)).comp π) hπS
  cases i with
  | cyclic p hp =>
    obtain ⟨a, b, hab⟩ := hnonab
    have hc : ∀ x y : (CFSGIndex.cyclic p hp).Group, x * y = y * x := fun x y => mul_comm x y
    exact absurd (e.injective (by rw [map_mul, map_mul]; exact hc (e a) (e b))) hab
  | alternating n hn =>
    exact hAlt L hK he H M hM π hπ hU ⟨CFSGIndex.alternating n hn, by simp [IsAlternatingIndex], ⟨e⟩⟩
  | lie d =>
    exact hLie L hK he H M hM π hπ hU ⟨CFSGIndex.lie d, by simp [IsLieIndex], ⟨e⟩⟩
  | sporadic s =>
    exact hSpor L hK he H M hM π hπ hU ⟨CFSGIndex.sporadic s, by simp [IsSporadicIndex], ⟨e⟩⟩

theorem sectionListBound_of_cases (hB : OddCentralCoverList) (hC : LowTwoRankSectionList)
    (h68 : Sec6EightMultipliers) (hbridge : TauCetiCatalogBridge) : SectionListBound := by
  intro L _ _ hK he H M _ _ hM π hπ
  by_cases hU : ∃ U : Subgroup (M ⧸ center M), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (3 + 2)
  · obtain ⟨Y, _, _, φ, hYperf, hYK, hYe, hφs, hcent, hodd, hprime⟩ :=
      section_cover_central_of_high_two_rank 3 he hK hM hU H π hπ
    have : IsSimpleGroup (M ⧸ center M) := hM.2.1
    have hnonab : ∃ a b : M ⧸ center M, a * b ≠ b * a := hM.2.2
    refine ⟨hB Y hYK hYperf hYe (M ⧸ center M) hnonab φ hφs hcent hodd, ?_⟩
    intro ℓ hℓ hℓ7 hdvd
    obtain ⟨hker, hYq, -⟩ := central_cover_quasisimple hYperf hnonab φ hφs hcent
    have hℓY : ℓ ∣ Nat.card (center Y) := by
      rw [hker]
      exact hprime ℓ hℓ (by omega) hdvd
    have := prime_dvd_center_eq_five h68 hbridge hYK hYq hYe hℓ (by omega) hℓY
    omega
  · exact hC L hK he H M hM π hπ hU

theorem sectionListBound_of_leaves (h68 : Sec6EightMultipliers) (hbridge : TauCetiCatalogBridge)
    (hT : ThreeCat)
    (hAltB : OddCentralCoverList3For IsAlternatingIndex) (hAltC : LowTwoRankSectionListFor IsAlternatingIndex)
    (hSporB : OddCentralCoverList3For IsSporadicIndex) (hSporC : LowTwoRankSectionListFor IsSporadicIndex)
    (hLieB : OddCentralCoverList3For IsLieIndex) (hLieC : LowTwoRankSectionListFor IsLieIndex)
    (h5 : OddCentralCoverListFive) : SectionListBound :=
  sectionListBound_of_cases (oddCentralCoverList_of_split h68 hbridge hT hAltB hSporB hLieB h5)
    (lowTwoRankSectionList_of_split hAltC hSporC hLieC) h68 hbridge

end CFSG.RankThree.PartOne.N143
