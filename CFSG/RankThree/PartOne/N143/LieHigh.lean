module

public import CFSG.RankThree.PartOne.N143.LieLeaves
import CFSG.RankThree.PartOne.N143.LieThree
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartOne.S11c.HigherLinearSmall
import CFSG.RankThree.PartOne.S11c.HigherUnitarySmall
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti Subgroup

@[expose] def IsLieHighEvenIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card - 1 ∧ q.p = 2
  | .lie ⟨.twistedA r q, _⟩ => 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card + 1 ∧ q.p = 2
  | _ => False

@[expose] def topCenterEquiv (Y : Type) [Group Y] :
    (↥(⊤ : Subgroup Y) ⧸ center ↥(⊤ : Subgroup Y)) ≃* (Y ⧸ center Y) :=
  QuotientGroup.congr _ _ (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)
    (Subgroup.map_center_eq (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y))

theorem oddCentralCoverRank3For_lieHigh (hEven : OddCentralCoverRank3For IsLieHighEvenIndex) :
    OddCentralCoverRank3For IsLieHighIndex := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  obtain ⟨hker, hYq, ⟨hcongr⟩⟩ := central_cover_quasisimple hperf hnonab φ hφ hcent
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsLieHighIndex])
  | alternating n hn => exact absurd hi (by simp [IsLieHighIndex])
  | sporadic s => exact absurd hi (by simp [IsLieHighIndex])
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      obtain ⟨h5, h3r, hq3⟩ : 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card - 1 := hi
      by_cases hq2 : q.p = 2
      · exact hEven Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
          ⟨CFSGIndex.lie ⟨.A r q, hv⟩, ⟨h5, h3r, hq3, hq2⟩, ⟨e⟩⟩
      · exfalso
        have hp3 : q.p ≠ 3 := ne_three_of_dvd_pow_sub_one_or_add_one q.exponent_pos
          (Or.inl (by simpa [PrimePower.card_def] using hq3))
        have eM : (↥(⊤ : Subgroup Y) ⧸ center ↥(⊤ : Subgroup Y)) ≃*
            (CFSGIndex.lie ⟨.A r q, hv⟩).Group := ((topCenterEquiv Y).trans hcongr).trans e
        have hmod := statedClassicalModel_of_isoLie_A hv eM
        have hrank : localRank q.p Y ≤ 3 :=
          (CFSG.RankThree.OddKernel.localRank_le_evenRank q.prime_p hq2).trans he
        have := CFSG.RankThree.PartOne.linear_small_parameters (X := Y) (Y := ⊤) (n := r + 1)
          (ℓ := q.p) (f := q.exponent) (by omega) q.prime_p hq2 hmod hrank
        rcases this.1 with h | ⟨h, -⟩
        · omega
        · exact hp3 h
    | twistedA r q =>
      obtain ⟨h5, h3r, hq3⟩ : 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card + 1 := hi
      by_cases hq2 : q.p = 2
      · exact hEven Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
          ⟨CFSGIndex.lie ⟨.twistedA r q, hv⟩, ⟨h5, h3r, hq3, hq2⟩, ⟨e⟩⟩
      · exfalso
        have hp3 : q.p ≠ 3 := ne_three_of_dvd_pow_sub_one_or_add_one q.exponent_pos
          (Or.inr (by simpa [PrimePower.card_def] using hq3))
        have eM : (↥(⊤ : Subgroup Y) ⧸ center ↥(⊤ : Subgroup Y)) ≃*
            (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group := ((topCenterEquiv Y).trans hcongr).trans e
        have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv eM
        have hrank : localRank q.p Y ≤ 3 :=
          (CFSG.RankThree.OddKernel.localRank_le_evenRank q.prime_p hq2).trans he
        have := CFSG.RankThree.PartOne.unitary_small_parameters (X := Y) (Y := ⊤) (n := r + 1)
          (ℓ := q.p) (f := q.exponent) (by omega) q.prime_p hq2 hmod hrank
        rcases this.1 with h | ⟨h, -⟩
        · omega
        · exact hp3 h
    | B r q => exact absurd hi (by simp [IsLieHighIndex])
    | C r q => exact absurd hi (by simp [IsLieHighIndex])
    | D r q => exact absurd hi (by simp [IsLieHighIndex])
    | twistedD r q => exact absurd hi (by simp [IsLieHighIndex])
    | E6 q => exact absurd hi (by simp [IsLieHighIndex])
    | E7 q => exact absurd hi (by simp [IsLieHighIndex])
    | E8 q => exact absurd hi (by simp [IsLieHighIndex])
    | F4 q => exact absurd hi (by simp [IsLieHighIndex])
    | G2 q => exact absurd hi (by simp [IsLieHighIndex])
    | twistedE6 q => exact absurd hi (by simp [IsLieHighIndex])
    | trialityD4 q => exact absurd hi (by simp [IsLieHighIndex])
    | suzuki m => exact absurd hi (by simp [IsLieHighIndex])
    | reeG2 m => exact absurd hi (by simp [IsLieHighIndex])
    | reeF4 m => exact absurd hi (by simp [IsLieHighIndex])
    | tits => exact absurd hi (by simp [IsLieHighIndex])

end CFSG.RankThree.PartOne.N143
