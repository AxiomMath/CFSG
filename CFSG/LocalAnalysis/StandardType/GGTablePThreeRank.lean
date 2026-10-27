module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankBound
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRest

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem labelAll_mono {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (hPP' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → P' R I F)
    (h : LargeEvenLabelAll lab P) : LargeEvenLabelAll lab P' := fun Q hQ =>
  largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.1, hPP' R I F hq.2⟩) (h Q hQ)

section Rank

variable {G : Type} [Group G] [Finite G]

theorem succ_le_twoLocalRank_of_marking_torusLift {B : Subgroup G} {x : G} {L : Subgroup G}
    (hI : GGThmIHyp 3 B x L) {S : LargeEvenLabel → Prop} {r : ℕ}
    (hS : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 r R)
    (hM : LargeEvenMarking ↥L fun lab _ _ _ _ _ => S lab) :
    r + 1 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨hL, lab, R, _, I, F, θ, hlab, hSlab, hlift⟩ :=
    largeEvenMarking_exists'
      (largeEvenMarking_and_labelAll (S := S) (P := fun lab _ _ _ _ _ => S lab) hS
        (fun _ _ _ _ _ _ h => h) hM)
  have hstar := hI.2.2.2.2.2.2.1
  exact succ_le_twoLocalRank_of_torusLift Nat.prime_three hstar.2.2.2.1.1
    (hstar.1.1.2 x hstar.2.1) hstar.2.2.1 hL θ hlift

end Rank

section Instances

variable {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G} {L : Subgroup G}

theorem six_le_twoLocalRank_of_tablePThree_E6
    (hI : GGThmIHyp 3 B x L)
    (hM : LargeEvenMarking ↥L fun lab _ _ _ _ _ => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) :
    6 ≤ LargeEvenTwoLocalRank 3 G := by
  have h := succ_le_twoLocalRank_of_marking_torusLift
    (S := fun lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) (r := 5) hI
    (fun lab _ hx => largeEvenLabelAll_torusLift_E6_three hx.1 hx.2) hM
  omega

theorem eight_le_twoLocalRank_of_tablePThree_A8 (hI : GGThmIHyp 3 B x L)
    (hM : LargeEvenMarking ↥L fun lab _ _ _ _ _ =>
      lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) :
    8 ≤ LargeEvenTwoLocalRank 3 G := by
  have h := succ_le_twoLocalRank_of_marking_torusLift
    (S := fun lab => lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) (r := 7) hI
    (fun lab _ hx => by
      have hrank : lab.rank = 8 := hx.2.1
      exact labelAll_mono (P := fun R _ _ _ => GGTorusLift 3 (lab.rank + 1 - 2) R)
        (fun R _ _ _ hq => by
          have h7 : lab.rank + 1 - 2 = 7 := by omega
          rwa [h7] at hq)
        (largeEvenLabelAll_torusLift_typeA Nat.prime_three hx.1 (by omega) hx.2.2)) hM
  omega

theorem seven_le_twoLocalRank_of_tablePThree_twA8
    (hI : GGThmIHyp 3 B x L)
    (hM : LargeEvenMarking ↥L fun lab _ _ _ _ _ =>
      lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) :
    7 ≤ LargeEvenTwoLocalRank 3 G := by
  have h := succ_le_twoLocalRank_of_marking_torusLift
    (S := fun lab => lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) (r := 6) hI
    (fun lab hlab hx => by
      have hrank : lab.rank = 8 := hx.2.1
      exact labelAll_mono
        (P := fun R _ _ _ => GGTorusLift 3 (ggUnitaryTorusRank 3 (lab.rank + 1)) R)
        (fun R _ _ _ hq => by
          have h6 : ggUnitaryTorusRank 3 (lab.rank + 1) = 6 := by
            rw [hrank]
            norm_num [ggUnitaryTorusRank]
          rwa [h6] at hq)
        (largeEvenLabelAll_torusLift_twA hlab hx.1 Nat.prime_three hx.2.2)) hM
  omega

theorem five_le_twoLocalRank_of_tablePThree_A5 (hI : GGThmIHyp 3 B x L)
    (hM : LargeEvenMarking ↥L fun lab _ _ _ _ _ =>
      lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  have h := succ_le_twoLocalRank_of_marking_torusLift
    (S := fun lab => lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) (r := 4) hI
    (fun lab _ hx => by
      have hrank : lab.rank = 5 := hx.2.1
      exact labelAll_mono (P := fun R _ _ _ => GGTorusLift 3 (lab.rank + 1 - 2) R)
        (fun R _ _ _ hq => by
          have h4 : lab.rank + 1 - 2 = 4 := by omega
          rwa [h4] at hq)
        (largeEvenLabelAll_torusLift_typeA Nat.prime_three hx.1 (by omega) hx.2.2)) hM
  omega

theorem six_le_twoLocalRank_of_tablePThree_D6
    (hI : GGThmIHyp 3 B x L)
    (hM : LargeEvenMarking ↥L fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) :
    6 ≤ LargeEvenTwoLocalRank 3 G := by
  have h := succ_le_twoLocalRank_of_marking_torusLift
    (S := fun lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) (r := 5) hI
    (fun lab _ hx => by
      have hrank : lab.rank = 6 := hx.2.1
      have hO : GGOrthRestLabel 3 lab := ⟨by omega, Or.inr ⟨hx.1, hx.2.2, rfl⟩⟩
      exact labelAll_mono
        (P := fun R _ I _ => I = LargeEvenInnSet R ∧ GGTorusLift 3 (lab.rank - 1) R)
        (fun R _ I F hq => by
          have h5 : lab.rank - 1 = 5 := by omega
          rw [h5] at hq
          exact hq.2)
        (OrthRest.labelAll ggOrthRestTorusLiftInput_holds Nat.prime_three hO)) hM
  omega

theorem seven_le_twoLocalRank_of_tablePThree_twD7
    (hI : GGThmIHyp 3 B x L)
    (hM : LargeEvenMarking ↥L fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) :
    7 ≤ LargeEvenTwoLocalRank 3 G := by
  have h := succ_le_twoLocalRank_of_marking_torusLift
    (S := fun lab => lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) (r := 6) hI
    (fun lab _ hx => by
      have hrank : lab.rank = 7 := hx.2.1
      have hO : GGOrthRestLabel 3 lab :=
        ⟨by omega, Or.inl ⟨hx.1, by rw [hx.2.2]; norm_num⟩⟩
      exact labelAll_mono
        (P := fun R _ I _ => I = LargeEvenInnSet R ∧ GGTorusLift 3 (lab.rank - 1) R)
        (fun R _ I F hq => by
          have h6 : lab.rank - 1 = 6 := by omega
          rw [h6] at hq
          exact hq.2)
        (OrthRest.labelAll ggOrthRestTorusLiftInput_holds Nat.prime_three hO)) hM
  omega

end Instances

end CFSG.StandardType
