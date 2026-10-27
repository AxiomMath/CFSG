module

public import CFSG.RankThree.PartTwo.Census.Interface
import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.BenderSuzuki.MatrixGroups

@[expose] noncomputable def suzukiTitsAut (m : ℕ) :
    GaloisField 2 (2 * m + 1) ≃+* GaloisField 2 (2 * m + 1) :=
  RingEquiv.ofBijective (iterateFrobenius (GaloisField 2 (2 * m + 1)) 2 (m + 1))
    (Finite.injective_iff_bijective.mp
      (iterateFrobenius (GaloisField 2 (2 * m + 1)) 2 (m + 1)).injective)

theorem suzukiTitsAut_apply (m : ℕ) (x : GaloisField 2 (2 * m + 1)) :
    suzukiTitsAut m x = x ^ 2 ^ (m + 1) :=
  rfl

theorem card_suzukiMatrixGroup {m : ℕ} (hm : 0 < m) :
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) :=
  (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_3 m hm (suzukiTitsAut m)
    (suzukiTitsAut_apply m)).2.2.2.2.2.2.1

theorem two_pow_odd_mod_three (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem not_three_dvd_card_suzukiMatrixGroup {m : ℕ} (hm : 0 < m) :
    ¬ 3 ∣ Nat.card (SuzukiMatrixGroup m) := by
  rw [card_suzukiMatrixGroup hm]
  set q := 2 ^ (2 * m + 1) with hq
  have h3 : q % 3 = 2 := two_pow_odd_mod_three m
  have h1 : 1 ≤ q := Nat.one_le_two_pow
  have hsq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h' | h'
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h' with h'' | h''
    · omega
    · omega
  · omega

theorem excluded433_suzuki (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    Excluded433 (.lie ⟨.suzuki m, hv⟩) := by
  intro G _ _ hG e
  have hm : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  refine hG.false_of_localRank_three_le_two
    (e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv))
    (localRank_le_of_pRank_le Nat.prime_three (pRank_le_two_of_not_dvd Nat.prime_three ?_))
  intro h
  exact not_three_dvd_card_suzukiMatrixGroup hm (dvd_trans (dvd_pow_self 3 (by norm_num)) h)

theorem item433Case_suzuki (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    Item433Case (.lie ⟨.suzuki m, hv⟩) :=
  (excluded433_suzuki m hv).item433Case

end CFSG.RankThree.PartTwo.Census
