module

public import CFSG.Quasithin.Background.RonanD321Inv
public import CFSG.Quasithin.Background.RonanD321Qhat
public import CFSG.Quasithin.Background.RonanD321Five
public import CFSG.Quasithin.Background.RonanD321Cent
public import CFSG.Quasithin.Background.RonanD321Two
public import CFSG.Quasithin.Background.SmithD321Holds

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD391 CFSG.Open
  CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique


theorem d321c_holds
    :
    ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
      D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
        Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
          orbSup T V = ⊤ ∨
          (IsPSL 3 2 1 ↥L ∧ IsIntDirect (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
            commV L = fixV (conjAutSub t L) ∧
            DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 ∧
            (∀ A ∈ QhatStar M, A ≤ stabSub (commV L)) ∧
            (Nat.card ↥(twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 5 ∨
              (IsElemAbelian 5 (twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) ∧
                Nat.card ↥(twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 25))) ∨
          ((∃ n : ℕ, IsPSL 2 2 n ↥L) ∧
            IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
            commV L ≤ fixV (conjAutSub t L) ∧
            (∃ n : ℕ, IsPSL 2 2 n ↥L ∧
              ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
                DirectSumOfCopies L (commV L) (commV L ⊓ fixV Mp) (FFModel.nat (StatedSL 2 K)) 2) ∧
            M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ ∧
            ∃ I ∈ IrrPlus L (commV L),
              M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub I) := by
  intro W _ _ M Mp T L V hD t htT htn hMp hqM
  by_cases htop : orbSup T V = ⊤
  · exact Or.inl htop
  right
  have hB : D321Base M Mp T L V t := d321Base_of (d3L38_of_a38 d3A38_holds) hD htT htn hMp
  rcases d321_holds W M Mp T L V hD t htT htn hMp hqM with h | ⟨hsum, hle, h2 | h3⟩
  · exact absurd h htop
  · left
    have h3L : 3 ∣ Nat.card ↥L := H13.three_dvd_card_of_isPSL_three_two h2.1
    exact ⟨h2.1, isIntDirect_of_d321Two hB h2 hsum, commV_eq_fixV_of_d321Two hB h2 hle, h2.2,
      qhatStar_le_stabSub hB hqM htop h3L, twoResidual_of_d321Two hB hqM htop h2 hsum hle⟩
  · right
    have hcent := cent_eq_bot_of_d321Three hB h3
    obtain ⟨n, hn, -⟩ := id h3
    exact ⟨⟨n, hn⟩, hsum, hle, h3, hcent, exists_inv_irrPlus hB h3 hle hcent⟩

end CFSG.Quasithin.RonanD321
