module

import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xn_pRank_le_one {M L : Subgroup G} (hL : L ∈ calC M) {n p : ℕ}
    (hU : IsU3 (Bar2 L) n) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p L ≤ 1 := by
  rw [← pRank_bar2_eq_of_odd hp hp2]
  haveI := PartTwo.s13_isSimple_of_isU3 hU
  have hZ : center (Bar2 L) = ⊥ := uc22p22a_center_eq_bot (PartTwo.s13_nonabelian_bar hL)
  have hinj : Function.Injective (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) := by
    rw [← MonoidHom.ker_eq_bot_iff,
      CFSG.EvenSporadicStandard.Induction.AutInner.ker_conj_eq_center, hZ]
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  have h := UCK.u3RankOne (Bar2 L) n (uc22p22d_isSU3_of_isU3 hL.2.2 hU) p hp hp2 hpn
    (E.map MulAut.conj) (Subgroup.map_le_range _ _) (CFSG.SectionRank.isElemAbelian_map hE _)
  rw [Subgroup.card_map_of_injective hinj] at h
  rw [pow_one]
  exact h

theorem uc22s13xn_three_lt {n q : ℕ} (hn : IsPowTwo n) (hn2 : 2 ≤ n) (hq : q.Prime)
    (hqd : q ∣ 2 ^ n + 1) : 3 < q := by
  obtain ⟨k, hk⟩ := hn
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  obtain ⟨j, hj⟩ : Even n := by
    rw [hk]
    exact (Nat.even_pow' hk0).2 even_two
  have h3 : (2 ^ n + 1) % 3 = 2 := by
    rw [hj, ← two_mul, pow_mul, Nat.add_mod, Nat.pow_mod]
    norm_num
  have h2 : (2 ^ n + 1) % 2 = 1 := by
    rw [Nat.add_mod, Nat.pow_mod]
    have hn0 : n ≠ 0 := by omega
    simp [Nat.zero_pow (Nat.pos_of_ne_zero hn0)]
  have hq2 : q ≠ 2 := by
    rintro rfl
    omega
  have hq3 : q ≠ 3 := by
    rintro rfl
    omega
  have := hq.two_le
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
