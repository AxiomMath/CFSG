module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.U3Rank
public import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem pRank_bar2_eq_of_odd {Y : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 Y)) = CFSG.Open.pRank p Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥Y) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) Y,
    ← CFSG.SectionRank.pRank_quotient_eq (p := p) (CFSG.pCore 2 ↥Y) hN]

theorem pRank_le_one_of_isL2_or_isSz {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : IsL2 X f ∨ IsSz X f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  rcases hX with hL2 | hSz
  · exact CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even
      (CFSG.Blueprint.LieModel.statedClassicalModel hL2 (by decide)) hp hp2
  · rcases hSz with ⟨hclass, -⟩ | ⟨-, hec, -⟩ | ⟨-, hrt, -⟩ | ⟨-, -, hsuz⟩
    · exact absurd hclass (by decide)
    · exact absurd hec (by decide)
    · exact absurd hrt (by decide)
    · exact CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki hsuz hp hp2

theorem two_le_pRank_three_of_isSU3 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsSU3 X n) (hn : Odd n) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hSCM : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX.2 (by decide)
  exact CFSG.GroupTheory.two_le_pRank_of_quotient (Subgroup.center X) Nat.prime_three
    (by norm_num)
    (CFSG.HardMathSupport.Timmesfeld.Tables.Census.two_le_pRank_three_psu_three_two_pow_odd
      (S := X ⧸ Subgroup.center X) hn hSCM)

end CFSG.LocalAnalysis.UniquenessCase.UC22
