module

public import CFSG.RankThree.PartTwo.Sec17.G1724J2
public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace G1724

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem two_le_pRank_five_of_cover
    {Y D : Subgroup G} (hDY : D ≤ Y)
    (hcov : Y = D ⊔ CFSG.Open.pCoreOf 2 Y)
    (hYJ : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥D) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₁⟩ := Proof17Res3.nonempty_quotient_pCore_two_equiv hDY hcov
  obtain ⟨e₂⟩ := hYJ
  have e : ↥D ⧸ CFSG.pCore 2 ↥D ≃* CFSG.Blueprint.NativeSporadic.J2 := e₁.symm.trans e₂
  have hN : ¬ 5 ∣ Nat.card (CFSG.pCore 2 ↥D) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥D))
    rw [hm]
    intro h
    have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
    omega
  calc 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.J2) :=
        two_le_pRank_five_J2
    _ = CFSG.Open.pRank 5 (⊤ : Subgroup (↥D ⧸ CFSG.pCore 2 ↥D)) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e).symm
    _ = CFSG.Open.pRank 5 (⊤ : Subgroup ↥D) :=
        CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥D) hN

end G1724

end CFSG.RankThree.PartTwo.Sec17
