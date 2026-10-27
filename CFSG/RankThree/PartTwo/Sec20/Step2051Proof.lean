module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec20.Alt20

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_mul_of_not_four_dvd {T S Y M : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S Y)
    (hYM : Y ≤ M) (h4 : ¬ 4 ∣ Y.relIndex M) : Nat.card T ≤ 2 * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hT.card_eq, hS.card_eq]
  have hYM' := Subgroup.relIndex_mul_card Y M
  rw [inf_eq_left.mpr hYM] at hYM'
  have hidx0 : Y.relIndex M ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hYM'
    exact (Nat.card_pos (α := M)).ne' hYM'.symm
  have hY0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card M).factorization 2 =
      (Y.relIndex M).factorization 2 + (Nat.card Y).factorization 2 := by
    rw [← hYM', Nat.factorization_mul hidx0 hY0, Finsupp.add_apply]
  have hle : (Y.relIndex M).factorization 2 ≤ 1 := by
    by_contra h
    push Not at h
    apply h4
    have : 2 ^ 2 ∣ Y.relIndex M :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hidx0).mpr h
    simpa using this
  rw [hfac, pow_add]
  calc 2 ^ (Y.relIndex M).factorization 2 * 2 ^ (Nat.card Y).factorization 2
      ≤ 2 ^ 1 * 2 ^ (Nat.card Y).factorization 2 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hle)
    _ = 2 * 2 ^ (Nat.card Y).factorization 2 := by rw [pow_one]

theorem card_le_of_isSylowOf_top {R T : Subgroup G} (hR : IsPGroup 2 R)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) : Nat.card R ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hT', hRT'⟩ := exists_isSylowOf_le hR (le_top : R ≤ ⊤)
  calc Nat.card R ≤ Nat.card T' := Subgroup.card_le_of_le hRT'
    _ = Nat.card T := by rw [hT'.card_eq, hT.card_eq]

theorem step2051_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hK : KType20 M N c)
    (hidx : (∃ n : ℕ, Odd n ∧
        Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) ∧
        Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
          (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c))))) →
      ¬ 4 ∣ (M ⊓ N).relIndex M)
    (hsyl : ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 R N →
      CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ M) (M ⊓ N) → (R ⊓ M).relIndex R = 8) :
    ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
  intro hTG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : ¬ 4 ∣ (M ⊓ N).relIndex M := by
    rcases hK with h | ⟨n, -, -, -, hidx'⟩
    · exact hidx h
    · exact hidx'
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (M ⊓ N)
  obtain ⟨R, hR, hSR⟩ := exists_isSylowOf_le hS.isPGroup (hS.le.trans inf_le_right)
  have heq : R ⊓ M = S :=
    hS.eq_of_le (le_inf hSR (hS.le.trans inf_le_left))
      (le_inf inf_le_right (inf_le_left.trans hR.le))
      (hR.isPGroup.to_le inf_le_left)
  have hRM : CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ M) (M ⊓ N) := heq ▸ hS
  have h8 := hsyl R hR hRM
  have hRS : Nat.card R = 8 * Nat.card S := by
    have := Subgroup.relIndex_mul_card (R ⊓ M) R
    rw [inf_eq_left.mpr (inf_le_left : R ⊓ M ≤ R), h8, heq] at this
    exact this.symm
  have h1 := card_le_of_isSylowOf_top hR.isPGroup hTG
  have h2 := card_le_two_mul_of_not_four_dvd hT.sylow hS inf_le_left h4
  have hSpos : 0 < Nat.card S := Nat.card_pos
  omega

theorem step2051_of (h189 : Sec18.Item189) (hidx : Step2051Index) (hsyl : Step2051Sylow) :
    Step2051 := by
  intro G _ _ A M L N c T hT
  obtain ⟨H, hH18, hH187, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  obtain ⟨-, -, hcase⟩ := h189 G A M H c hH18 hH187
  rw [← hL, ← hN] at hcase
  exact step2051_core hT.toCtx20 hcase (hidx G A M L N c T hT) (hsyl G A M L N c T hT)

end CFSG.RankThree.PartTwo.Sec20
