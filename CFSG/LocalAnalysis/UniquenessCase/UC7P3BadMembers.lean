module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadRows
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusAlt
import CFSG.RankThree.PartTwo.Sec4.RonanK432L2List

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree (gammaCore)

variable {L : Type} [Group L] [Finite L]

theorem false_of_isLinTwoIndex {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d) (e : L ≃* CatGroup d)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hF3 : ringChar (GaloisField p n) ≠ 3 := by
    rw [ringChar.eq (GaloisField p n) p]
    omega
  have hcard : 4 ≤ Nat.card (GaloisField p n) := by
    rw [GaloisField.card p n (by omega)]
    calc 4 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  have h1 := CFSG.RankThree.PartTwo.Sec4.RonanK432.pRank_psl2_le_one hF3 hcard
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (e.trans e₂)] at h4
  omega

theorem false_of_isUnitaryIndex (hUO : KFactUnitaryOrder) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (e : L ≃* CatGroup d)
    (hH : ThreeHeavy (Nat.card L)) : False := by
  have h := hUO L p d hd ⟨e⟩
  obtain ⟨q, -, hq⟩ := hd
  have hfe : d.1.fieldExponent = q.exponent := by rw [hq]; simp
  have hpos : d.1.fieldExponent ≠ 0 := by rw [hfe]; exact q.exponent_pos.ne'
  have h5 : 5 ≤ p ^ d.1.fieldExponent := hp5.trans (Nat.le_self_pow hpos p)
  have h3 : ¬ 3 ∣ p ^ d.1.fieldExponent := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  exact not_threeHeavy_unitary h5 h3 h hH

theorem false_of_isAltTwoP {p : ℕ} (hp5 : 5 ≤ p) (hA : IsAltTwoP p L) (hs : IsSimpleGroup L)
    (hnab : ∃ a b : L, a * b ≠ b * a) (R : Sylow 3 L)
    (hΓ : gammaCore 3 1 ⊤ (R : Subgroup L) < ⊤) : False := by
  obtain ⟨e⟩ := hA
  have hC := centralizer_top_eq_bot_of_simple hs hnab
  exact hΓ.ne (CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.gammaCore_eq_top_of_alt
    (X := L) (K := ⊤) (n := 2 * p) (by omega) (Subgroup.topEquiv.trans e) hC R)

@[expose] def BadListOrders : Prop :=
  (∀ (K : Type) [Group K], IsSimpleGroup K → IsSporadicGroup .McL K → Nat.card K = 898128000) ∧
  (∀ (K : Type) [Group K], IsSimpleGroup K → IsSporadicGroup .J4 K →
    Nat.card K = 86775571046077562880) ∧
  (∀ (K : Type) [Group K], IsSimpleGroup K → IsFi22 K → Nat.card K = 64561751654400) ∧
  (∀ (K : Type) [Group K], IsTitsGroup K → Nat.card K = 17971200) ∧
  (∀ (K : Type) [Group K], IsoLie K (.suzuki 2) → Nat.card K = 32537600)

theorem false_of_suzuki (hOrd : BadListOrders) (hiso : IsoLie L (.suzuki 2))
    (hH : ThreeHeavy (Nat.card L)) : False := by
  rw [hOrd.2.2.2.2 L hiso] at hH
  exact not_threeHeavy_sz32 hH

theorem false_of_isSmallStrongP (hOrd : BadListOrders) (hUO : KFactUnitaryOrder) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hs : IsSimpleGroup L) (hnab : ∃ a b : L, a * b ≠ b * a)
    (R : Sylow 3 L) (hΓ : gammaCore 3 1 ⊤ (R : Subgroup L) < ⊤)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) (hH : ThreeHeavy (Nat.card L))
    (hL : IsSmallStrongP p L) : False := by
  rcases hL with ⟨d, hd, ⟨e⟩⟩ | ⟨d, ⟨q, hqp, -, hq⟩, ⟨e⟩⟩ | hA | ⟨h3, -⟩ |
      ⟨-, hT | hM | hF⟩ | ⟨-, hJ⟩
  · exact false_of_isLinTwoIndex hp hp5 (by norm_num) hd e h4
  · exact false_of_isUnitaryIndex hUO hp hp5 ⟨q, hqp, hq⟩ e hH
  · exact false_of_isAltTwoP hp5 hA hs hnab R hΓ
  · omega
  · rw [hOrd.2.2.2.1 L hT] at hH
    exact not_threeHeavy_tits hH
  · rw [hOrd.1 L hs hM] at hH
    exact not_threeHeavy_mcl hH
  · rw [hOrd.2.2.1 L hs hF] at hH
    exact not_threeHeavy_fi22 hH
  · rw [hOrd.2.1 L hs hJ] at hH
    exact not_threeHeavy_j4 hH

theorem false_of_oneLieIdent (hUO : KFactUnitaryOrder) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) (hH : ThreeHeavy (Nat.card L))
    (hL : ∃ d : TauCeti.ValidLieTypeIndex,
      ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨
        (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨ IsReeGTwoIndex p d) ∧
      Nonempty (L ≃* CatGroup d)) : False := by
  obtain ⟨d, hd | ⟨hd, -⟩ | ⟨h3, -⟩, ⟨e⟩⟩ := hL
  · obtain ⟨n, hn, hd⟩ := hd
    exact false_of_isLinTwoIndex hp hp5 (by omega) hd e h4
  · exact false_of_isUnitaryIndex hUO hp hp5 hd e hH
  · omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
