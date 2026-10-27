module

public import CFSG.Walter.Models
public import CFSG.GH74.KGroups.PSL2
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups
public import CFSG.GH74.Orders.LieType
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped MatrixGroups

theorem s13_Cert13_ordA_one (q : ℕ) :
    CFSG.Open.ordA 1 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
  simp [CFSG.Open.ordA]

theorem s13_Cert13_gcd_two_pow (n : ℕ) (hn : 1 ≤ n) :
    Nat.gcd 2 (2 ^ n - 1) = 1 := by
  have h2n : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow' n 1) h2n odd_one
  exact Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_left.mpr hodd)

theorem s13_isL2_two_of_isL2Odd_five {X : Type} [Group X]
    (h : IsL2Odd X 5) : IsL2 X 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 5 1) 5 1
    (by norm_num) (GaloisField.card 5 1 (by norm_num)) h
  obtain ⟨e5⟩ := CFSG.Walter.nonempty_psl2_five_mulEquiv_psl2_four
  obtain ⟨-, hc | ⟨hn, -⟩⟩ :=
    CFSG.Walter.lieModel_psl_two_of_mulEquiv 2 2 (by norm_num) (e.trans e5)
  · exact Or.inl ⟨by decide, hc⟩
  · exact absurd hn (by decide)

theorem s13_dvd_card_of_isL2_or_isSz {X : Type} [Group X]
    [Finite X] {n s r : ℕ} (hX : IsL2 X n ∨ IsSz X n) (hs : s ∣ n) (hr : r.Prime)
    (hrd : r ∣ 2 ^ s - 1) : r ∣ Nat.card X := by
  have hdvd : r ∣ 2 ^ n - 1 := hrd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hs)
  rcases hX with h | h
  · have hcard : Nat.card X = CFSG.Open.ordA 1 (2 ^ n) :=
      CFSG.GH74.card_of_lieModel_PSL (G := X) (n := 2) (p := 2) (f := n) (by norm_num) h
    have hn1 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible h).2.1
    rw [hcard, s13_Cert13_ordA_one, s13_Cert13_gcd_two_pow n hn1, Nat.div_one]
    exact hdvd.trans
      (dvd_mul_of_dvd_right (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2) (2 ^ n))
  · rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hsuz⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · obtain ⟨-, a, ha, hn, hcard⟩ := CFSG.GH74.card_of_suzukiModel hsuz
      rw [hcard]
      refine hdvd.trans ⟨(2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1), ?_⟩
      rw [CFSG.Open.ordSuzuki]
      exact Nat.mul_comm _ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
