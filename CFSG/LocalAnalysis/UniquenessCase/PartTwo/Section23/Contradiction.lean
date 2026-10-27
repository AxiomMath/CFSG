module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFitting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem etaSet_nonempty_of_two_le {n : ℕ} (hn : 2 ≤ n) : (etaSet n).Nonempty := by
  have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hne : 2 ^ n - 1 ≠ 1 := by
    have : 4 ≤ 2 ^ n := by simpa using hpow
    omega
  obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hne
  exact ⟨r, hrp, hrd⟩

theorem false_of_s23_43 (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hBB : c.B = c.B0) (h52 : S23_5_2 D Ch) (h5 : S23_5_3 D Ch) (h10 : S23_10 D Ch)
    (h43 : S23_43 D Ch) (hn : 2 ≤ CFSG.Open.pRank 2 D.Z) : False := by
  have hcn : 2 ≤ c.n := by
    rcases h52 h1930 c with h | ⟨-, -, h⟩
    · omega
    · omega
  obtain ⟨hcyc, hsigF⟩ := h43 h1930 c
  have hpiB : piSet c.B = etaSet c.n := by
    rw [hBB]
    exact c.hpi
  have hηne : (etaSet c.n).Nonempty := etaSet_nonempty_of_two_le hcn
  have hBne : c.B ≠ ⊥ := by
    intro hbot
    obtain ⟨r, hr⟩ := hηne
    have : r ∈ piSet c.B := by rw [hpiB]; exact hr
    rw [hbot] at this
    simp only [piSet, Set.mem_setOf_eq, Subgroup.card_bot] at this
    exact hr.1.not_dvd_one this.2
  have hBZ : ⁅c.B, D.Z⁆ ≠ ⊥ := by
    intro hbot
    have hle : c.B ≤ Subgroup.centralizer (D.Z : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hCB : c.B ⊓ Subgroup.centralizer (D.Z : Set G) = c.B := inf_eq_left.mpr hle
    rcases h5 h1930 c hpiB with htriv | ⟨hcn2, hpiCB⟩
    · exact hBne (hCB.symm.trans htriv)
    ·
      have hne : 2 ^ (CFSG.Open.pRank 2 D.Z) - 1 ≠ 1 := by
        have hpow : 2 ^ 2 ≤ 2 ^ (CFSG.Open.pRank 2 D.Z) :=
          Nat.pow_le_pow_right (by norm_num) hn
        have : 4 ≤ 2 ^ (CFSG.Open.pRank 2 D.Z) := by simpa using hpow
        omega
      obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hne
      have hrd2 : r ∣ 2 ^ (2 * CFSG.Open.pRank 2 D.Z) - 1 :=
        hrd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left _ 2))
      have hreta : r ∈ etaSet (2 * CFSG.Open.pRank 2 D.Z) := ⟨hrp, hrd2⟩
      have hrpiB : r ∈ piSet c.B := by
        rw [hpiB, hcn2]
        exact hreta
      have hpiBplus : piSet c.B = {p | p.Prime ∧ p ∣ 2 ^ (CFSG.Open.pRank 2 D.Z) + 1} := by
        rw [← hCB]
        exact hpiCB
      have hrplus : r ∣ 2 ^ (CFSG.Open.pRank 2 D.Z) + 1 := by
        rw [hpiBplus] at hrpiB
        exact hrpiB.2
      have hcop : Nat.Coprime (2 ^ CFSG.Open.pRank 2 D.Z - 1)
          (2 ^ CFSG.Open.pRank 2 D.Z + 1) :=
        uc22pwsu3_coprime_two_pow (by omega)
      exact hrp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hrd hrplus)
  obtain ⟨p, hpσ, P, hPsyl, hnotcent⟩ := h10 h1930 c hcyc hBZ
  have hpprime : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨Q, hQP⟩ := hPsyl
  have hPle : P ≤ CFSG.fittingSubgroup (Bar2 D.M) := by
    rw [← hQP]
    exact Subgroup.map_subtype_le (Q : Subgroup ↥(CFSG.fittingSubgroup (Bar2 D.M)))
  have hPp : IsPGroup p ↥P := by
    rw [← hQP]
    exact Q.isPGroup'.map (CFSG.fittingSubgroup (Bar2 D.M)).subtype
  have hPne : P ≠ ⊥ := by
    intro hPbot
    apply hnotcent
    rw [hPbot]
    have htop : Subgroup.centralizer ((⊥ : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) = ⊤ := by
      simp
    rw [htop]
    exact le_top
  have hPcard := IsPGroup.iff_card.mp hPp
  obtain ⟨k, hk⟩ := hPcard
  have hkpos : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero] at hk
    exact hPne ((Subgroup.card_eq_one).mp hk)
  have hpdivP : p ∣ Nat.card ↥P := by
    rw [hk]
    exact dvd_pow_self p (Nat.ne_of_gt hkpos)
  have hpdivF : p ∣ Nat.card ↥(CFSG.fittingSubgroup (Bar2 D.M)) :=
    dvd_trans hpdivP (Subgroup.card_dvd_of_le hPle)
  exact hsigF p hpσ hpdivF

end CFSG.LocalAnalysis.UniquenessCase.UC22
