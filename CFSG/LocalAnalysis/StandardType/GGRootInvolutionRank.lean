module

public import CFSG.LieType.Universal.Catalog
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section

theorem lieUniversal_rank_eq_bnRank (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime)
    (hadm : StatedLieAdmissible t n p f) (hrank : 3 ≤ bnRank t n) :
    (lieUniversal t n p f hp).D.rank = bnRank t n := by
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [bnRank] at hrank; omega⟩
    show m = m + 1 - 1
    omega
  | PSU =>
    have : Fact p.Prime := ⟨hp⟩
    have e : lieUniversal .PSU n p f hp =
        ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * f)) p f) n,
          Unitary.rootDatum (card_galoisField_two_mul p f hf) n⟩ := by
      simp only [lieUniversal, hf, ↓reduceDIte]
    rw [e]
    rfl
  | PSp => rfl
  | POmegaOdd => rfl
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    have : Fact p.Prime := ⟨hp⟩
    have e : lieUniversal .POmegaPlus n p f hp =
        ⟨spinGroup (Spin.quadPlus n (GaloisField p f)), Spin.plusDatum n (GaloisField p f) hn⟩ := by
      simp only [lieUniversal, hn, ↓reduceDIte]
    rw [e]
    rfl
  | POmegaMinus => rfl
  | F4 => rfl
  | E6 => rfl
  | E7 => rfl
  | E8 => rfl
  | twistedE6 => rfl
  | G2 => simp [bnRank] at hrank
  | trialityD4 => simp [bnRank] at hrank
  | twistedB2 => simp [bnRank] at hrank
  | twistedG2 => simp [bnRank] at hrank
  | twistedF4 => simp [bnRank] at hrank
  | Tits => simp [bnRank] at hrank

theorem two_le_lieUniversal_rank (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime)
    (hadm : StatedLieAdmissible t n p f) (hrank : 3 ≤ bnRank t n) :
    2 ≤ (lieUniversal t n p f hp).D.rank := by
  rw [lieUniversal_rank_eq_bnRank t n p f hp hadm hrank]
  omega

theorem lieUniversal_rank_eq_zero (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) :
    (lieUniversal t n p f hp).D.rank = 0 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

end CFSG.StandardType
