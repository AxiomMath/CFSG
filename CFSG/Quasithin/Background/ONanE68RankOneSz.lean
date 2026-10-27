module

public import CFSG.Open.Catalog
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.Quasithin.E6.E68Proof

namespace RankOne

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

private noncomputable def titsAut (a : ℕ) :
    GaloisField 2 (2 * a + 1) ≃+* GaloisField 2 (2 * a + 1) :=
  RingEquiv.ofBijective (iterateFrobenius (GaloisField 2 (2 * a + 1)) 2 (a + 1))
    (Finite.injective_iff_bijective.mp
      (iterateFrobenius (GaloisField 2 (2 * a + 1)) 2 (a + 1)).injective)

private theorem two_pow_odd_mod_three (a : ℕ) : 2 ^ (2 * a + 1) % 3 = 2 := by
  induction a with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem not_three_dvd_card_sz {a : ℕ} (ha : 1 ≤ a) : ¬ 3 ∣ Nat.card (Sz a) := by
  have hcard := (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_3 a ha (titsAut a)
    fun x => rfl).2.2.2.2.2.2.1
  have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
  have e : Sz a = SuzukiMatrixGroup a := hmodel.symm.trans (szModel_eq_suzukiMatrixGroup a)
  rw [Nat.card_congr (MulEquiv.subgroupCongr e).toEquiv, hcard]
  set q := 2 ^ (2 * a + 1) with hq
  have h3 : q % 3 = 2 := two_pow_odd_mod_three a
  have h1 : 1 ≤ q := Nat.one_le_two_pow
  have hsq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h' | h'
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h' with h'' | h''
    · omega
    · omega
  · omega

end RankOne

end CFSG.Quasithin.E6.E68Proof
