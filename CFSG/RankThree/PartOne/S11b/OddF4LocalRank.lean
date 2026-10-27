module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.PartOne.S11b.OddF4Cover
public import CFSG.RankThree.PartOne.S11b.OddF4Roots
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.RankThreeEven (localRank)

theorem oddF4ActualCoverLocalRankFour : OddF4ActualCoverLocalRankFour := by
  intro X _ _ Y p f hp hp2 hf hmod
  obtain ⟨K, _, _, hK, φ, hφ, hker⟩ :=
    CFSG.RankThree.Chevalley.exists_surj_adjointGroup_of_model hmod.2
  have : Fact p.Prime := ⟨hp⟩
  have hchar : ringChar K = p := CFSG.RankThree.Chevalley.ringChar_eq_of_card hp hf hK
  have : CharP K p := ringChar.eq_iff.mp hchar
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  obtain ⟨hz, hzU⟩ := oddF4SixUC_comm_torus K h2
  exact oddF4_cover_six_local_rank Y hφ hker.le hp hp2 (oddF4SixUC_isElementaryAbelian K)
    (r := f * 6) (by rw [oddF4SixUC_card, hK, ← pow_mul]) (by omega) hz hzU

end CFSG.RankThree.PartOne
