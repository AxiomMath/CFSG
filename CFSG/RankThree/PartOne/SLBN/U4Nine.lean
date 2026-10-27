module

public import CFSG.RankThree.PartOne.SLBN.LeviSU
public import CFSG.RankThree.PartOne.SRC.CentralizerGen
public import CFSG.RankThree.Classical.UnitaryRankWitness
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartOne.SLBN

open TauCeti CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.SRC CFSG.Assembly.LowTwoRank


theorem rankFourCover_unitaryPSU_nine {K : Type} [Field K] (h : UnitaryFieldData 3 2 K) :
    RankFourCover 3 (unitaryPSU h 4) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : CharP K 3 := h.charP
  have : Finite K := h.finite
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; norm_num)
  obtain ⟨P, hP⟩ := exists_evenFrame h h2 (n := 4) (r := 2) (by norm_num)
  have hP' : hadj h P * P = frameGram 2 (4 - 2 * 2) K := hP
  have hnm : 2 * 2 + (4 - 2 * 2) = 4 := by omega
  obtain ⟨r, hr⟩ : IsSquare (-1 : K) := by
    have := Fintype.ofFinite K
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, h.card]
    norm_num
  have hi : h.bar r = r := by
    rw [h.bar_apply]
    calc r ^ 3 ^ 2 = r * (r * r) ^ 4 := by ring
      _ = r := by rw [← hr]; norm_num
  have hF : Nat.card K = 3 ^ 4 := by rw [h.card]
  exact rankFourCover_of_cover_ker hp (by norm_num)
    (fun W _ _ ρ hρ hker => rank_four_of_cover_SL2 (e := 4) hF (by norm_num) le_rfl ρ hρ hker)
    (levProj h hP' hnm) (sq_eq_one_of_levProj_eq_one h hP' hnm)
    (orderOf_invProj h hP' hnm hi hr.symm (by omega) rfl h2) (levProj_comm h hP' hnm hi hr.symm)

theorem rankFourCover_psu_four_nine {p e : ℕ} [Fact p.Prime] (hp3 : p = 3) (he : e = 2) :
    RankFourCover p (StatedProj (StatedSU 4 (p ^ e) (GaloisField p (2 * e)))) := by
  subst hp3 he
  have h : UnitaryFieldData 3 2 (GaloisField 3 (2 * 2)) :=
    ⟨Nat.prime_three, by norm_num, GaloisField.card 3 (2 * 2) (by norm_num)⟩
  exact rankFourCover_of_mulEquiv (unitaryPSUEquiv h (by norm_num)).symm
    (rankFourCover_unitaryPSU_nine h)

theorem rankFourCover_typeTwistedA_four_nine (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 9) :
    RankFourCover 3 (ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) := by
  have hq' : q.p ^ q.exponent = 9 := by rw [← PrimePower.card_def]; exact hq
  have hp := q.prime_p
  have hdvd : q.p ∣ 3 ^ 2 := by
    have : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [hq'] at this
    exact this
  have hp3 : q.p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hdvd)
  have he2 : q.exponent = 2 := by
    rw [hp3] at hq'
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using hq')
  have hℓ : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = q.p := by
    simp [ValidLieTypeIndex.characteristic]
  have hfe : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = q.exponent := by
    simp [ValidLieTypeIndex.fieldExponent]
  have hc3 : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = 3 := by rw [hℓ]; exact hp3
  have hpr : (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩).Prime := by
    rw [hc3]; exact Nat.prime_three
  have : Fact (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩).Prime := ⟨hpr⟩
  have key := rankFourCover_of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)
    (rankFourCover_psu_four_nine (p := ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
      (e := ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩) hc3 (by rw [hfe]; exact he2))
  rwa [hc3] at key

end CFSG.RankThree.PartOne.SLBN
