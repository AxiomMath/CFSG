module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamG2
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamSyl

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Hering129C

theorem kFCensus46Three_holds :
    KFCensus46Three := by
  intro Q Lb _ _ _ c a I X f hQ hD
  obtain ⟨p, hp, hp3, hQ⟩ := hQ
  rcases hQ with hG2 | ⟨⟨e⟩⟩ | ⟨hmod1, ⟨e⟩⟩ | ⟨hmod, ⟨e⟩⟩
  ·
    obtain ⟨r, hrc, hrp, -, hG⟩ := isG2D4_of_chevalley_G2 hG2
    have hrc' : r.card = p := by rw [hrc, pow_one]
    exact census_concl_of_isG2D4 hD r 1 hG (by omega) (by omega) (fun h => absurd h (by norm_num))
  ·
    exfalso
    haveI : Finite (GaloisField p 1) := inferInstance
    obtain ⟨g, hg⟩ := (ppair_self hD).map e
    refine hg.false_of_abelian_sylow (sylow_comm_projSp_two ?_)
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
    intro h3
    rcases (Nat.dvd_prime hp.out).mp h3 with h | h <;> omega
  ·
    exfalso
    obtain ⟨g, hg⟩ := (ppair_self hD).map e
    exact hg.false_of_abelian_sylow (sylow_comm_projSU_four p hmod1)
  ·
    exfalso
    obtain ⟨g, hg⟩ := (ppair_self hD).map e
    refine hg.false_of_abelian_sylow (sylow_comm_projSL_four ?_)
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
    exact hmod

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
