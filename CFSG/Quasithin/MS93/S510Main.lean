module

public import CFSG.Quasithin.MS93.S510XZ
public import CFSG.Quasithin.MS93.S510Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5B

theorem s510_of (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55) (h56 : S56)
    (h59 : S59) (hnxz : S510NXZ) : S510 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc hαβ
  by_cases hXU : Xq M = Uq M T L ⊔ Zq M L
  swap
  · exact hnxz G M T L h hmin hb k F _ _ a hd hXU α' hc hαβ
  by_contra hno
  push Not at hno
  have hcc : S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) ≠
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ∨
        ¬ S510.LineCase h (2 ^ k) a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l, hl⟩ := (S510.exists_case56_iff h (2 ^ k) a _).2 hcon
    exact hno l hl
  obtain ⟨s, hsα, hch⟩ := S510.exists_isChain h32 hX2 h52 h54 h55 h56 h59 h hmin hb hd hc
    (critDist (puAmalgam h.le) + 3)
  have hdd := hch.dist_eq
  have hb2 : 2 ≤ critDist (puAmalgam h.le) := two_le_critDist _ h.hyp20 h.critDist_pos
  have htop : ∀ i ≤ critDist (puAmalgam h.le),
      geo _ s α' (2 * (critDist (puAmalgam h.le) + 3) + i) =
        geo _ (baseA (puAmalgam h.le)) α' i := by
    intro i hi
    have h1 := hch.geo_eq (i := 2 * (critDist (puAmalgam h.le) + 3))
      (j := critDist (puAmalgam h.le) + 2 * (critDist (puAmalgam h.le) + 3)) (m := i)
      (by omega) le_rfl (by omega)
    rw [hsα, ← hdd, geo_dist] at h1
    exact h1.symm
  have hN : S5.jOff h.le L (2 ^ k)
        (geo _ s α' (2 * (critDist (puAmalgam h.le) + 3) + 2))
        (geo _ s α' (2 * (critDist (puAmalgam h.le) + 3) + 1)) ≠
      S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * (critDist (puAmalgam h.le) + 3)))
        (geo _ s α' (2 * (critDist (puAmalgam h.le) + 3) + 1)) ∨
        ¬ S510.LineCase h (2 ^ k) a := by
    rw [htop 2 (by omega), htop 1 (by omega), hsα, hαβ]
    exact hcc
  exact hch.false_of_xz h32 hX2 h54 h59 hmin hd hb (by omega) (hch.case_prop hN) hXU

end S5B

end CFSG.Quasithin.MS93
