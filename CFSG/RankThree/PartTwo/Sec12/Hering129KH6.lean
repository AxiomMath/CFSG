module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KH5
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH2b
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH3b
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH4b

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open Matrix (ProjGenLinGroup)


theorem gap129HessL3_of_pgl (hPGL : KF_L3_PGL) (hDeg : Gap129HessL3Deg) : Gap129HessL3 := by
  intro P _ _ Yh Bh xh bh ch hD hex
  obtain ⟨p, e, hp, hiso⟩ := hex
  haveI := hD.normal
  obtain ⟨p, e, hp, he, hiso⟩ : ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
      Sec4.IsoLThreePi ↥Yh p e := by
    by_cases he : 1 ≤ e
    · exact ⟨p, e, hp, he, hiso⟩
    · obtain rfl : e = 0 := by omega
      by_cases h3 : p % 3 = 1
      · exact ⟨p, 1, hp, le_rfl, Hering129KH2b.isoLThreePi_zero hiso h3⟩
      · exfalso
        rcases hiso with ⟨-, hf⟩ | ⟨h2, -⟩
        · exact hDeg P Yh Bh xh bh ch hD p h3 hf
        · simp at h2
  obtain ⟨π, K, _, hK, hq, ⟨e'⟩⟩ := Hering129KH2.hess_model hD he hiso
  have hact := Hering129KH3.hess_actions hD hK hq e'
  obtain ⟨y, hy⟩ := hact bh (Subgroup.mem_sup_right (by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers bh))))
  obtain ⟨hyZ, hy3, hm1, hm3, hcomm, Xm, hXL, hXC, hXp, hXs, hmX⟩ :=
    Hering129KH3b.hess_to_pgl hD hK hq e' hy
  obtain ⟨F, hF⟩ := hPGL π p e K hK hq y hy.1 hyZ hy3 _
    (e' ⟨ch, hD.cY⟩).2 hm1 hm3 hcomm Xm hXL hXC hXp hXs hmX
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    Hering129KH4.liftSub_props hD hK hq e' hact hy hF
  exact ⟨Hering129KH4.liftSub e' F, h1, h2, h3, h4, h5, h6, h7, h8,
    Hering129KH4b.liftSub_trans hD hK hq e' hact hy hF,
    Hering129KH5.nonempty_autIn_liftSub hD hK hq e' hact hy hF⟩

end CFSG.RankThree.PartTwo.Sec12
