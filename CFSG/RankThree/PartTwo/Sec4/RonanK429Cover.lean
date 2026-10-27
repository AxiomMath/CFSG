module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverFix
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverPSL
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverPSU
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverRank
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverCenter

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts


theorem k429CoverL3 : K429CoverL3 := by
  intro L _ _ hLq hZ3 n hn hS α hα3 hfield K hKfix hKq hKsn hKZ
  by_contra hZ
  haveI : Group.IsPerfect L := hLq.1
  have hZodd : Odd (Nat.card (Subgroup.center L)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZ3
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨hZcard, π, p, f, F, _, hK, hq, f₀, hf, ρ, hρ, g, hg, e, hform⟩ :
      Nat.card (Subgroup.center L) = 3 ∧ CoverNormalForm L α := by
    rcases hfield with ⟨F, _, _, e', hk⟩ | ⟨p, f, F, _, h, hq2, e', hk⟩
    · exact coverNormalForm_of_psl hZodd hZ hα3 e' hk
    · obtain rfl := eq_two_of_isoLThreePi_of_unitaryPSU hn hS h e'
      exact coverNormalForm_of_psu hZodd hZ hα3 h hq2 e' hk
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  have hKeq : K = autFix α :=
    autFix_eq_of_frobPow hK hq hf hφ hφ3 (eq_or_eq_sq_of_pow hφ hρ) hg e hα3 hform hKfix hKq
      hKsn
  have hZK : Subgroup.center L ≤ K := hKeq ▸ center_le_autFix_of_card_three hZcard hα3
  apply hZ
  rw [eq_bot_iff]
  intro z hz
  rw [← hKZ]
  exact ⟨hZK hz, hz⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK429
