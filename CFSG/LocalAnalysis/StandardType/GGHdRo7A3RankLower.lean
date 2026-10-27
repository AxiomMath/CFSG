module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SideDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem a3_rankLower_holds :
    A3RankLowerLeaf := by
  intro G _ _ p B X z m hp3 hm9 h3m hBmax hzp hz1 hXz hperf hlabel
  obtain ⟨lab, -, hHas, htag, hlabn, hlabrank⟩ := hlabel
  have hp : p.Prime := hp3.symm ▸ Nat.prime_three
  have hHas' : LargeEvenRecipeUnitary m (2 ^ 1)
      (fun R' _ _ _ => Nonempty (↥X ⧸ Subgroup.center ↥X ≃* R')) := by
    simpa only [GGHasLabel, LargeEvenRawDatum, htag, hlabn, hlabrank] using hHas
  obtain ⟨F, hFfield, hFfin, hFcard, hQ⟩ := hHas'
  obtain ⟨θ⟩ := hQ
  have hpq : p ∣ 2 ^ 1 + 1 := by
    rw [hp3]
    norm_num
  have hdq : (m, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h1 := (Prod.ext_iff.mp h).1
    omega
  have hlift := ggTorusLift_unitary (K := F) (n := 1) (d := m) hFcard
    (by norm_num) (by omega) hdq hp hpq
  have hrank : ggUnitaryTorusRank p m = m - 3 := by
    rw [ggUnitaryTorusRank, hp3, ite_eq_left h3m]
  have hTLR : m - 2 ≤ LargeEvenTwoLocalRank p G := by
    have h := succ_le_twoLocalRank_of_torusLift (G := G) (p := p) (x := z) (L := X) hp
      hXz hzp hz1 hperf θ hlift
    rw [hrank] at h
    omega
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := by
    unfold LargeEvenIsBmax at hBmax
    exact hBmax.2.1
  calc p ^ (m - 2) ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hTLR
    _ = Nat.card B := hBcard.symm

end CFSG.StandardType.HdRo7A3
