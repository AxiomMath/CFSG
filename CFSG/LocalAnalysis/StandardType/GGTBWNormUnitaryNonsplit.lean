module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormPerm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggTorusWNormSC_unitary_nonsplit {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 4 ≤ d)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro he
    simp only [Prod.mk.injEq] at he
    omega
  have hZ := TableBUE.center_proj_eq_bot hK (by omega) hdq
  have hIp := InndiagSU.ggOutdiagPrime_unitary hK hn (by omega) hdq hp hpq hpd
  have hcp := StdSubRestU.ggCenterPrime_unitary hK hn (by omega) hdq hp hp2 hpd
  have hT := UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd
  exact ggTorusWNormSC_of_permEltSC hp hp2 hd hpd hZ hIp hcp hT

theorem largeEvenLabelAll_wnorm_unitary_nonsplit {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ lab.n)
    (ht : lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) (hr : 3 ≤ lab.rank)
    (hpq : p ∣ 2 ^ lab.n + 1) (hpd : ¬ p ∣ lab.rank + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hr hn hpq hpd ⊢
  rcases ht with rfl | ⟨rfl, rfl⟩
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_unitary_nonsplit (d := r + 1) (n := n)
      hK hn (by omega) hp hp2 hpq hpd
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_unitary_nonsplit (d := 4) (n := n)
      hK hn (by norm_num) hp hp2 hpq hpd

end CFSG.StandardType
