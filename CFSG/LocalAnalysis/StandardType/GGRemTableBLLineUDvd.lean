module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGUnitDvdLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLCover
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcFlatDefs
public import CFSG.LocalAnalysis.StandardType.GGYardstoneLegacyImports

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.LineU

theorem largeEvenLabelAll_unitDvd_line (hU : UnitaryUniversalCover)
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGUnitDvdLabelNo63 p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, hl, hpn, hpd⟩, hno⟩ := h
  dsimp only at ht hl hpn hpd hno
  subst ht
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  have hlift : GGTorusLift p (ggUnitaryTorusRank p (l + 1))
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) :=
    ggTorusLift_unitary hK hn (by omega) hdq hp hpn
  have hline : GGNoInvariantLineSCr p (ggUnitaryTorusRank p (l + 1))
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (l + 1)) K (2 ^ n))) := by
    have h63' : ¬ (l + 1 = 6 ∧ p = 3) := fun ⟨h6, h3⟩ => hno ⟨by omega, h3⟩
    have hd5 : 5 ≤ l + 1 := by
      by_contra hlt
      have hl3 : l = 3 := by omega
      subst hl3
      have h4 : p ∣ 2 ^ 2 := by simpa using hpd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
    exact noInvariantLineSCr_unitary hU hK hn hd5 hp hpn hpd h63'
  exact ⟨K, i1, i2, hK, ⟨hQ', ggUnitaryTorusRank p (l + 1), hlift, hline⟩⟩

theorem ggLNoInvariantLineInputOn_unitDvd (hU : UnitaryUniversalCover) :
    GGLNoInvariantLineInputOn GGUnitDvdLabelNo63 :=
  ggLNoInvariantLineInputOn_of_labelsSCr fun _ _ hp hlab h =>
    largeEvenLabelAll_unitDvd_line hU hp hlab h

theorem ggLNoInvariantLineInputOn_remainder_of_unitDvd
    (hU : GGLNoInvariantLineInputOn GGUnitDvdLabelNo63)
    (h63 : GGLNoInvariantLineInputOn GGUnitDvd63Label)
    (hN : GGLNoInvariantLineInputOn fun p lab =>
      Yardstones.M3f9567aba59d.GGRemainderTableBLResLine p lab ∧ ¬ GGUnitDvdLabel p lab) :
    GGLNoInvariantLineInputOn Yardstones.M3f9567aba59d.GGRemainderTableBLResLine := by
  refine CorFourTwoVacMore.lNoInvariantLineInputOn_mono (fun p lab h => ?_) (hN.or (hU.or h63))
  by_cases hc : GGUnitDvdLabel p lab
  · by_cases h6 : lab.rank = 5 ∧ p = 3
    · exact Or.inr (Or.inr ⟨hc, h6⟩)
    · exact Or.inr (Or.inl ⟨hc, h6⟩)
  · exact Or.inl ⟨h, hc⟩

end CFSG.StandardType

end
