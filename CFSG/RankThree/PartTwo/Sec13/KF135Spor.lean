module

public import CFSG.RankThree.PartTwo.Sec13.KF135Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

open CFSG.RankThree.PartTwo.Sec13.F135Last CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporFactors sporOrder)

theorem sporadics42_cube : ∀ s ∈ sporadics42, ∀ y ∈ sporFactors s, 7 ≤ y.1 → 3 ≤ y.2 →
    (s = .He ∧ y.1 = 7) ∨ (s = .ONan ∧ y.1 = 7) ∨ (s = .J4 ∧ y.1 = 11) := by
  decide

theorem kF135At_fam6
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hord : ∀ s : TauCeti.SporadicName,
      Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s) = sporOrder s)
    (hout : ∀ (s : TauCeti.SporadicName) {p : ℕ}, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)) :
    KF135At Fam6 := by
  intro S _ _ p P x u V hF h
  obtain ⟨s, hs, ⟨f⟩⟩ := hF
  have hp7 := h.seven_le
  have houtS : ¬ p ∣ Nat.card (Outer S) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv]
    exact hout s h.prime (by omega)
  have hcube := h.cube_dvd_card_of_not_dvd_outer houtS
  obtain ⟨b⟩ := hbr s
  have hcard : Nat.card S = sporOrder s :=
    (Nat.card_congr (f.trans b.symm).toEquiv).trans (hord s)
  rw [hcard] at hcube
  obtain ⟨y, hy, hpy, hy3⟩ :=
    CFSG.ComponentClassification.GSThmB.QPUSpor.exists_of_prime_pow_dvd_prod h.prime
      (by norm_num) (CFSG.ComponentClassification.GSThmB.QPUSpor.sporFactors_prime s)
      (CFSG.ComponentClassification.GSThmB.QPUSpor.sporFactors_nodup s) hcube
  rcases sporadics42_cube s hs y hy (hpy ▸ hp7) hy3 with ⟨rfl, h7⟩ | ⟨rfl, h7⟩ | ⟨rfl, h11⟩
  · exact Or.inl ⟨hpy.trans h7, Or.inl ⟨f.trans b.symm⟩⟩
  · exact Or.inl ⟨hpy.trans h7, Or.inr ⟨f.trans b.symm⟩⟩
  · exact Or.inr ⟨hpy.trans h11, ⟨f.trans b.symm⟩⟩

end CFSG.RankThree.PartTwo.Sec13.KF135Proof
