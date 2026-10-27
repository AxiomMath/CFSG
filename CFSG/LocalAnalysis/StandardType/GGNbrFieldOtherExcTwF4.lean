module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4Row
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4Fix
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4Eight

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggFieldKLevel_twF4Add
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherTwF4AddLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hS
  by_cases h3 : 3 ≤ lab.n / p
  · exact ggFieldKLevel_twF4AddLarge_of
      (fun _ _ hp hp2 hlab h => largeEvenLabelAll_rowPlainTwo_twF4Add hp hp2 hlab h)
      ggFieldFixKnown_twF4 hpc hconj hcen hinn p lab hp hp2 hlab hS h3
  · obtain ⟨hd, ht, hpq⟩ := hS
    obtain ⟨m, hm⟩ := odd_div_twF4Row hlab ht hd
    have h1 : lab.n / p = 1 := by omega
    have hp3 : p = 3 := by
      have h := (ggFermat_dvd_two_pow_add_one_iff hp hd).mp hpq
      rw [h1] at h
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using h)
    subst hp3
    have hn : lab.n = 3 := by
      have := Nat.div_mul_cancel hd
      rw [h1] at this
      omega
    exact ggFieldKLevel_twF4Eight hpc hconj hcen hinn hlab ⟨ht, hn⟩

end CFSG.StandardType

end
