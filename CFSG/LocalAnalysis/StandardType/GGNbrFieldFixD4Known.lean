module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsKnownOmegaPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggFieldFixKnown_d4A :
    GGFieldFixKnown fun p lab => GGFieldFixD4Label p lab ∧ 3 ∣ lab.n ∧ 3 ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hp2 hlab hS
  obtain ⟨⟨ht, hr, hp3, hn2, hn3⟩, hpn, hpq⟩ := hS
  subst hp3
  have h4 : 4 ≤ lab.rank := by omega
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hr hn2 hn3 hpn hpq h4 hn ⊢
  subst ht
  refine largeEvenLabelAll_omegaPlus (lab := ⟨.D, l, n⟩) rfl h4 fun K _ _ _ hK => ?_
  intro hS hna f hf hord
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum]
  simp only [h3, ↓reduceIte]
  exact FieldFixOmegaPlus.exists_fixGeom h4 hn hp hp2 hK
    ((ggDvd_two_pow_sub_one_iff hp hpn).mp hpq) hS hna hf hord

theorem ggFieldFixKnown_d4B :
    GGFieldFixKnown fun p lab => GGFieldFixD4Label p lab ∧ 3 ∣ lab.n ∧ 3 ∣ 2 ^ lab.n + 1 := by
  intro p lab hp hp2 hlab hS
  obtain ⟨⟨ht, hr, hp3, hn2, hn3⟩, hpn, -⟩ := hS
  subst hp3
  have h4 : 4 ≤ lab.rank := by omega
  have hq : 4 ≤ 2 ^ (lab.n / 3) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (lab.n / 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hr hn2 hn3 hpn h4 hq hn ⊢
  subst ht
  refine largeEvenLabelAll_omegaPlus (lab := ⟨.D, l, n⟩) rfl h4 fun K _ _ _ hK => ?_
  intro hS hna f hf hord
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum]
  simp only [h3, ↓reduceIte]
  exact FieldFixOmegaPlusNs.exists_fixGeom h4 hn hp hp2 hK hq hS hna hf hord

end CFSG.StandardType

end
