module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB1AAAAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResAlg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResSum

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_L3_three_seven_fixed_mem_Z {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (g : MulAut ↥(commSub ⊤ L))
    (hgc : g ∈ Subgroup.centralizer
      (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))))
    (hg7 : g ^ 7 = 1)
    (hgZ : ∀ z : ↥(commSub ⊤ L), (z : W) ∈ commSub ⊤ L ⊓ fixV L → g z = z)
    (hn : ¬ ∀ u : ↥(commSub ⊤ L), g u * u⁻¹ ∈ fixV (autSub L (commSub ⊤ L))) :
    ∀ u : ↥(commSub ⊤ L), g u = u → (u : W) ∈ commSub ⊤ L ⊓ fixV L := by
  have hrow : s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) :=
    ⟨3, le_rfl, h.1, h.2⟩
  obtain ⟨helem, -, -, hquasi, hsl3, hcomm, -⟩ := s16h_L3_res_algebra hc h.1
  obtain ⟨k, hk, hsum⟩ := s16h_L3_res_sum hrow
  have hLstab : L ≤ stabSub (commSub ⊤ L) :=
    s16h_le_stabSub_of_stable fun x hx u hu =>
      commSub_top_stable151b
        (fun y hy => L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) u hu
  have hZeq : (fixV (autSub L (commSub ⊤ L))).map (commSub ⊤ L).subtype =
      commSub ⊤ L ⊓ fixV L := map_subtype_fixV_autSub hLstab
  have hgZ' : ∀ z : ↥(commSub ⊤ L), z ∈ fixV (autSub L (commSub ⊤ L)) → g z = z := by
    intro z hz
    refine hgZ z ?_
    have hmem : (z : W) ∈ (fixV (autSub L (commSub ⊤ L))).map (commSub ⊤ L).subtype :=
      Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    rwa [hZeq] at hmem
  have hfix := s16h_L3_sum_three_seven_fixed_mem_fixV
    (U := ↥(commSub ⊤ L)) (L := autSub L (commSub ⊤ L))
    helem hquasi hsl3 hcomm ⟨k, hk, hsum⟩ hgc hg7 hgZ' hn
  intro u hu
  have hu' : u ∈ fixV (autSub L (commSub ⊤ L)) := hfix u hu
  have hmem : (u : W) ∈ (fixV (autSub L (commSub ⊤ L))).map (commSub ⊤ L).subtype :=
    Subgroup.mem_map.mpr ⟨u, hu', rfl⟩
  rwa [hZeq] at hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
