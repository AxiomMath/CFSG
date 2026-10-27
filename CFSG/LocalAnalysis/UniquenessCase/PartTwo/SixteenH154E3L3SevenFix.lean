module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Lat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmallMod
import CFSG.Quasithin.Background.F918Z8Ex2a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_mem_of_comm_mem_sum {L : Subgroup (MulAut W)} {Z : Subgroup W} {k : ℕ}
    (hZ : Z ≤ fixV L) (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ Z k)
    {x : W} (hx : ∀ l ∈ L, l x * x⁻¹ ∈ Z) : x ∈ Z := by
  obtain ⟨I, hZI, hind, hsup, hnat⟩ := hsum
  have hIinv : ∀ i, ∀ l ∈ L, ∀ w ∈ I i, l w ∈ I i :=
    fun i => s16c1614_invariant_of_binaryNaturalSL (hnat i)
  have hxZ : x ∈ Z ⊔ ⨆ i, I i := by rw [hsup]; exact Subgroup.mem_top x
  obtain ⟨z, hz, y, hy, hzy⟩ := Subgroup.mem_sup.mp hxZ
  obtain ⟨j, hj, hyprod⟩ := d321i_exists_prod_of_mem_iSup I hy
  have hx_eq : x = z * ∏ i, j i := by rw [← hzy, hyprod]
  have hjZ : ∀ i₀, j i₀ ∈ Z := by
    intro i₀
    refine s16h_e3_l3_mem_of_comm_mem (hnat i₀) (hj i₀) fun l hl => ?_
    have hyI : ∀ i, l (j i) * (j i)⁻¹ ∈ I i := fun i =>
      (I i).mul_mem (hIinv i l hl (j i) (hj i)) ((I i).inv_mem (hj i))
    have hly : l (∏ i, j i) * (∏ i, j i)⁻¹ = l x * x⁻¹ := by
      have hzL : l z = z := (mem_fixV.mp (hZ hz)) l hl
      rw [hx_eq, map_mul, mul_inv_rev, hzL]
      rw [show (z * l (∏ i, j i)) * ((∏ i, j i)⁻¹ * z⁻¹)
            = (z * z⁻¹) * (l (∏ i, j i) * (∏ i, j i)⁻¹) by ac_rfl]
      rw [mul_inv_cancel, one_mul]
    have hprodZ : ∏ i, (l (j i) * (j i)⁻¹) ∈ Z := by
      have h1 : l (∏ i, j i) * (∏ i, j i)⁻¹ = ∏ i, (l (j i) * (j i)⁻¹) := by
        rw [map_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      rw [← h1, hly]
      exact hx l hl
    have hsplit : ∏ i, (l (j i) * (j i)⁻¹)
        = (l (j i₀) * (j i₀)⁻¹) * ∏ i ∈ Finset.univ.erase i₀, (l (j i) * (j i)⁻¹) := by
      rw [Finset.mul_prod_erase Finset.univ (fun i => l (j i) * (j i)⁻¹)
        (Finset.mem_univ i₀)]
    have hyi_eq : l (j i₀) * (j i₀)⁻¹
        = (∏ i, (l (j i) * (j i)⁻¹)) *
          (∏ i ∈ Finset.univ.erase i₀, (l (j i) * (j i)⁻¹))⁻¹ := by
      rw [hsplit, mul_assoc, mul_inv_cancel, mul_one]
    have hrest : (∏ i ∈ Finset.univ.erase i₀, (l (j i) * (j i)⁻¹))
        ∈ ⨆ (j' : Fin k) (_ : j' ≠ i₀), I j' :=
      Subgroup.prod_mem _ fun i hi =>
        Subgroup.mem_iSup_of_mem i
          (Subgroup.mem_iSup_of_mem (Finset.mem_erase.mp hi).1 (hyI i))
    have hmem : l (j i₀) * (j i₀)⁻¹ ∈ Z ⊔ ⨆ (j' : Fin k) (_ : j' ≠ i₀), I j' := by
      rw [hyi_eq]
      exact Subgroup.mul_mem_sup hprodZ (Subgroup.inv_mem _ hrest)
    exact hind i₀ (Subgroup.mem_inf.mpr ⟨hyI i₀, hmem⟩)
  have hprod : ∏ i, j i ∈ Z := Subgroup.prod_mem _ fun i _ => hjZ i
  rw [hx_eq]
  exact Z.mul_mem hz hprod

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
