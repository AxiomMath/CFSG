module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmallMod
import CFSG.Quasithin.Background.F918Z8Ex2a
import CFSG.Quasithin.Vol2.Ch3B513NC1Lin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

theorem s16fh_sum_cover [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) {U Z : Subgroup W} (hUinv : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    (hUc : commSub U L = U) (hZ : Z ≤ fixV L)
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {k c : ℕ}
    (hN : ∀ I : Subgroup W, N L I Z →
      ∃ D : FFModel, S16BoundCover D c ∧ D.Realizes L I Z ∧ commSub I L ⊔ Z = I)
    (h : SumOfNat N L U Z k) : Nat.card ↥Z ≤ 2 ^ (c * k) := by
  obtain ⟨I, _hZI, hind, hsup, hNI⟩ := h
  choose D hD hR hcs using fun i => hN (I i) (hNI i)
  have hIinv : ∀ i, ∀ l ∈ L, ∀ x ∈ I i, l x ∈ I i :=
    fun i => s16c1614_invariant_of_realizes (hR i)
  have hIU : ∀ i, I i ≤ U := by
    intro i
    calc I i ≤ ⨆ i, I i := le_iSup _ i
      _ ≤ Z ⊔ ⨆ i, I i := le_sup_right
      _ = U := hsup
  have hZU : Z ≤ U := by rw [← hsup]; exact le_sup_left
  let J : Fin k → Subgroup W := fun i => commSub (I i) L
  have hJI : ∀ i, J i ≤ I i := fun i => commSub_le_of_invariant (hIinv i)
  have hJinv : ∀ i, ∀ l ∈ L, ∀ y ∈ J i, l y ∈ J i :=
    fun i => s16jp_commSub_stable (L := L) (Y := I i) (hIinv i)
  have hJJ : ∀ i, commSub (J i) L = J i :=
    fun i => s16jp_commSub_commSub hperf (hIinv i)
  have hJZ : ∀ i, Nat.card ↥(Z ⊓ J i) ≤ 2 ^ c := by
    intro i
    have hZJ : Z ⊓ J i ≤ fixV L := inf_le_left.trans hZ
    have hR₀ : (D i).Realizes L (J i) (Z ⊓ J i) :=
      s16jp_realizes_restrict_sub (hJI i) (hJinv i) (hcs i) (hR i)
    exact s16fh_cover_restrict (hD i) hW2 (hJinv i) (hJJ i) hZJ hR₀
  have hgen : ∀ y ∈ ⨆ i, I i, ∀ l ∈ L, l y * y⁻¹ ∈ ⨆ i, J i := by
    intro y hy
    refine Subgroup.iSup_induction (fun i => I i) hy
      (C := fun z => ∀ l ∈ L, l z * z⁻¹ ∈ ⨆ i, J i) ?_ ?_ ?_
    · intro i y hy l hl
      exact le_iSup (fun i => J i) i (Subgroup.subset_closure ⟨l, hl, y, hy, rfl⟩)
    · intro l hl
      simpa only [map_one, inv_one, one_mul] using Subgroup.one_mem (⨆ i, J i)
    · intro a b ha hb l hl
      rw [map_mul, mul_inv_rev]
      rw [show (l a * l b) * (b⁻¹ * a⁻¹) = (l a * a⁻¹) * (l b * b⁻¹) by ac_rfl]
      exact mul_mem (ha l hl) (hb l hl)
  have hUJ : U ≤ ⨆ i, J i := by
    rw [← hUc]
    change Subgroup.closure {c : W | ∃ x ∈ L, ∃ w ∈ U, x w * w⁻¹ = c} ≤ ⨆ i, J i
    rw [Subgroup.closure_le]
    rintro c ⟨l, hl, x, hx, rfl⟩
    have hx' : x ∈ Z ⊔ ⨆ i, I i := by rw [hsup]; exact hx
    obtain ⟨z, hz, y, hy, hzy⟩ := Subgroup.mem_sup.mp hx'
    have hzL : l z = z := (mem_fixV.mp (hZ hz)) l hl
    have hxy : l x * x⁻¹ = l y * y⁻¹ := by
      rw [← hzy, map_mul, mul_inv_rev, hzL]
      rw [show (z * l y) * (y⁻¹ * z⁻¹) = (z * z⁻¹) * (l y * y⁻¹) by ac_rfl]
      rw [mul_inv_cancel, one_mul]
    rw [hxy]
    exact hgen y hy l hl
  have hJU : (⨆ i, J i) ≤ U := iSup_le fun i => (hJI i).trans (hIU i)
  have hUeq : U = ⨆ i, J i := le_antisymm hUJ hJU
  have hZsup : Z ≤ ⨆ i, Z ⊓ J i := by
    intro z hzZ
    have hzJ : z ∈ ⨆ i, J i := hUeq ▸ (hZU hzZ)
    obtain ⟨j, hj, hzprod⟩ := d321i_exists_prod_of_mem_iSup J hzJ
    have hjiI : ∀ i, j i ∈ I i := fun i => hJI i (hj i)
    have hjiZ : ∀ i, j i ∈ Z ⊓ J i := by
      intro i₀
      have hprod : (∏ i ∈ Finset.univ.erase i₀, j i) ∈
          ⨆ (j' : Fin k) (_ : j' ≠ i₀), I j' :=
        Subgroup.prod_mem _ fun i hi =>
          Subgroup.mem_iSup_of_mem i
            (Subgroup.mem_iSup_of_mem (Finset.mem_erase.mp hi).1 (hjiI i))
      have hsplit : z = j i₀ * ∏ i ∈ Finset.univ.erase i₀, j i := by
        rw [hzprod, Finset.mul_prod_erase Finset.univ j (Finset.mem_univ i₀)]
      have hj_eq : j i₀ = z * (∏ i ∈ Finset.univ.erase i₀, j i)⁻¹ := by
        calc j i₀ = j i₀ * (∏ i ∈ Finset.univ.erase i₀, j i) *
                (∏ i ∈ Finset.univ.erase i₀, j i)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel, mul_one]
          _ = z * (∏ i ∈ Finset.univ.erase i₀, j i)⁻¹ := by rw [← hsplit]
      have hmem : j i₀ ∈ Z ⊔ ⨆ (j' : Fin k) (_ : j' ≠ i₀), I j' := by
        rw [hj_eq]
        exact Subgroup.mul_mem_sup hzZ (Subgroup.inv_mem _ hprod)
      exact Subgroup.mem_inf.mpr
        ⟨hind i₀ (Subgroup.mem_inf.mpr ⟨hjiI i₀, hmem⟩), hj i₀⟩
    rw [hzprod]
    exact Subgroup.prod_mem _ fun i _ => Subgroup.mem_iSup_of_mem i (hjiZ i)
  have hcard1 : Nat.card ↥Z ≤ Nat.card ↥(⨆ i, Z ⊓ J i) := Subgroup.card_le_of_le hZsup
  have hcard2 : Nat.card ↥(⨆ i, Z ⊓ J i) ≤ ∏ i : Fin k, Nat.card ↥(Z ⊓ J i) :=
    B513N.card_iSup_le_prod k (fun i => Z ⊓ J i)
  have hcard3 : ∏ i : Fin k, Nat.card ↥(Z ⊓ J i) ≤ ∏ i : Fin k, 2 ^ c :=
    Finset.prod_le_prod fun i _ => hJZ i
  calc Nat.card ↥Z ≤ Nat.card ↥(⨆ i, Z ⊓ J i) := hcard1
    _ ≤ ∏ i : Fin k, Nat.card ↥(Z ⊓ J i) := hcard2
    _ ≤ ∏ i : Fin k, 2 ^ c := hcard3
    _ = (2 ^ c) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = 2 ^ (c * k) := (Nat.pow_mul 2 c k).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
