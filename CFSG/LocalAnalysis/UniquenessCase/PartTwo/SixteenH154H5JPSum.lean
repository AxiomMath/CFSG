module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmallMod
import CFSG.Quasithin.Background.F918Z8Ex2a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

private theorem s16jp_iSup_inf_eq_bot {k : ℕ} (Z : Subgroup W) (J : Fin k → Subgroup W)
    (hJZ : ∀ i, Z ⊓ J i = ⊥)
    (hind : ∀ i, J i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), J j) ≤ Z) :
    Z ⊓ ⨆ i, J i = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨hzZ, hzJ⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨j, hj, hzprod⟩ := d321i_exists_prod_of_mem_iSup J hzJ
  have hji : ∀ i, j i = 1 := by
    intro i₀
    have hjI : j i₀ ∈ J i₀ := hj i₀
    have hprod : (∏ i ∈ Finset.univ.erase i₀, j i) ∈
        ⨆ (j' : Fin k) (_ : j' ≠ i₀), J j' := by
      exact Subgroup.prod_mem _ fun i hi =>
        Subgroup.mem_iSup_of_mem i
          (Subgroup.mem_iSup_of_mem (Finset.mem_erase.mp hi).1 (hj i))
    have hsplit : z = j i₀ * ∏ i ∈ Finset.univ.erase i₀, j i := by
      rw [hzprod, Finset.mul_prod_erase Finset.univ j (Finset.mem_univ i₀)]
    have hj_eq : j i₀ = z * (∏ i ∈ Finset.univ.erase i₀, j i)⁻¹ := by
      calc j i₀ = j i₀ * (∏ i ∈ Finset.univ.erase i₀, j i) *
              (∏ i ∈ Finset.univ.erase i₀, j i)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = z * (∏ i ∈ Finset.univ.erase i₀, j i)⁻¹ := by rw [← hsplit]
    have hmem : j i₀ ∈ Z ⊔ ⨆ (j' : Fin k) (_ : j' ≠ i₀), J j' := by
      rw [hj_eq]
      exact Subgroup.mul_mem_sup hzZ (Subgroup.inv_mem _ hprod)
    have hZ : j i₀ ∈ Z := hind i₀ (Subgroup.mem_inf.mpr ⟨hjI, hmem⟩)
    have : j i₀ ∈ Z ⊓ J i₀ := Subgroup.mem_inf.mpr ⟨hZ, hjI⟩
    rw [hJZ i₀] at this
    exact Subgroup.mem_bot.mp this
  exact Subgroup.mem_bot.mpr (hzprod.trans (Finset.prod_eq_one (fun i _ => hji i)))

theorem s16jp_sum_cover [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L)
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {k : ℕ}
    (hN : ∀ I : Subgroup W, N L I (commSub ⊤ L ⊓ fixV L) →
      ∃ D : FFModel, S16C11V1ModelCover D ∧ D.Realizes L I (commSub ⊤ L ⊓ fixV L) ∧
        commSub I L ⊔ (commSub ⊤ L ⊓ fixV L) = I)
    (h : SumOfNat N L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k) :
    commSub ⊤ L ⊓ fixV L = ⊥ := by
  obtain ⟨I, _hZI, hind, hsup, hNI⟩ := h
  choose D hD hR hcs using fun i => hN (I i) (hNI i)
  have hIinv : ∀ i, ∀ l ∈ L, ∀ x ∈ I i, l x ∈ I i :=
    fun i => s16c1614_invariant_of_realizes (hR i)
  have hIU : ∀ i, I i ≤ commSub ⊤ L := by
    intro i
    calc I i ≤ ⨆ i, I i := le_iSup _ i
      _ ≤ (commSub ⊤ L ⊓ fixV L) ⊔ ⨆ i, I i := le_sup_right
      _ = commSub ⊤ L := hsup
  have hUc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  let J : Fin k → Subgroup W := fun i => commSub (I i) L
  have hJI : ∀ i, J i ≤ I i := fun i => commSub_le_of_invariant (hIinv i)
  have hJinv : ∀ i, ∀ l ∈ L, ∀ y ∈ J i, l y ∈ J i :=
    fun i => s16jp_commSub_stable (L := L) (Y := I i) (hIinv i)
  have hJJ : ∀ i, commSub (J i) L = J i :=
    fun i => s16jp_commSub_commSub hperf (hIinv i)
  have hJZ : ∀ i, (commSub ⊤ L ⊓ fixV L) ⊓ J i = ⊥ := by
    intro i
    have hZJ' : (commSub ⊤ L ⊓ fixV L) ⊓ J i = fixV L ⊓ J i := by
      calc (commSub ⊤ L ⊓ fixV L) ⊓ J i
          = commSub ⊤ L ⊓ (fixV L ⊓ J i) := by rw [inf_assoc]
        _ = fixV L ⊓ J i := by
            rw [inf_eq_right.mpr (le_trans inf_le_right ((hJI i).trans (hIU i)))]
    have hR₀ : (D i).Realizes L (J i) ((commSub ⊤ L ⊓ fixV L) ⊓ J i) :=
      s16jp_realizes_restrict_sub (hJI i) (hJinv i) (hcs i) (hR i)
    have hR' : (D i).Realizes L (J i) (fixV L ⊓ J i) := hZJ' ▸ hR₀
    exact hZJ'.trans (s16c11_v1_cover_restrict (hD i) hW2 (hJinv i) (hJJ i) hR')
  have hindJ : ∀ i, J i ⊓ ((commSub ⊤ L ⊓ fixV L) ⊔
      ⨆ (j : Fin k) (_ : j ≠ i), J j) ≤ commSub ⊤ L ⊓ fixV L := by
    intro i
    refine le_trans (inf_le_inf (hJI i) (sup_le_sup le_rfl ?_)) (hind i)
    exact iSup_le fun j => iSup_le fun hj =>
      le_trans (hJI j) (le_iSup₂ (f := fun (j' : Fin k) (_ : j' ≠ i) => I j') j hj)
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
  have hUJ : commSub ⊤ L ≤ ⨆ i, J i := by
    rw [← hUc]
    change Subgroup.closure {c : W | ∃ x ∈ L, ∃ w ∈ commSub ⊤ L, x w * w⁻¹ = c} ≤
      ⨆ i, J i
    rw [Subgroup.closure_le]
    rintro c ⟨l, hl, x, hx, rfl⟩
    have hx' : x ∈ (commSub ⊤ L ⊓ fixV L) ⊔ ⨆ i, I i := by rw [hsup]; exact hx
    obtain ⟨z, hz, y, hy, hzy⟩ := Subgroup.mem_sup.mp hx'
    have hzL : l z = z := (mem_fixV.mp (Subgroup.mem_inf.mp hz).2) l hl
    have hxy : l x * x⁻¹ = l y * y⁻¹ := by
      rw [← hzy, map_mul, mul_inv_rev, hzL]
      rw [show (z * l y) * (y⁻¹ * z⁻¹) = (z * z⁻¹) * (l y * y⁻¹) by ac_rfl]
      rw [mul_inv_cancel, one_mul]
    rw [hxy]
    exact hgen y hy l hl
  have hJU : (⨆ i, J i) ≤ commSub ⊤ L := iSup_le fun i => (hJI i).trans (hIU i)
  have hUeq : commSub ⊤ L = ⨆ i, J i := le_antisymm hUJ hJU
  have hbot := s16jp_iSup_inf_eq_bot (commSub ⊤ L ⊓ fixV L) J hJZ hindJ
  refine eq_bot_iff.mpr fun z hz => ?_
  have hzJ : z ∈ ⨆ i, J i := by rw [← hUeq]; exact (Subgroup.mem_inf.mp hz).1
  exact Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hz, hzJ⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
