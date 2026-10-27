module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbKit
public import CFSG.Holt.H78.SectionsBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_orbit_lBar_Mbar {W : Type} [CommGroup W] [Finite W] {H K : Subgroup (MulAut W)}
    (hKH : K ≤ normalizer (H : Set (MulAut W))) (hHK : H ≤ K) (hST : OmegaSingTrans H)
    (hH : Nat.card H = 25920) {w : W} (hw : w ≠ 1) (h960 : Nat.card (ptCent H w) = 960) :
    (ptCent K w).relIndex K = 27 := by
  have hcard_conj : ∀ g : MulAut W, g ∈ normalizer (H : Set (MulAut W)) →
      Nat.card (ptCent H (g • w)) = 960 := by
    intro g hg
    have hgH : H.map (MulAut.conj g).toMonoidHom = H := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg
    have hpt : ptCent H (g • w) = (ptCent H w).map (MulAut.conj g).toMonoidHom := by
      rw [ptCent, ptCent, MulAction.stabilizer_smul_eq_stabilizer_map_conj g w,
        Subgroup.map_inf H (MulAction.stabilizer (MulAut W) w) (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective, hgH]
    rw [hpt, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, h960]
  have hsub1 : MulAction.orbit H w ⊆ MulAction.orbit K w := by
    intro x hx
    rw [MulAction.mem_orbit_iff] at hx ⊢
    obtain ⟨h, rfl⟩ := hx
    exact ⟨⟨h, hHK h.2⟩, rfl⟩
  have hsub2 : MulAction.orbit K w ⊆ MulAction.orbit H w := by
    intro x hx
    rw [MulAction.mem_orbit_iff] at hx ⊢
    obtain ⟨k, rfl⟩ := hx
    have hkne : ((k : K) : MulAut W) • w ≠ 1 := by
      intro h1
      exact hw (((k : K) : MulAut W).injective (by simpa using h1))
    obtain ⟨h, hh, hhw⟩ := hST w (((k : K) : MulAut W) • w) hw hkne h960
      (hcard_conj (k : MulAut W) (hKH k.2))
    exact ⟨⟨h, hh⟩, hhw⟩
  have horb : MulAction.orbit K w = MulAction.orbit H w :=
    Set.Subset.antisymm hsub2 hsub1
  have hstab : (ptCent K w).relIndex K = (MulAction.stabilizer (MulAut W) w).relIndex K := by
    rw [ptCent, inf_relIndex_left]
  rw [hstab, ← CFSG.Holt.H78.card_orbit_eq_relIndex w K, horb,
    CFSG.Holt.H78.card_orbit_eq_relIndex w H,
    show (MulAction.stabilizer (MulAut W) w).relIndex H = (ptCent H w).relIndex H by
      rw [ptCent, inf_relIndex_left]]
  have hptle : ptCent H w ≤ H := inf_le_left
  have hmul := Subgroup.relIndex_mul_card (ptCent H w) H
  rw [inf_eq_left.mpr hptle, h960, hH] at hmul
  exact Nat.eq_of_mul_eq_mul_right (m := 960) (by norm_num) (by rw [hmul])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
