module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveApply

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W]

theorem mem_conjSet_of_map_conj {Y X X' : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ Y)
    (hX' : X.map (MulAut.conj g).toMonoidHom = X') : X' ∈ conjSet X Y :=
  ⟨g, hg, hX'.symm⟩

theorem commV_sup_eq_top {Y X X' : Subgroup (MulAut W)}
    (hsum : IsDirSumOver (conjSet X Y) (fun X₁ => commV X₁))
    (htwo : ∀ X₁ ∈ conjSet X Y, X₁ = X ∨ X₁ = X') :
    commV X ⊔ commV X' = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hsum.2]
  refine iSup_le fun X₁ => ?_
  rcases htwo X₁ X₁.2 with h | h
  · rw [h]; exact le_sup_left
  · rw [h]; exact le_sup_right

theorem commV_inf_eq_bot {Y X X' : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ Y)
    (hX' : X.map (MulAut.conj g).toMonoidHom = X') (hne : X' ≠ X)
    (hsum : IsDirSumOver (conjSet X Y) (fun X₁ => commV X₁)) :
    commV X ⊓ commV X' = ⊥ := by
  let X₀ : {X₁ // X₁ ∈ conjSet X Y} := ⟨X, s15_T7_mem_conjSet_self X Y⟩
  let X₁ : {X₁ // X₁ ∈ conjSet X Y} := ⟨X', mem_conjSet_of_map_conj hg hX'⟩
  have hne' : X₁ ≠ X₀ := fun h => hne (congrArg Subtype.val h)
  have hind := (iSupIndep_def.mp hsum.1) X₀
  have hle : commV X' ≤
      ⨆ j : {X₁ // X₁ ∈ conjSet X Y}, ⨆ (_ : j ≠ X₀), commV (j : Subgroup (MulAut W)) :=
    le_iSup_of_le X₁ (le_iSup_of_le hne' le_rfl)
  exact (hind.mono_right hle).eq_bot

theorem mul_comm_of_map_conj [Finite W] {Y X X' : Subgroup (MulAut W)} {g : MulAut W}
    (hcomp : IsComponentOf X Y) (hg : g ∈ Y) (hX' : X.map (MulAut.conj g).toMonoidHom = X')
    (hne : X' ≠ X) : ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
  have hcomp' : IsComponentOf X' Y := hX' ▸ CFSG.Quasithin.B113.isComponentOf_conj hcomp hg
  exact CFSG.Quasithin.B69.components_mul_comm_of_ne (V := W) (X := Y) (L := X') (L' := X)
    hcomp' hcomp hne

theorem commV_le_fixV [Finite W] {Y X X' : Subgroup (MulAut W)} {g : MulAut W}
    (hcomp : IsComponentOf X Y) (hg : g ∈ Y) (hX' : X.map (MulAut.conj g).toMonoidHom = X')
    (hne : X' ≠ X) (hsum : IsDirSumOver (conjSet X Y) (fun X₁ => commV X₁)) :
    commV X' ≤ fixV X ∧ commV X ≤ fixV X' := by
  have hcomp' : IsComponentOf X' Y := hX' ▸ CFSG.Quasithin.B113.isComponentOf_conj hcomp hg
  have hXmem : X ∈ conjSet X Y := s15_T7_mem_conjSet_self X Y
  have hX'mem : X' ∈ conjSet X Y := mem_conjSet_of_map_conj hg hX'
  refine ⟨?_, ?_⟩
  · exact commV_le_fixV_of_isDirSumOver hsum hXmem hX'mem hne
      (le_normalizer_of_isComponentOf_ne hcomp hcomp' hne.symm)
  · exact commV_le_fixV_of_isDirSumOver hsum hX'mem hXmem hne.symm
      (le_normalizer_of_isComponentOf_ne hcomp' hcomp hne)

theorem commV_inf_fixV_eq_bot [Finite W] {Y X X' : Subgroup (MulAut W)} {g : MulAut W}
    (hcomp : IsComponentOf X Y) (hg : g ∈ Y) (hX' : X.map (MulAut.conj g).toMonoidHom = X')
    (hne : X' ≠ X) (hsum : IsDirSumOver (conjSet X Y) (fun X₁ => commV X₁))
    (hfix : fixV (X ⊔ X') = ⊥) : commV X ⊓ fixV X = ⊥ := by
  have hX'fix : commV X ≤ fixV X' := (commV_le_fixV hcomp hg hX' hne hsum).2
  rw [← le_bot_iff]
  have hle : commV X ⊓ fixV X ≤ fixV X ⊓ fixV X' :=
    le_inf inf_le_right (le_trans inf_le_left hX'fix)
  have hbot : fixV X ⊓ fixV X' = ⊥ := by rw [← fixV_sup_eq, hfix]
  rwa [hbot] at hle

theorem apply_eq_of_apply_mul_eq [Finite W] {Y X X' : Subgroup (MulAut W)} {g : MulAut W}
    (hcomp : IsComponentOf X Y) (hg : g ∈ Y) (hX' : X.map (MulAut.conj g).toMonoidHom = X')
    (hne : X' ≠ X) (hsum : IsDirSumOver (conjSet X Y) (fun X₁ => commV X₁))
    {x : MulAut W} (hx : x ∈ X) {v v' : W} (hv' : v' ∈ commV X') (hxv : x (v * v') = v * v') :
    x v = v := by
  have hfix : commV X' ≤ fixV X := (commV_le_fixV hcomp hg hX' hne hsum).1
  have hv'fix : x v' = v' := mem_fixV.mp (hfix hv') x hx
  rw [map_mul, hv'fix] at hxv
  exact mul_right_cancel hxv

theorem apply_mul_inv_eq [Finite W] {Y X X' : Subgroup (MulAut W)} {g : MulAut W}
    (hcomp : IsComponentOf X Y) (hg : g ∈ Y) (hX' : X.map (MulAut.conj g).toMonoidHom = X')
    (hne : X' ≠ X) (hsum : IsDirSumOver (conjSet X Y) (fun X₁ => commV X₁))
    {x : MulAut W} (hx : x ∈ X) (v : W) {v' : W} (hv' : v' ∈ commV X') :
    x (v * v') * (v * v')⁻¹ = x v * v⁻¹ ∧ x v * v⁻¹ ∈ commV X := by
  have hfix : commV X' ≤ fixV X := (commV_le_fixV hcomp hg hX' hne hsum).1
  have hv'fix : x v' = v' := mem_fixV.mp (hfix hv') x hx
  refine ⟨?_, Subgroup.subset_closure ⟨x, hx, v, rfl⟩⟩
  calc x (v * v') * (v * v')⁻¹
      = x v * v' * (v * v')⁻¹ := by rw [map_mul, hv'fix]
    _ = x v * v' * (v'⁻¹ * v⁻¹) := by rw [mul_inv_rev]
    _ = x v * (v' * (v'⁻¹ * v⁻¹)) := by rw [mul_assoc]
    _ = x v * ((v' * v'⁻¹) * v⁻¹) := by rw [mul_assoc]
    _ = x v * (1 * v⁻¹) := by rw [mul_inv_cancel]
    _ = x v * v⁻¹ := by rw [one_mul]

theorem exists_mul_eq_ne_one {Y X X' : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ Y)
    (hX' : X.map (MulAut.conj g).toMonoidHom = X') (hne : X' ≠ X)
    (hsum : IsDirSumOver (conjSet X Y) (fun X₁ => commV X₁))
    (htwo : ∀ X₁ ∈ conjSet X Y, X₁ = X ∨ X₁ = X') {z : W} (hz : z ≠ 1) (hgz : g z = z) :
    ∃ v ∈ commV X, ∃ v' ∈ commV X', v * v' = z ∧ v ≠ 1 := by
  have hsup : commV X ⊔ commV X' = ⊤ := commV_sup_eq_top hsum htwo
  have hzmem : z ∈ commV X ⊔ commV X' := by rw [hsup]; exact Subgroup.mem_top z
  obtain ⟨v, hv, v', hv', hmul⟩ := Subgroup.mem_sup.mp hzmem
  refine ⟨v, hv, v', hv', hmul, ?_⟩
  intro hv1
  have hv'z : v' = z := by rw [hv1, one_mul] at hmul; exact hmul
  have hzX' : z ∈ commV X' := hv'z ▸ hv'
  have hmap : commV X' = (commV X).map g.toMonoidHom := by
    rw [← hX']; exact commV_map_conj_eq X g
  have hzmap : z ∈ (commV X).map g.toMonoidHom := hmap ▸ hzX'
  obtain ⟨w, hw, hgw⟩ := Subgroup.mem_map.mp hzmap
  have hgw' : g w = z := hgw
  have hwz : w = z := EquivLike.injective g (by rw [hgw', hgz])
  have hzX : z ∈ commV X := hwz ▸ hw
  have hbot : z ∈ (⊥ : Subgroup W) := by
    rw [← commV_inf_eq_bot hg hX' hne hsum]
    exact Subgroup.mem_inf.mpr ⟨hzX, hzX'⟩
  exact hz (Subgroup.mem_bot.mp hbot)

end CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj
