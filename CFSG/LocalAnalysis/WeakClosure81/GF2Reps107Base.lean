module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
import CFSG.GroupTheory.E3Params

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}

theorem w107_rk_commSub_zpowers_le_three {t : MulAut W}
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) :
    rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3 := by
  rw [← commV_eq_commSub, ← rkIdx_fixV_zpowers, ← CFSG.GroupTheory.mQuot_top_eq_rkIdx]
  exact hm

omit [Finite W] in
theorem w107_conj_center_mem (hctx : Is135Context Y L) {t : MulAut W} (htY : t ∈ Y) {z : ↥L}
    (hz : z ∈ Subgroup.center ↥L) :
    ∃ z' ∈ Subgroup.center ↥L, (z' : MulAut W) = t * (z : MulAut W) * t⁻¹ := by
  have hLY : L ≤ Y := hctx.2.2.1
  have hconj := conj_mem_of_normal_subgroupOf hLY (w135_normal_of_ctx hctx)
  have hzL : t * (z : MulAut W) * t⁻¹ ∈ L := hconj t htY (z : MulAut W) z.2
  refine ⟨⟨t * (z : MulAut W) * t⁻¹, hzL⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hgL : t⁻¹ * (g : MulAut W) * t ∈ L := by
    have h := hconj t⁻¹ (Y.inv_mem htY) (g : MulAut W) g.2
    simpa using h
  have hcomm : (t⁻¹ * (g : MulAut W) * t) * (z : MulAut W) =
      (z : MulAut W) * (t⁻¹ * (g : MulAut W) * t) := by
    have h := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz (⟨t⁻¹ * (g : MulAut W) * t, hgL⟩ : ↥L))
    simpa using h
  apply Subtype.ext
  show (g : MulAut W) * (t * (z : MulAut W) * t⁻¹) =
      (t * (z : MulAut W) * t⁻¹) * (g : MulAut W)
  calc (g : MulAut W) * (t * (z : MulAut W) * t⁻¹)
      = t * (t⁻¹ * (g : MulAut W) * t) * (z : MulAut W) * t⁻¹ := by group
    _ = t * ((t⁻¹ * (g : MulAut W) * t) * (z : MulAut W)) * t⁻¹ := by group
    _ = t * ((z : MulAut W) * (t⁻¹ * (g : MulAut W) * t)) * t⁻¹ := by rw [hcomm]
    _ = (t * (z : MulAut W) * t⁻¹) * (g : MulAut W) := by group

omit [Finite W] in
theorem w107_fixV_center_eq_bot (hctx : Is135Context Y L) {z : ↥L}
    (hz : z ∈ Subgroup.center ↥L) (hz1 : z ≠ 1) :
    fixV (Subgroup.zpowers (z : MulAut W)) = ⊥ := by
  obtain ⟨-, -, -, -, -, hIrr⟩ := hctx
  set g : MulAut W := (z : MulAut W) with hg
  have hmem : ∀ l ∈ L, ∀ h ∈ Subgroup.zpowers g, l * h * l⁻¹ ∈ Subgroup.zpowers g := by
    intro l hl h hh
    have hcomm : l * g = g * l := by
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨l, hl⟩ : ↥L))
      simpa [hg] using h
    have hconj : l * g * l⁻¹ = g := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow, hconj]
    exact Subgroup.zpow_mem_zpowers g k
  have hstab : StableUnder L (fixV (Subgroup.zpowers g)) := stableUnder_fixV hmem
  have hgoal : fixV (Subgroup.zpowers g) = ⊥ := by
    rcases hIrr.2.2.2 (fixV (Subgroup.zpowers g)) hstab bot_le le_top with hbot | htop
    · exact hbot
    · exfalso
      have hg1 : g = 1 := by
        ext v
        have hv : v ∈ fixV (Subgroup.zpowers g) := htop ▸ Subgroup.mem_top v
        simpa using (mem_fixV.mp hv) g (Subgroup.mem_zpowers g)
      exact hz1 (Subtype.ext (by simpa [hg] using hg1))
  simpa [hg] using hgoal

theorem w107_commSub_center_eq_top (hctx : Is135Context Y L) {z : ↥L}
    (hz : z ∈ Subgroup.center ↥L) (hz1 : z ≠ 1) :
    commSub (⊤ : Subgroup W) (Subgroup.zpowers (z : MulAut W)) = ⊤ := by
  have hfix : fixV (Subgroup.zpowers (z : MulAut W)) = ⊥ :=
    w107_fixV_center_eq_bot hctx hz hz1
  have hker : (commHom (z : MulAut W)).ker = ⊥ := by rw [ker_commHom, hfix]
  have hinj : Function.Injective (commHom (z : MulAut W)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hsurj : Function.Surjective (commHom (z : MulAut W)) :=
    Finite.injective_iff_surjective.mp hinj
  rw [commSub_zpowers_eq_map (W := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)]
  exact Subgroup.map_top_of_surjective _ hsurj

end CFSG.LocalAnalysis.WeakClosure81
