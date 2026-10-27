module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
import CFSG.GroupTheory.AutomorphismAction.MapEqOfMapsTo
import CFSG.Quasithin.Background.F918Z4dAux
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private def stabFixQuot (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | (∀ u ∈ U, g u = u) ∧ ∀ w : W, w⁻¹ * g w ∈ U}
  one_mem' := by
    refine ⟨fun _ _ => rfl, fun w => ?_⟩
    simp
  mul_mem' := by
    rintro g h ⟨hgU, hgQ⟩ ⟨hhU, hhQ⟩
    refine ⟨fun u hu => ?_, fun w => ?_⟩
    · rw [MulAut.mul_apply, hhU u hu, hgU u hu]
    · have he : w⁻¹ * (g * h) w = (w⁻¹ * h w) * ((h w)⁻¹ * g (h w)) := by
        rw [MulAut.mul_apply]
        group
      rw [he]
      exact U.mul_mem (hhQ w) (hgQ (h w))
  inv_mem' := by
    rintro g ⟨hgU, hgQ⟩
    refine ⟨fun u hu => ?_, fun w => ?_⟩
    · exact g.injective (by rw [MulAut.inv_apply, MulEquiv.apply_symm_apply, hgU u hu])
    · have he : w⁻¹ * g⁻¹ w = ((g⁻¹ w)⁻¹ * g (g⁻¹ w))⁻¹ := by
        rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]
        group
      rw [he]
      exact U.inv_mem (hgQ (g⁻¹ w))

private theorem mem_stabFixQuot {U : Subgroup W} {g : MulAut W} :
    g ∈ stabFixQuot U ↔ (∀ u ∈ U, g u = u) ∧ ∀ w : W, w⁻¹ * g w ∈ U := Iff.rfl

private def stabSetSubgroup (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | ∀ w : W, g w ∈ U ↔ w ∈ U}
  one_mem' := by
    intro w
    simp
  mul_mem' := by
    intro g h hg hh w
    rw [MulAut.mul_apply, hg, hh]
  inv_mem' := by
    intro g hg w
    rw [MulAut.inv_apply]
    constructor
    · intro h
      have h' : g (g.symm w) ∈ U := (hg (g.symm w)).2 h
      rwa [MulEquiv.apply_symm_apply] at h'
    · intro h
      exact (hg (g.symm w)).1 (by rwa [MulEquiv.apply_symm_apply])

private theorem mem_stabSetSubgroup {U : Subgroup W} {g : MulAut W} :
    g ∈ stabSetSubgroup U ↔ ∀ w : W, g w ∈ U ↔ w ∈ U := Iff.rfl

private theorem mul_self_eq_one_of_mem_stabFixQuot {U : Subgroup W} {g : MulAut W}
    (hW : ∀ w : W, w * w = 1) (hg : g ∈ stabFixQuot U) : g * g = 1 := by
  rw [mem_stabFixQuot] at hg
  refine MulEquiv.ext fun w => ?_
  have hfix : g (w⁻¹ * g w) = w⁻¹ * g w := hg.1 _ (hg.2 w)
  have hw : w * (w⁻¹ * g w) = g w := by group
  have key : g (g w) = w := by
    calc g (g w) = g (w * (w⁻¹ * g w)) := by rw [hw]
      _ = g w * g (w⁻¹ * g w) := map_mul g w _
      _ = g w * (w⁻¹ * g w) := by rw [hfix]
      _ = (w * (w⁻¹ * g w)) * (w⁻¹ * g w) := by rw [hw]
      _ = w * ((w⁻¹ * g w) * (w⁻¹ * g w)) := by rw [mul_assoc]
      _ = w := by rw [hW, mul_one]
  simpa [MulAut.mul_apply] using key

private theorem conj_mem_stabFixQuot {U : Subgroup W} {l g : MulAut W}
    (hU : ∀ w ∈ U, l w ∈ U) (hUi : ∀ w ∈ U, l⁻¹ w ∈ U) (hg : g ∈ stabFixQuot U) :
    l * g * l⁻¹ ∈ stabFixQuot U := by
  rw [mem_stabFixQuot] at hg ⊢
  refine ⟨fun u hu => ?_, fun w => ?_⟩
  · have hv : l⁻¹ u ∈ U := hUi u hu
    calc (l * g * l⁻¹) u = l (g (l⁻¹ u)) := by simp only [MulAut.mul_apply]
      _ = l (l⁻¹ u) := by rw [hg.1 _ hv]
      _ = u := by rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]
  · have hx : (l⁻¹ w)⁻¹ * g (l⁻¹ w) ∈ U := hg.2 _
    have he : w⁻¹ * (l * g * l⁻¹) w = l ((l⁻¹ w)⁻¹ * g (l⁻¹ w)) := by
      simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
        MulEquiv.apply_symm_apply]
    rw [he]
    exact hU _ hx

private theorem mem_stabFixQuot_zpowers (hW : ∀ w : W, w * w = 1) {d : MulAut W}
    (hd2 : d * d = 1) : d ∈ stabFixQuot (fixV (Subgroup.zpowers d)) := by
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_left (hW w)
  have hdd : ∀ w : W, d (d w) = w := by
    intro w
    have h := congrArg (fun f : MulAut W => f w) hd2
    simpa [MulAut.mul_apply] using h
  rw [mem_stabFixQuot]
  refine ⟨fun u hu => mem_fixV_zpowers_iff_apply.mp hu, fun w => ?_⟩
  rw [mem_fixV_zpowers_iff_apply]
  calc d (w⁻¹ * d w) = (d w)⁻¹ * w := by rw [map_mul, map_inv, hdd w]
    _ = w⁻¹ * d w := by rw [hinv w, hinv (d w), mul_comm]

variable [Finite W]

private theorem inv_apply_mem_of_mapsTo {U : Subgroup W} {l : MulAut W}
    (h : ∀ w ∈ U, l w ∈ U) {w : W} (hw : w ∈ U) : l⁻¹ w ∈ U := by
  have hiff := CFSG.GroupTheory.apply_mem_iff_of_mapsTo l h (l⁻¹ w)
  rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at hiff
  exact hiff.mp hw

theorem eq_one_of_stab_fixV (hW : ∀ w : W, w * w = 1) {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hO2 : O2Trivial L)
    {d : MulAut W} (hd : d ∈ Y) (hd2 : d * d = 1)
    (hstab : ∀ l ∈ L, ∀ w ∈ fixV (Subgroup.zpowers d), l w ∈ fixV (Subgroup.zpowers d)) :
    d = 1 := by
  have hfin : Finite (MulAut W) := Finite.of_injective _ DFunLike.coe_injective
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have hdC : d ∈ stabFixQuot (fixV (Subgroup.zpowers d)) := mem_stabFixQuot_zpowers hW hd2
  have hnorm : ∀ l ∈ L, ∀ g ∈ stabFixQuot (fixV (Subgroup.zpowers d)),
      l * g * l⁻¹ ∈ stabFixQuot (fixV (Subgroup.zpowers d)) :=
    fun l hl g hg =>
      conj_mem_stabFixQuot (hstab l hl) (fun w hw => inv_apply_mem_of_mapsTo (hstab l hl) hw) hg
  have hNL : ((stabFixQuot (fixV (Subgroup.zpowers d)) ⊓ L).subgroupOf L).Normal := by
    refine Subgroup.Normal.mk fun n hn l => ?_
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hnorm l l.2 n hn.1, L.mul_mem (L.mul_mem l.2 hn.2) (L.inv_mem l.2)⟩
  have hC2 : IsPGroup 2 ↥(stabFixQuot (fixV (Subgroup.zpowers d))) := by
    intro g
    refine ⟨1, ?_⟩
    have hsq : (g : MulAut W) * (g : MulAut W) = 1 := mul_self_eq_one_of_mem_stabFixQuot hW g.2
    have h2 : g ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hsq)
    simpa using h2
  have hbot : stabFixQuot (fixV (Subgroup.zpowers d)) ⊓ L = ⊥ :=
    hO2 _ inf_le_right hNL (hC2.to_le inf_le_left)
  have hcomm : ∀ l ∈ L, d * l * d⁻¹ * l⁻¹ = 1 := by
    intro l hl
    have hmem : d * l * d⁻¹ * l⁻¹ ∈ stabFixQuot (fixV (Subgroup.zpowers d)) ⊓ L := by
      refine ⟨?_, L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY hd) l).1 hl) (L.inv_mem hl)⟩
      have hconj : l * d⁻¹ * l⁻¹ ∈ stabFixQuot (fixV (Subgroup.zpowers d)) :=
        hnorm l hl d⁻¹ ((stabFixQuot _).inv_mem hdC)
      have he : d * l * d⁻¹ * l⁻¹ = d * (l * d⁻¹ * l⁻¹) := by group
      rw [he]
      exact (stabFixQuot _).mul_mem hdC hconj
    rwa [hbot, Subgroup.mem_bot] at hmem
  have hcent : d ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : d * l * d⁻¹ = l := mul_inv_eq_one.mp (hcomm l hl)
    calc l * d = (d * l * d⁻¹) * d := by rw [h1]
      _ = d * l := by group
  have hdL : d ∈ L := mem_of_mem_centralizer_of_fstar_eq hLY hF hd hcent
  by_cases hd1 : d = 1
  · exact hd1
  · exfalso
    have hzle : Subgroup.zpowers d ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
      Subgroup.zpowers_le.mpr hcent
    have hle : (Subgroup.zpowers d).subgroupOf L ≤ Subgroup.center ↥L := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (hzle (Subgroup.mem_subgroupOf.mp hx)) y y.2)
    have ho : orderOf d = 2 := orderOf_eq_prime (by rwa [pow_two]) hd1
    have hP : IsPGroup 2 ↥(Subgroup.zpowers d) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
    have hNnorm : ((Subgroup.zpowers d).subgroupOf L).Normal := Subgroup.normal_of_le_center hle
    exact hd1 (Subgroup.zpowers_eq_bot.mp
      (hO2 (Subgroup.zpowers d) (Subgroup.zpowers_le.mpr hdL) hNnorm hP))

theorem eq_one_of_le_closure_centralizer (hW : ∀ w : W, w * w = 1) {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hO2 : O2Trivial L)
    {d e : MulAut W} (hd : d ∈ Y) (hd2 : d * d = 1)
    (hde : fixV (Subgroup.zpowers d) = fixV (Subgroup.zpowers e))
    (hgen : L ≤ Subgroup.closure (((Subgroup.centralizer {d} : Subgroup (MulAut W)) :
      Set (MulAut W)) ∪ (Subgroup.centralizer {e} : Subgroup (MulAut W)))) :
    d = 1 := by
  refine eq_one_of_stab_fixV hW hLY hLn hF hO2 hd hd2 ?_
  have hL : L ≤ stabSetSubgroup (fixV (Subgroup.zpowers d)) := by
    refine le_trans hgen ((Subgroup.closure_le _).mpr ?_)
    intro g hg
    rw [Set.mem_union] at hg
    rcases hg with hg | hg
    · have hgd : Commute d g := Subgroup.mem_centralizer_iff.mp hg d (Set.mem_singleton d)
      refine fun w => ⟨fun hw => ?_, fun hw => ?_⟩
      · have h1 : g⁻¹ (g w) ∈ fixV (Subgroup.zpowers d) :=
          CFSG.Quasithin.Z4d.mem_fixV_zpowers_of_comm hgd.inv_right.eq hw
        rwa [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
      · exact CFSG.Quasithin.Z4d.mem_fixV_zpowers_of_comm hgd.eq hw
    · have hge : Commute e g := Subgroup.mem_centralizer_iff.mp hg e (Set.mem_singleton e)
      refine fun w => ⟨fun hw => ?_, fun hw => ?_⟩
      · have h1 : g⁻¹ (g w) ∈ fixV (Subgroup.zpowers e) :=
          CFSG.Quasithin.Z4d.mem_fixV_zpowers_of_comm hge.inv_right.eq (hde ▸ hw)
        rw [hde]
        rwa [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
      · have h1 : g w ∈ fixV (Subgroup.zpowers e) :=
          CFSG.Quasithin.Z4d.mem_fixV_zpowers_of_comm hge.eq (hde ▸ hw)
        rwa [← hde] at h1
  intro l hl w hw
  exact (mem_stabSetSubgroup.mp (hL hl) w).2 hw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

end
