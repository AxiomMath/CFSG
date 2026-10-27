module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.GapSingleCompModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3MinDegreeHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22U3Loss0
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.Quasithin.H13.A5M22HatRow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81 (fixV_eq_bot_of_normal)

variable {W : Type} [CommGroup W] [Finite W]

theorem false_of_isU3_two_of_rkIdx_le_three (hK : Inputs1719.K_U34InvolutionGen)
    (hW : ∀ w : W, w ^ 2 = 1) {Y N : Subgroup (MulAut W)} (hirr : IsIrrOn Y ⊤ ⊥)
    (hYN : Y ≤ normalizer (N : Set (MulAut W))) (hN : IsU3 ↥N 2) {t : MulAut W} (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (htm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3) : False := by
  have hnorm : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.mp (hYN hy) n).mp hn
  obtain ⟨hSU, -⟩ := U3Loss.isSU3_of_isU3 hN
  have hd12 : 6 * 2 ≤ dMinDeg ↥N := Inputs1719.k_SU3MinDegree_holds ↥N 2 hSU le_rfl
  have hsimple : IsSimpleGroup ↥N :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hN
  have hNbot : N ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot N).mp IsSimpleGroup.toNontrivial
  have hfixN : fixV N = ⊥ :=
    fixV_eq_bot_of_normal (fun Z hZ => hirr.2.2.2 Z hZ bot_le le_top) hnorm hNbot
  set α : MulAut ↥N := N.normalizerMonoidHom ⟨t, hYN htY⟩ with hαdef
  have hαapp : ∀ n : ↥N, ((α n : ↥N) : MulAut W) = t * n * t⁻¹ := fun n =>
    N.normalizerMonoidHom_apply_apply_coe _ n
  have hα : α ≠ 1 :=
    normalizerMonoidHom_ne_one_of_rkIdx_lt_dMinDeg hW hirr hYN hNbot htY ht2 (by omega)
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hαα : α * α = 1 := by
    refine MulEquiv.ext fun n => Subtype.ext ?_
    rw [MulAut.mul_apply, hαapp, hαapp, MulAut.one_apply]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [htinv]
    calc t * (t * (n : MulAut W) * t) * t = (t * t) * (n : MulAut W) * (t * t) := by group
      _ = n := by rw [htt, one_mul, mul_one]
  obtain ⟨x₁, x₂, hgen⟩ := hK ↥N hN α hαα hα
  have hfix : ∀ x : ↥N, ∀ w : W, t w = w → ((x : MulAut W)⁻¹ * t * x) w = w →
      ((((α x)⁻¹ * x : ↥N)) : MulAut W) w = w := by
    intro x w hw hxw
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hαapp]
    have h1 : t ((x : MulAut W) w) = (x : MulAut W) w := by
      simp only [MulAut.mul_apply] at hxw
      have h2 := congrArg (fun v => (x : MulAut W) v) hxw
      simpa only [MulAut.apply_inv_self] using h2
    have h1' : t⁻¹ ((x : MulAut W) w) = (x : MulAut W) w := by
      calc t⁻¹ ((x : MulAut W) w) = t⁻¹ (t ((x : MulAut W) w)) := by rw [h1]
        _ = (x : MulAut W) w := MulAut.inv_apply_self _ t _
    simp only [mul_inv_rev, inv_inv, MulAut.mul_apply]
    rw [h1', MulAut.inv_apply_self, hw]
  set F : Subgroup W := fixV (Subgroup.zpowers t) ⊓
    fixV (Subgroup.zpowers ((x₁ : MulAut W)⁻¹ * t * x₁)) ⊓
    fixV (Subgroup.zpowers ((x₂ : MulAut W)⁻¹ * t * x₂)) with hF
  have hNcent : N ≤ centSub F := by
    have hN' : N = (Subgroup.closure {(α x₁)⁻¹ * x₁, (α x₂)⁻¹ * x₂}).map N.subtype := by
      rw [hgen, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hN', MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩ u hu
    obtain ⟨⟨hu0, hu1⟩, hu2⟩ := hu
    rcases hy with rfl | hy
    · exact hfix x₁ u (mem_fixV_zpowers_iff_apply.mp hu0) (mem_fixV_zpowers_iff_apply.mp hu1)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hfix x₂ u (mem_fixV_zpowers_iff_apply.mp hu0) (mem_fixV_zpowers_iff_apply.mp hu2)
  have hFbot : F = ⊥ := by
    rw [eq_bot_iff, ← hfixN]
    intro w hw n hn
    exact hNcent hn w hw
  have hrk : rkIdx F ≤ 9 := by
    have h1 := CFSG.Quasithin.H13.A5.M22Hat.rkIdx_inf_le hW
      (fixV (Subgroup.zpowers t) ⊓ fixV (Subgroup.zpowers ((x₁ : MulAut W)⁻¹ * t * x₁)))
      (fixV (Subgroup.zpowers ((x₂ : MulAut W)⁻¹ * t * x₂)))
    have h2 := CFSG.Quasithin.H13.A5.M22Hat.rkIdx_inf_le hW (fixV (Subgroup.zpowers t))
      (fixV (Subgroup.zpowers ((x₁ : MulAut W)⁻¹ * t * x₁)))
    have h3 := CFSG.Quasithin.H13.A5.M22Hat.rkIdx_fixV_conj ((x₁ : MulAut W)⁻¹) t
    have h4 := CFSG.Quasithin.H13.A5.M22Hat.rkIdx_fixV_conj ((x₂ : MulAut W)⁻¹) t
    rw [inv_inv] at h3 h4
    rw [← hF] at h1
    omega
  rw [hFbot] at hrk
  have h5 := rk_add_rkIdx (⊥ : Subgroup W)
  rw [rk_bot] at h5
  have hdle : dMinDeg ↥N ≤ rk W := by
    refine Inputs1719.dMinDeg_le_rk_of_hom_ne_one (fun a b => mul_comm a b)
      (fun a => by rw [← pow_two]; exact hW a) N.subtype ?_
    intro h
    apply hNbot
    rw [eq_bot_iff]
    intro n hn
    have h6 := congrArg (fun f : ↥N →* MulAut W => f ⟨n, hn⟩) h
    exact Subgroup.mem_bot.mpr h6
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
