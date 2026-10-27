module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowLiftCov
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16g_layer_top_of_O2E_eq {Y : Subgroup G} (hYE : F11.O2E Y = Y) :
    CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ := by
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) :=
    QuotientGroup.mk'_surjective _
  have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hcomap : (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    change F11.O2E Y = (⊤ : Subgroup ↥Y).map Y.subtype
    rw [hYE, hTop]
  have h := Subgroup.map_comap_eq_self_of_surjective hπ
    (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)))
  rw [hcomap, Subgroup.map_top_of_surjective _ hπ] at h
  exact h.symm

theorem s16g_exists_lift (D : Data G) (hS : S16gStd D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hset : Setting16 D V₀ V L)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L))
    (hz : Odd (Nat.card (Subgroup.center ↥(lBar V₀ V hV L)))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hmult : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)))
    (hMst : D.M ≤ stabTil V₀ V) {y : MulAut (Vtil V₀ V hV)} (hy : y ∈ lBar V₀ V hV L)
    (hyp : orderOf y = p) :
    ∃ m : ↥D.M, orderOf m = p ∧ barHom V₀ V hV hMst m = y := by
  obtain ⟨Y, hYM, hperf, hlay, hsolv, hYbar⟩ := s16g_exists_cover D hS (hV := hV) hset hq
  have hYs : Y ≤ stabTil V₀ V := hYM.trans hMst
  let φ : ↥Y →* ↥(barSub V₀ V hV Y) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hYs)) (barSub V₀ V hV Y)
      (fun g => actTil_mem_barSub V₀ V hV g.2 (hYs g.2))
  have hφ : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV Y ψ).1 hψ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  let N : Subgroup ↥Y := φ.ker
  have hNker : N = (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y := by
    ext g
    have hMn : D.M ≤ normalizer (V : Set G) := hMst.trans (stabTil_le_normalizer V₀ V)
    rw [show N = φ.ker from rfl, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_cTilde_iff hV hMn]
    have hgY : (g : G) ∈ Y := g.2
    constructor
    · intro h1
      exact ⟨hgY, hYM hgY, hYs hgY, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1
  haveI : N.Normal := MonoidHom.normal_ker φ
  have hNsolv : Group.IsSolvable ↥N := by
    rw [hNker]
    have hle : (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y ≤ CFSG.solvableRadical ↥Y := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hsolv (Subgroup.mem_subgroupOf.mp hx)
      have hzx' : z = x := Subtype.ext hzx
      exact hzx' ▸ hz
    haveI := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := ↥Y)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hperf' : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hlayer : CFSG.Open.rankThreeLayer (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) = ⊤ :=
    s16g_layer_top_of_O2E_eq hlay
  let e : ↥Y ⧸ N ≃* ↥(lBar V₀ V hV L) :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans (MulEquiv.subgroupCongr hYbar)
  obtain ⟨y', hy'o, hy'e⟩ :=
    s16g_lift_order_p (Y := ↥Y) hperf' hlayer N hNsolv e hq hz hp hp2 hmult
      (x := ⟨y, hy⟩) (by rw [Subgroup.orderOf_mk]; exact hyp)
  let m : ↥D.M := ⟨(y' : G), hYM y'.2⟩
  refine ⟨m, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe m, show (m : G) = (y' : G) from rfl, Subgroup.orderOf_coe, hy'o]
  · have hval : ((e (QuotientGroup.mk y') : ↥(lBar V₀ V hV L)) :
        MulAut (Vtil V₀ V hV)) = (φ y' : MulAut (Vtil V₀ V hV)) := by
      have h1 : ((QuotientGroup.quotientKerEquivOfSurjective φ hφ)
          (QuotientGroup.mk y') : ↥(barSub V₀ V hV Y)) = φ y' := rfl
      simpa [e] using congrArg Subtype.val h1
    have h1 : (φ y' : MulAut (Vtil V₀ V hV)) = y := by
      have h2 := congrArg Subtype.val hy'e
      rw [hval] at h2
      simpa using h2
    rw [show barHom V₀ V hV hMst m = (φ y' : MulAut (Vtil V₀ V hV)) from rfl, h1]

theorem s16g_false_of_fix_lBar (D : Data G) (hS : S16gStd D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hset : Setting16 D V₀ V L)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L))
    (hz : Odd (Nat.card (Subgroup.center ↥(lBar V₀ V hV L)))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpσ : p ∈ D.sig)
    (hmult : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)))
    (hker : p ∣ Nat.card (F11.CTilde D.M V₀ V))
    (hfix : ∀ x : Vtil V₀ V hV, x ≠ 1 → ∃ y ∈ lBar V₀ V hV L, orderOf y = p ∧ y x = x) :
    False := by
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  refine s16g_false_of_fix_ker D hS (hV := hV) hset hp hpσ hker hMst ?_
  intro x hx1
  obtain ⟨y, hy, hyo, hyx⟩ := hfix x hx1
  obtain ⟨m, hmo, hmy⟩ := s16g_exists_lift D hS hset hq hz hp hp2 hmult hMst hy hyo
  refine ⟨m, hmo, ?_, ?_⟩
  · rw [hmy]
    intro h
    rw [h, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  · rw [hmy]
    exact hyx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
