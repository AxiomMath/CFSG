module

import CFSG.Fischer.Classification.Recognition.SymOBasic
import CFSG.Quasithin.Background.Asc81cPfTen8
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1

open CFSG.Quasithin

variable {W : Type} [CommGroup W] {K : Subgroup (MulAut W)} {Z : Subgroup W}

theorem le_stabSub_of_stableUnder (hZK : StableUnder K Z) : K ≤ stabSub Z := by
  intro x hx u
  constructor
  · intro hxu
    have hx' : x⁻¹ ∈ K := K.inv_mem hx
    simpa using hZK x⁻¹ hx' (x u) hxu
  · intro hu
    exact hZK x hx u hu

@[expose] def toAutQuot (hZK : StableUnder K Z) : ↥K →* ↥(autQuot K Z) :=
  ((quotHom Z).comp (Subgroup.inclusion (le_stabSub_of_stableUnder hZK))).codRestrict
    (autQuot K Z) fun x => Subgroup.mem_map.mpr ⟨Subgroup.inclusion _ x, x.2, rfl⟩

theorem toAutQuot_apply_mk (hZK : StableUnder K Z) (x : ↥K) (w : W) :
    ((toAutQuot hZK x : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w) =
      QuotientGroup.mk ((x : MulAut W) w) :=
  rfl

theorem toAutQuot_surjective (hZK : StableUnder K Z) : Function.Surjective (toAutQuot hZK) := by
  intro y
  have hy : (y : MulAut (W ⧸ Z)) ∈ (K.subgroupOf (stabSub Z)).map (quotHom Z) := y.2
  rw [Subgroup.mem_map] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨(x : MulAut W), hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

theorem mul_self_eq_one_of_mem_ker_toAutQuot (hW : ∀ w : W, w ^ 2 = 1) (hZK : StableUnder K Z)
    (hZ : Z ≤ fixV K) {x : ↥K} (hx : x ∈ (toAutQuot hZK).ker) : x * x = 1 := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  have hxq : quotHom Z (Subgroup.inclusion (le_stabSub_of_stableUnder hZK) x) = 1 :=
    congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
  have hmem : (x : MulAut W) w * w⁻¹ ∈ Z := by
    have h1 := congrArg (fun f : MulAut (W ⧸ Z) => f (QuotientGroup.mk w)) hxq
    simp only [MulAut.one_apply, quotHom_mk] at h1
    exact (mk_eq_mk_iff ((x : MulAut W) w) w).mp h1
  have hfixZ : ∀ z ∈ Z, (x : MulAut W) z = z := fun z hz =>
    (mem_fixV.mp (hZ hz)) (x : MulAut W) x.2
  calc ((x * x : ↥K) : MulAut W) w = (x : MulAut W) ((x : MulAut W) w) := rfl
    _ = (x : MulAut W) (((x : MulAut W) w * w⁻¹) * w) := by
        rw [show ((x : MulAut W) w * w⁻¹) * w = (x : MulAut W) w by group]
    _ = (x : MulAut W) ((x : MulAut W) w * w⁻¹) * (x : MulAut W) w := by rw [map_mul]
    _ = ((x : MulAut W) w * w⁻¹) * (x : MulAut W) w := by rw [hfixZ _ hmem]
    _ = w := by
      rw [show ((x : MulAut W) w * w⁻¹) * (x : MulAut W) w =
        ((x : MulAut W) w * (x : MulAut W) w) * w⁻¹ by ac_rfl]
      rw [show (x : MulAut W) w * (x : MulAut W) w = 1 by
        simpa [pow_two] using hW ((x : MulAut W) w), one_mul,
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hW w)]

theorem ker_toAutQuot_le_center (hW : ∀ w : W, w ^ 2 = 1) (hZK : StableUnder K Z)
    (hZ : Z ≤ fixV K) (hq : CFSG.Open.IsQuasisimple ↥K) :
    (toAutQuot hZK).ker ≤ Subgroup.center ↥K := by
  have hker_sq : ∀ a ∈ (toAutQuot hZK).ker, a * a = 1 :=
    fun a ha => mul_self_eq_one_of_mem_ker_toAutQuot hW hZK hZ ha
  have hker_comm : ∀ a ∈ (toAutQuot hZK).ker, ∀ b ∈ (toAutQuot hZK).ker, a * b = b * a := by
    intro a ha b hb
    have ha2 := hker_sq a ha
    have hb2 := hker_sq b hb
    have hab2 := hker_sq (a * b) ((toAutQuot hZK).ker.mul_mem ha hb)
    have h1 : a * b = (a * b)⁻¹ := mul_eq_one_iff_eq_inv.mp hab2
    rw [h1, mul_inv_rev, (mul_eq_one_iff_inv_eq.mp hb2), (mul_eq_one_iff_inv_eq.mp ha2)]
  exact CFSG.Fischer.Classification.Recognition.SymO.le_center_of_normal hq
    (toAutQuot hZK).normal_ker hker_comm

theorem fixV_zpowers_eq (hZK : StableUnder K Z) (hZ : Z ≤ fixV K) {x : ↥K}
    (hx : ∀ u : W ⧸ Z, ((toAutQuot hZK x : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) u = u → u = 1) :
    fixV (Subgroup.zpowers (x : MulAut W)) = Z := by
  apply le_antisymm
  · intro w hw
    have hzw : ((toAutQuot hZK x : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w) =
        QuotientGroup.mk w := by
      rw [toAutQuot_apply_mk, hw (x : MulAut W) (Subgroup.mem_zpowers _)]
    exact (QuotientGroup.eq_one_iff w).mp (hx _ hzw)
  · intro z hz
    rw [mem_fixV]
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact CFSG.Quasithin.Asc81c.Pf.zpow_apply_eq
      ((mem_fixV.mp (hZ hz)) (x : MulAut W) x.2) i

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1
