module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsElevenEight
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJModel
import CFSG.Quasithin.Background.SmithB45J2Small28
import CFSG.Quasithin.Background.SmithB51G2DExcl
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.Quasithin.EmptyFaithful.S151bW3Mod
import CFSG.GroupTheory.InvertingInvolutionRank
import CFSG.GroupTheory.ElemAbelianPlaneAction
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsIrrOnInvolution
import CFSG.Quasithin.Background.D2RkIdxBounds
public import CFSG.CharacterTheory.SteinbergBYFieldFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem w4Lem11_8Rk_of_inverts
    (hK : K_J2InvertsGen) : W4Lem11_8Rk := by
  intro W _ _ hW Y L hLY hN hL hirr hm
  classical
  have hcardL : Nat.card L = 604800 := by
    obtain ⟨e⟩ := hL
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  have heven : Even (Nat.card Y) := by
    have h := Subgroup.card_dvd_of_le hLY
    rw [hcardL] at h
    exact even_iff_two_dvd.2 (dvd_trans (by norm_num) h)
  obtain ⟨t, htY, ht2, htm⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam Y heven
  obtain ⟨l, hl, htl⟩ := exists_not_commute_of_isIrrOn hW hirr ht2
  have hKs : IsSpor ↥(L.subgroupOf Y) .J2 := by
    obtain ⟨e⟩ := hL
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLY).trans e⟩
  have ht2' : (⟨t, htY⟩ : Y) * ⟨t, htY⟩ = 1 := by
    apply Subtype.ext
    show t * t = 1
    rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hnc : ∃ k ∈ L.subgroupOf Y, (⟨t, htY⟩ : Y) * k ≠ k * ⟨t, htY⟩ :=
    ⟨⟨l, hLY hl⟩, Subgroup.mem_subgroupOf.2 hl, fun h => htl (congrArg Subtype.val h)⟩
  obtain ⟨x, -, g, -, hord, hgen⟩ := hK (↥Y) (L.subgroupOf Y) hN hKs ⟨t, htY⟩ ht2' hnc
  have hordy : orderOf ((x : MulAut W)⁻¹ * (t * x * t⁻¹)) = 5 ∨
      orderOf ((x : MulAut W)⁻¹ * (t * x * t⁻¹)) = 7 := by
    have e : ((x⁻¹ * (⟨t, htY⟩ * x * (⟨t, htY⟩ : Y)⁻¹) : Y) : MulAut W) =
        (x : MulAut W)⁻¹ * (t * x * t⁻¹) := rfl
    rw [← e, Subgroup.orderOf_coe]
    exact hord
  have hgenL : Subgroup.closure ({(x : MulAut W)⁻¹ * (t * x * t⁻¹),
      (g : MulAut W) * ((x : MulAut W)⁻¹ * (t * x * t⁻¹)) * (g : MulAut W)⁻¹} :
        Set (MulAut W)) = L := by
    have h1 := congrArg (Subgroup.map Y.subtype) hgen
    rw [MonoidHom.map_closure, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLY,
      Set.image_pair] at h1
    exact h1
  have hfixL : fixV L = ⊥ := by
    have hst : StableUnder L (fixV L) := by
      intro l hl u hu
      rw [mem_fixV] at hu ⊢
      intro l' hl'
      rw [hu l hl]
      exact hu l' hl'
    rcases hirr.2.2.2 _ hst bot_le le_top with h0 | h1
    · exact h0
    · exfalso
      have hLbot : L = ⊥ := by
        rw [eq_bot_iff]
        intro l hl
        rw [Subgroup.mem_bot]
        refine MulEquiv.ext fun v => ?_
        have hv : v ∈ fixV L := by rw [h1]; exact Subgroup.mem_top v
        exact (mem_fixV.1 hv) l hl
      rw [hLbot, Subgroup.card_bot] at hcardL
      omega
  set y : MulAut W := (x : MulAut W)⁻¹ * (t * x * t⁻¹) with hy
  have hfix2 : fixV (Subgroup.zpowers y) ⊓
      fixV (Subgroup.zpowers ((g : MulAut W) * y * (g : MulAut W)⁻¹)) = ⊥ := by
    rw [← FixVLat.fixV_sup_eq, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, ← Set.insert_eq, hgenL, hfixL]
  have hrk1 : rkIdx (fixV (Subgroup.zpowers y)) ≤ 2 * E3.mParam Y := by
    have h := CFSG.GroupTheory.rk_commV_conj_comm_le (W := W) (φ := t) (x := (x : MulAut W))
      (y := y) rfl
    rw [← rkIdx_fixV_zpowers, ← rkIdx_fixV_zpowers, htm] at h
    exact h
  have hrk2 : rkIdx (fixV (Subgroup.zpowers y)) ≤ 12 := by
    have h25 : (2 : ZMod 5) ≠ 0 := by decide
    have h27 : (2 : ZMod 7) ≠ 0 := by decide
    rcases hordy with h5 | h7
    · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hd := orderOf_two_dvd_rkIdx_fixV (p := 5) hW h25 h5
      rw [CFSG.GroupTheory.PlaneAction.orderOf_two_zmod_five] at hd
      omega
    · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hd := orderOf_two_dvd_rkIdx_fixV (p := 7) hW h27 h7
      rw [CFSG.GroupTheory.PlaneAction.orderOf_two_zmod_seven] at hd
      omega
  have hrkW : rk W ≤ 24 := by
    have h1 := rkIdx_inf_le_add (fixV (Subgroup.zpowers y))
      (fixV (Subgroup.zpowers ((g : MulAut W) * y * (g : MulAut W)⁻¹)))
    rw [hfix2, rkIdx_fixV_conj151b] at h1
    have h2 : rkIdx (⊥ : Subgroup W) = rk W := by
      have := rk_add_rkIdx (⊥ : Subgroup W)
      rw [rk_bot] at this
      omega
    omega
  have hcard : Nat.card W < 2 ^ 28 := by
    rw [card_eq_two_pow_rk hW]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨π, hπ⟩ :=
    J2Mod.j2SmallModules_holds_28 W hW L hL (isIrrSec_of_isIrrOn_top hirr) hcard
  have hW4096 : Nat.card W = 2 ^ 12 := by
    rw [CFSG.Quasithin.B5.G2D.card_eq_mod hπ, CFSG.Quasithin.B5.G2D.card_zornQMod]
    have hF4 : Fintype.card CFSG.CharacterTheory.SteinbergBY.FieldFour = 4 := rfl
    norm_num [Nat.card_eq_fintype_card, hF4]
  rw [card_eq_two_pow_rk hW] at hW4096
  exact Nat.pow_right_injective (le_refl 2) hW4096

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
