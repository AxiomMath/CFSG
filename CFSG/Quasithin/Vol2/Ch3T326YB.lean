module

public import CFSG.Quasithin.Vol2.Ch3T326R
public import CFSG.Quasithin.Vol2.Ch3T326Y

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem concl_ii (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (hB48 : D36B48q) (h6 : Vol2.Ch11.TmpL6_3_2_2_six)
    [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hV : conjClosure V₀ T =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
    (s : G) (hs : s ∈ T) (hsn : s ∉ Subgroup.normalizer (L : Set G)) (x : G) (hx : x ∈ T)
    (hDx : D3Std (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))))
    (hlt : (CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) <
      orbSup (autOn T (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))))
    (htriv : ∀ v ∈ (CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))),
      ∀ g ∈ conjAutSub (conjAct (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩)
        (autOn L (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))), g v = v)
    (hU : ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
      Subgroup.centralizer (CFSG.conjugate L s : Set G))
    (h32 : D36L32
        (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))) :
    Concl326Cii T L V₀ := by
  have hbot := c.inf_fixV_eq_bot hA37 hA38 hB48 h6 hs hsn hx hDx hlt htriv h32
  have hcard8 := c.card_V₀_of_d36L32 hx h32.2.2.2 hbot
  have hMp := c.autOn_L₀_eq hA37 hA38 hs hsn
  have hUfix := c.fix_of_le_centralizer hs hU
  have hLVM := c.L_le_NVM
  have hHVM := c.H_le_NVM
  have hUVM := Subgroup.le_normalizer_iff_commutator_le_left.mp hLVM
  have hcomm := commSub_top_autOn (VM := conjClosure (conjClosure V₀ T)
    (Subgroup.normalizer (conjClosure L T : Set G))) hLVM
  have hxVM : CFSG.conjugate V₀ x ≤ conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)) :=
    le_of_le_of_eq (Subgroup.map_mono ((T325.V₀_le_V T V₀).trans
      (T325.V_le_VM T (conjClosure L T) V₀))) (c.conjugate_VM (c.T_le_M hx))
  have horb : orbSup (autOn T (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))))
      ((CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))) = ⊤ := by
    rw [c.orbSup_conjugate hx, Subgroup.subgroupOf_eq_top.mpr hV.ge]
  obtain ⟨hL32', ⟨r₀, hr₀T, hr₀N, hr₀s⟩, hall, -⟩ := h32
  have hL32 := isPSL_of_autSub_top horb hL32'
  have hVU : (CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) ≤
      commSub ⊤ (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))) := by
    have h1 := (hall r₀ hr₀T hr₀N hr₀s).1
    rw [horb] at h1
    rw [h1]
    exact le_sup_left
  have hstab := fun n (hn : n ∈ autOn T (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))) hnL hin =>
    stab_of_inner hDx horb hMp hVU hUfix hn hnL hin
  have hr₀out : ¬ IsInnerOn (autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))) r₀ := fun hin =>
    hr₀s (mem_stabSub_of_map_eq' (hstab r₀ hr₀T hr₀N hin))
  obtain ⟨g₀, hg₀T, rfl⟩ := Setup.mem_autOn_iff.mp hr₀T
  have hg₀L : (g₀ : G) ∈ Subgroup.normalizer (L : Set G) :=
    c.mem_normalizer_of_conjAct hA37 hA38 hg₀T hr₀N
  have hg₀H : (g₀ : G) ∈ L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) :=
    Subgroup.mem_sup_right ⟨hg₀T, hg₀L⟩
  have hA : ∀ g (hg : g ∈ T ⊓ Subgroup.normalizer (L : Set G)),
      conjAct _ ⟨g, hHVM (Subgroup.mem_sup_right hg)⟩ ∈
        stabSub ((CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) →
      g ∈ L ⊔ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))) := by
    intro g hg hgs
    have hgT := Setup.mem_autOn_iff.mpr ⟨⟨g, hHVM (Subgroup.mem_sup_right hg)⟩, hg.1, rfl⟩
    have hgN := H13.autOn_le_normalizer hLVM hHVM c.H_le_NL
      (Setup.mem_autOn_iff.mpr
        ⟨⟨g, hHVM (Subgroup.mem_sup_right hg)⟩, Subgroup.mem_sup_right hg, rfl⟩)
    refine c.mem_sup_of_isInnerOn hA37 hA38 hL32 (Subgroup.mem_sup_right hg) ?_
    by_contra hout
    have hin := isInnerOn_mul_inv hL32 hgN hr₀N hout hr₀out
    have h1 := hstab _ (Subgroup.mul_mem _ hgT (Subgroup.inv_mem _ hr₀T))
      (Subgroup.mul_mem _ hgN (Subgroup.inv_mem _ hr₀N)) hin
    apply hr₀s
    have h3 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_stabSub_of_map_eq' h1)) hgs
    rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at h3
  refine ⟨?_, hV, ⟨g₀, ⟨hg₀T, hg₀L⟩, fun hmem => hr₀out (c.isInnerOn_of_mem_sup hL32 hg₀H hmem)⟩,
    ⟨x, hx, fun s' hs' hs'n => ?_⟩, hcard8⟩
  · have hAut := autOn_eq_top hL32
      (InternalSec.autOn_le_autOn_of_le (c.L_le_L₀.trans Subgroup.le_normalizer))
      (InternalSec.autOn_le_autOn_of_le c.T_le_M hr₀T) hr₀N hr₀out
    obtain ⟨e₁⟩ := Bridge.nonempty_sl3_of_isPSL hL32
    exact ⟨(MulEquiv.subgroupCongr hAut).trans (Subgroup.topEquiv.trans
      (MulAut.congr (e₁.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2)))))⟩
  · have hs'H : s'⁻¹ ∈ L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) :=
      Subgroup.mem_sup_right (Subgroup.inv_mem _ hs')
    obtain ⟨r, hrdef⟩ : ∃ r, r = conjAct (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s'⁻¹, hHVM hs'H⟩ := ⟨_, rfl⟩
    have hrT : r ∈ autOn T (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) := by
      rw [hrdef]
      exact Setup.mem_autOn_iff.mpr ⟨⟨s'⁻¹, hHVM hs'H⟩, T.inv_mem hs'.1, rfl⟩
    have hrN : r ∈ Subgroup.normalizer (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) : Set _) := by
      rw [hrdef]
      exact H13.autOn_le_normalizer hLVM hHVM c.H_le_NL
        (Setup.mem_autOn_iff.mpr ⟨⟨s'⁻¹, hHVM hs'H⟩, hs'H, rfl⟩)
    have hrs : r ∉ stabSub ((CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))) := by
      intro hrs
      apply hs'n
      refine hA s' hs' ?_
      have h1 := Subgroup.inv_mem _ hrs
      rw [hrdef, ← map_inv] at h1
      have e : (⟨s'⁻¹, hHVM hs'H⟩ : Subgroup.normalizer (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)) : Set G))⁻¹ =
          ⟨s', hHVM (Subgroup.mem_sup_right hs')⟩ := Subtype.ext (inv_inv s')
      rwa [e] at h1
    obtain ⟨hU', hsum⟩ := hall r hrT hrN hrs
    rw [horb, hcomm] at hU' hsum
    have hxsVM : CFSG.conjugate (CFSG.conjugate V₀ x) s' ≤ conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)) :=
      le_of_le_of_eq (Subgroup.map_mono hxVM) (c.conjugate_VM (c.T_le_M hs'.1))
    have hmap : ((CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))).map r.toMonoidHom =
        (CFSG.conjugate (CFSG.conjugate V₀ x) s').subgroupOf (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))) := by
      rw [hrdef, map_conjAct_subgroupOf hxVM]
      show (CFSG.conjugate (CFSG.conjugate V₀ x) s'⁻¹⁻¹).subgroupOf _ = _
      rw [inv_inv]
    rw [hmap] at hU' hsum
    have h5 := inf_eq_bot_of_isSumMod hsum
      (le_bot_iff.mp ((inf_le_inf_left _ inf_le_right).trans hbot.le))
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.subgroupOf_sup hxVM hxsVM] at hU'
      have h4 := Subgroup.subgroupOf_inj.mp hU'
      rwa [inf_of_le_left hUVM, inf_of_le_left (sup_le hxVM hxsVM)] at h4
    · rw [eq_bot_iff]
      intro y hy0
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy0
      have hy : (⟨y, hxVM hy1⟩ : ↥(conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)))) ∈
          (CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
              (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
            (CFSG.conjugate (CFSG.conjugate V₀ x) s').subgroupOf (conjClosure (conjClosure V₀ T)
              (Subgroup.normalizer (conjClosure L T : Set G))) :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hy1, Subgroup.mem_subgroupOf.mpr hy2⟩
      rw [h5, Subgroup.mem_bot] at hy
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hy)

end Ctx

end CFSG.Quasithin.H13.T326
