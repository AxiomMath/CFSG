module

public import CFSG.LocalAnalysis.WeakClosure81.EightOne
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem isCalH0_of_le_normalizer {V H : Subgroup G} (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hHM : H ≤ Subgroup.normalizer (V : Set G)) : IsCalH0 V H :=
  ⟨hH, CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hH.1 hHM hV.isPGroup⟩

private abbrev conjGens (V T : Subgroup G) : Subgroup G :=
  ⨆ (g : G) (_ : conjSubgroup V g ≤ T ∧ conjSubgroup V g ≠ V), conjSubgroup V g

private theorem inf_centralizer_ne_bot_of_le_normalizer {X T : Subgroup G}
    (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT2 : IsPGroup 2 T) (hXne : X ≠ ⊥) :
    X ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ := by
  haveI : Group.IsNilpotent ↥T := hT2.isNilpotent
  haveI : (X.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXT).mpr hTX
  have hXsubne : X.subgroupOf T ≠ ⊥ := by
    intro h
    apply hXne
    rw [← Subgroup.map_subgroupOf_eq_of_le hXT, h, Subgroup.map_bot]
  have hZ : X.subgroupOf T ⊓ Subgroup.center ↥T ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hXsubne
  have hZmap : ((X.subgroupOf T) ⊓ Subgroup.center ↥T).map T.subtype ≠ ⊥ :=
    fun h => hZ ((Subgroup.map_eq_bot_iff_of_injective
      ((X.subgroupOf T) ⊓ Subgroup.center ↥T) T.subtype_injective).1 h)
  refine ne_bot_of_le_ne_bot hZmap ?_
  refine (Subgroup.map_inf_le (X.subgroupOf T) (Subgroup.center ↥T) T.subtype).trans
    (inf_le_inf ?_ ?_)
  · exact (Subgroup.map_subgroupOf_eq_of_le hXT).le
  · rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨q, hq⟩)

private theorem mem_normalizer_conjGens_of_le {V T : Subgroup G} {n : G}
    (hnV : n ∈ Subgroup.normalizer (V : Set G))
    (hnT : ∀ g : G, conjSubgroup V g ≤ T → conjSubgroup V (g * n) ≤ T) :
    n ∈ Subgroup.normalizer (conjGens V T : Set G) := by
  have h1 : conjSubgroup (conjGens V T) n ≤ conjGens V T := by
    have hmap : conjSubgroup (conjGens V T) n =
        ⨆ (g : G) (_ : conjSubgroup V g ≤ T ∧ conjSubgroup V g ≠ V),
          conjSubgroup V (g * n) := by
      rw [show conjSubgroup (conjGens V T) n =
          (conjGens V T).map (MulAut.conj n⁻¹).toMonoidHom from rfl]
      unfold conjGens
      rw [Subgroup.map_iSup]
      refine iSup_congr fun g => ?_
      rw [Subgroup.map_iSup]
      refine iSup_congr fun hg => ?_
      show (conjSubgroup V g).map (MulAut.conj n⁻¹).toMonoidHom = conjSubgroup V (g * n)
      exact conjSubgroup_conjSubgroup V g n
    rw [hmap]
    refine iSup₂_le fun g hg => ?_
    change conjSubgroup V (g * n) ≤
      ⨆ (g : G) (_ : conjSubgroup V g ≤ T ∧ conjSubgroup V g ≠ V), conjSubgroup V g
    refine le_iSup₂_of_le (g * n) ⟨hnT g hg.1, ?_⟩ le_rfl
    intro hVn
    exact hg.2 (by
      calc conjSubgroup V g = conjSubgroup (conjSubgroup V (g * n)) n⁻¹ := by
            rw [conjSubgroup_conjSubgroup]; congr 1; group
        _ = conjSubgroup V n⁻¹ := by rw [hVn]
        _ = V := conjSubgroup_eq_iff_mem_normalizer.mpr
            ((Subgroup.normalizer (V : Set G)).inv_mem hnV))
  have heq : conjSubgroup (conjGens V T) n = conjGens V T :=
    Subgroup.eq_of_le_of_card_ge h1 (E3.card_conjSubgroup (conjGens V T) n).ge
  exact conjSubgroup_eq_iff_mem_normalizer.mp heq

end CFSG.LocalAnalysis.WeakClosure81

end
