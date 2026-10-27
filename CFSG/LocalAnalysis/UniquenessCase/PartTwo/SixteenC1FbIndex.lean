module

public import CFSG.Quasithin.Background.Harris.R1.QbetaPerf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c1_actTil_fix_of_mem_centralizer {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} {g : stabTil V₀ V} (hg : (g : G) ∈ centralizer ({x.val} : Set G)) :
    actTil V₀ V hV g (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
  have hcomm : (g : G) * x.val * (g : G)⁻¹ = x.val := by
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc (g : G) * x.val * (g : G)⁻¹ = x.val * (g : G) * (g : G)⁻¹ := by rw [hc]
      _ = x.val := by group
  have hact : actStab V₀ V hV g x = x := by
    apply IntMod.val_injective
    rw [actStab_apply_val, hcomm]
  rw [actTil_mk, hact]

private theorem s16c1_subgroupOf_perfectCore {H K : Subgroup G} (hHK : H ≤ K) :
    (perfectCore H).subgroupOf K = perfectCore (H.subgroupOf K) := by
  have h1 : perfectCore H = (perfectCore (H.subgroupOf K)).map K.subtype := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hHK]
  rw [h1]
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem s16c1_barSub_cent_le {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hL : L ≤ stabTil V₀ V) (x : IntMod V hV) :
    barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L) ≤
      ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x) := by
  intro φ hφ
  change φ ∈ lBar V₀ V hV L ⊓
    MulAction.stabilizer (MulAut (Vtil V₀ V hV)) (mkTil V₀ V hV x)
  rw [Subgroup.mem_inf]
  obtain ⟨g, hg, rfl⟩ :=
    (mem_barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L) φ).1 hφ
  refine ⟨actTil_mem_barSub V₀ V hV hg.2 g.2, ?_⟩
  rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
  exact s16c1_actTil_fix_of_mem_centralizer hg.1

theorem s16c1_relIndex_cent_le_card {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hL : L ≤ stabTil V₀ V) (x : IntMod V hV) :
    (barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L)).relIndex
      (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) ≤ Nat.card ↥V₀ := by
  classical
  let S : Subgroup (MulAut (Vtil V₀ V hV)) :=
    MulAction.stabilizer (MulAut (Vtil V₀ V hV)) (mkTil V₀ V hV x)
  let Y : Subgroup G := L ⊓ (S.comap (actTil V₀ V hV)).map (stabTil V₀ V).subtype
  have hYleL : Y ≤ L := fun _ hy => hy.1
  have hYstab : Y ≤ stabTil V₀ V := fun _ hy => hL (hYleL hy)
  have hYfix : ∀ g : ↥(stabTil V₀ V), (g : G) ∈ Y →
      actTil V₀ V hV g (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
    intro g hg
    have hg2 : (g : G) ∈ (S.comap (actTil V₀ V hV)).map (stabTil V₀ V).subtype := hg.2
    rw [Subgroup.mem_map] at hg2
    obtain ⟨g', hg'S, hg'g⟩ := hg2
    have hgg : g' = g := Subtype.ext hg'g
    have hmem : actTil V₀ V hV g ∈ S := by
      rw [← hgg]; exact hg'S
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hmem
  have hfixY : ∀ y ∈ Y, y * x.val * y⁻¹ * (x.val)⁻¹ ∈ V₀ := by
    intro y hy
    have h := hYfix ⟨y, hYstab hy⟩ hy
    have h1 : mkTil V₀ V hV (actStab V₀ V hV ⟨y, hYstab hy⟩ x) = mkTil V₀ V hV x := by
      rw [← actTil_mk]; exact h
    rw [mkTil_eq_iff, actStab_apply_val] at h1
    exact h1
  have hcent_le_Y : centralizer ({x.val} : Set G) ⊓ L ≤ Y := by
    intro g hg
    rw [Subgroup.mem_inf] at hg
    refine ⟨hg.2, Subgroup.mem_map.mpr ⟨⟨g, hL hg.2⟩, ?_, rfl⟩⟩
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact s16c1_actTil_fix_of_mem_centralizer (g := ⟨g, hL hg.2⟩) hg.1
  have hbarY : barSub V₀ V hV Y = ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x) := by
    apply le_antisymm
    · intro φ hφ
      change φ ∈ lBar V₀ V hV L ⊓
        MulAction.stabilizer (MulAut (Vtil V₀ V hV)) (mkTil V₀ V hV x)
      rw [Subgroup.mem_inf]
      obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV Y φ).1 hφ
      refine ⟨actTil_mem_barSub V₀ V hV (hYleL hg) g.2, ?_⟩
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hYfix g hg
    · intro φ hφ
      change φ ∈ lBar V₀ V hV L ⊓
        MulAction.stabilizer (MulAut (Vtil V₀ V hV)) (mkTil V₀ V hV x) at hφ
      rw [Subgroup.mem_inf] at hφ
      obtain ⟨hφL, hφw⟩ := hφ
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hφw
      obtain ⟨g, hgL, hgφ⟩ := (mem_barSub V₀ V hV L φ).1 hφL
      refine (mem_barSub V₀ V hV Y φ).2 ⟨g, ⟨hgL, ?_⟩, hgφ⟩
      refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def, hgφ]
      exact hφw
  have hYinf : Y ⊓ centralizer ({x.val} : Set G) =
      centralizer ({x.val} : Set G) ⊓ L := by
    apply le_antisymm
    · exact le_inf inf_le_right (le_trans inf_le_left hYleL)
    · exact le_inf hcent_le_Y inf_le_left
  have hkey := c8_relIndex_barSub_le (V₀ := V₀) (V := V) (hV := hV) x (Y := Y) hYstab hfixY
  rw [hYinf, hbarY] at hkey
  exact hkey

theorem s16c1_barSub_perfectCore {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {K : Subgroup G}
    (hK : K ≤ stabTil V₀ V) :
    barSub V₀ V hV (perfectCore K) = perfectCore (barSub V₀ V hV K) := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  unfold barSub
  rw [s16c1_subgroupOf_perfectCore hK, map_perfectCore]

theorem s16c1_barSub_xInf_eq {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hcard : Nat.card ↥V₀ ≤ 4) (hL : L ≤ stabTil V₀ V) (x : IntMod V hV)
    (hperf : ⁅ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x),
        ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)⁆ =
      ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) :
    barSub V₀ V hV (xInf L x.val) = ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x) := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hBP : barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L) ≤
      ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x) := s16c1_barSub_cent_le hL x
  have hidx : (barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L)).relIndex
      (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) ≤ 4 :=
    le_trans (s16c1_relIndex_cent_le_card hL x) hcard
  haveI : Finite ↥(ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) := Subtype.finite
  have hPB : ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x) ≤
      barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L) :=
    CFSG.Quasithin.Background.Harris.R1.perfect_le_of_index_le_four
      (K := ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x))
      (Stab := barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L))
      hperf hBP hidx
  have hEq : barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L) =
      ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x) := le_antisymm hBP hPB
  calc barSub V₀ V hV (xInf L x.val)
      = barSub V₀ V hV (perfectCore (centralizer ({x.val} : Set G) ⊓ L)) := rfl
    _ = perfectCore (barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L)) :=
        s16c1_barSub_perfectCore (K := centralizer ({x.val} : Set G) ⊓ L)
          (inf_le_right.trans hL)
    _ = perfectCore (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) := by rw [hEq]
    _ = ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x) :=
        perfectCore_eq_self_of_perfect hperf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
