module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGFixSub
import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derCentB
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derExistsY
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggB2der_y_component {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) {y : ↥B} (hyD : (y : G) ∈ D)
    (hyx : (y : G) ∉ Subgroup.zpowers x) :
    L.normalizerMonoidHom (Subgroup.inclusion hBL y) ≠ 1 ∧
      L.normalizerMonoidHom (Subgroup.inclusion hBL y) ^ 3 = 1 ∧
      IsComponentOf (J.subgroupOf L)
        (ggFixSub (L.normalizerMonoidHom (Subgroup.inclusion hBL y))) ∧
      GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
        (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) := by
  classical
  obtain ⟨hxL, hx1, -, -⟩ := GGConfig.data_L hcfg
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre 3 B x L D J := hcfg.2.2.1
  have hB : IsElemAbelian 3 B := hS.1.1
  have hxB : x ∈ B := hS.2.1
  have hcyc := hS.2.2.2.2
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hDB : D ≤ B := hpre.1
  have hDcard : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  set e : MulAut ↥L := L.normalizerMonoidHom (Subgroup.inclusion hBL y) with he
  have he1 : e ≠ 1 := by
    intro h1
    have hyC : (y : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hfix : e ⟨l, hl⟩ = ⟨l, hl⟩ := by rw [h1]; rfl
      have hcoe : (y : G) * l * (y : G)⁻¹ = l := by
        have h := congrArg Subtype.val hfix
        rw [he, Subgroup.normalizerMonoidHom_apply_apply_coe] at h
        exact h
      calc l * (y : G) = (y : G) * l * (y : G)⁻¹ * (y : G) := by rw [hcoe]
        _ = (y : G) * l := by group
    have hmem : (y : G) ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨y.2, hyC⟩
    rw [ggB2der_centralizer_B_eq hB hxB hx1 hxL hcyc] at hmem
    exact hyx hmem
  have he3 : e ^ 3 = 1 := by
    have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using hB.2 (y : G) y.2)
    have hinc : (Subgroup.inclusion hBL y) ^ 3 = 1 := by
      rw [← map_pow, hy3, map_one]
    rw [he, ← map_pow, hinc, map_one]
  have hDgen : ∀ d ∈ D, ∃ i j : ℤ, d = x ^ i * (y : G) ^ j :=
    ggB2der_D_gen hB hDB hDcard hxD hx1 hyD hyx
  have hcent_eq : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
    apply le_antisymm
    · intro l hl
      refine ⟨hl.1, ?_⟩
      change ∀ h ∈ ({(y : G)} : Set G), h * l = l * h
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hl.2) (y : G) hyD
    · intro l hl
      obtain ⟨hlL, hly⟩ := hl
      refine ⟨hlL, ?_⟩
      change ∀ h ∈ (D : Set G), h * l = l * h
      intro d hd
      obtain ⟨i, j, rfl⟩ := hDgen d hd
      have hcx : Commute (l : G) x := by
        have h := hLx hlL
        change ∀ k ∈ ({(x)} : Set G), k * l = l * k at h
        exact (h x (Set.mem_singleton x)).symm
      have hcy : Commute (l : G) (y : G) := by
        have h := hly
        change ∀ k ∈ ({(y : G)} : Set G), k * l = l * k at h
        exact (h (y : G) (Set.mem_singleton (y : G))).symm
      exact (((hcx.zpow_right i).mul_right (hcy.zpow_right j)).eq).symm
  have hcomp' : IsComponentOf J (L ⊓ Subgroup.centralizer ({(y : G)} : Set G)) := by
    rwa [← hcent_eq]
  have hcompL : IsComponentOf (J.subgroupOf L) (ggFixSub e) := by
    have h := ggIsComponentOf_ggFixSub_normalizerMonoidHom (g := (y : G)) (hBL y.2) hcomp'
    rw [he]
    exact h
  have hlabel : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
      (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
    ggHasLabel_of_mulEquiv
      (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJL)
        (Subgroup.map_center_eq _)).symm hJ
  exact ⟨he1, he3, hcompL, hlabel⟩

end CFSG.StandardType
