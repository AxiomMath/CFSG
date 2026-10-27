module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepZpowersInf
public import CFSG.LocalAnalysis.StandardType.GGE6DepNormalizerOfConj
public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootGamma
public import CFSG.LocalAnalysis.StandardType.GGE6DepNoTransvectionGamma

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_perfect_le_layer {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian 3 Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k) (hnt : GGNoTransvection 3 Bs)
    {R : Type} [Group R] {I : Set (MulAut R)} {ψ : ↥L →* R}
    (hTB : GGTorusTBGroup 3 5 R I ↥L ψ (ggGamma L hBsN).range)
    (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5) (hBl : GGE6DepBlocks R I)
    {c : ↥Bs} (hcL : (c : G) ∈ L) (hc : GGCorootPt 3 (ggAutomizer L Bs) c) {P : Subgroup G}
    (hP : P ≤ L ⊓ Subgroup.centralizer ({(c : G)} : Set G)) (hPP : ⁅P, P⁆ = P) :
    P ≤ LargeEvenLayer (L ⊓ Subgroup.centralizer ({(c : G)} : Set G)) := by
  have hxmem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hker]; exact Subgroup.mem_zpowers x
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := hxmem.2
  have hxp : x ^ 3 = 1 := hBs.2 x hxmem.1
  have hxL : Subgroup.zpowers x ⊓ L = ⊥ :=
    GGE6Dep.zpowers_inf_eq_bot_of_centralizer (p := 3) (by norm_num) hxC hxp hZ
  have hNT : ∀ φ ∈ ggTorusAut (ggGamma L hBsN).range, ¬ GGIsTransvection 3 φ :=
    ggTorusAut_noTransvection_gamma (p := 3) (by norm_num) hBs hBsN hker hZ hBsL hnt
  have hc' : GGCorootPt 3 (ggTorusAut (ggGamma L hBsN).range)
      ((ggGamma L hBsN).rangeRestrict c) :=
    ggCorootPt_gamma (p := 3) (by norm_num) (by norm_num) hBs hBsN hker hxL hcL hc
  obtain ⟨hK5, -⟩ := hBl ↥L ψ (ggGamma L hBsN).range hTB hcard hNT
  set P' : Subgroup ↥L := P.comap L.subtype with hP'def
  have hPmap : P'.map L.subtype = P := by
    have hPL : P ≤ L.subtype.range := by
      rw [Subgroup.range_subtype]
      exact hP.trans inf_le_left
    exact Subgroup.map_comap_eq_self hPL
  have hP'le : P' ≤ ggFix (ggGamma L hBsN c) := by
    intro q hq
    rw [mem_ggFix]
    apply Subtype.ext
    rw [ggGamma_coe]
    have hqP : L.subtype q ∈ P := hq
    have hqc : (c : G) * (q : G) = (q : G) * (c : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hP hqP).2).symm
    rw [hqc]; group
  have hP'perf : ⁅P', P'⁆ = P' := by
    refine Subgroup.map_injective L.subtype_injective ?_
    rw [Subgroup.map_commutator, hPmap, hPP]
  have hlayer : (⨆ (J : Subgroup ↥L)
      (_ : IsComponentOf J (ggFix (ggGamma L hBsN c))), J)
      ≤ LargeEvenLayer (ggFix (ggGamma L hBsN c)) :=
    iSup_le fun J => iSup_le fun hJ => le_sSup hJ
  have hP'layer : P' ≤ LargeEvenLayer (ggFix (ggGamma L hBsN c)) :=
    (hK5 ((ggGamma L hBsN).rangeRestrict c) hc' P' hP'le hP'perf).trans hlayer
  rw [← hPmap]
  calc P'.map L.subtype
      ≤ (LargeEvenLayer (ggFix (ggGamma L hBsN c))).map L.subtype :=
        Subgroup.map_mono hP'layer
    _ = LargeEvenLayer ((ggFix (ggGamma L hBsN c)).map L.subtype) :=
        (largeEvenLayer_map_of_injective L.subtype L.subtype_injective _).symm
    _ = LargeEvenLayer (L ⊓ Subgroup.centralizer ({(c : G)} : Set G)) := by
        rw [map_ggFix_ggGamma L hBsN c]

end CFSG.StandardType

end
