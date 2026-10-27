module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.LocalAnalysis.StandardType.FF81.CentralizerOdd
import CFSG.LocalAnalysis.StandardType.FS81.S7Fusion
import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.StandardType.FF81.CentE6

open CFSG CFSG.Open

theorem centralizer_inf_centralizer_eq_zpowers {G : Type} [Group G] [Finite G] {n : ℕ}
    {b t : G} {L Y : Subgroup G} {K : ℕ → Subgroup G} (hchar : IsCharTwoType G)
    (hA : HypA G n b L) (hU : Upstream n b L K t) (hYD : YData n b L Y t)
    (hQY : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≤ Y) :
    Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers b := by
  obtain ⟨z, hz, hF⟩ := hU
  obtain ⟨N, hND, hNnormal, h3N, hcard⟩ :=
    CFSG.StandardType.FF81.exists_normal_compl_centralizer_inf_centralizer hA hz.loc
  have hNb : N ≤ Subgroup.centralizer ({b} : Set G) := hND.trans inf_le_left
  have hNY : N ≤ Subgroup.centralizer (Y : Set G) := hYD.core N hNb hNnormal h3N
  obtain ⟨S, hS, htS, hord, -⟩ := hYD.syl
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hNY hx) t (hS.1 htS)).symm
  have hNQ : N ≤ Subgroup.centralizer
      (pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => Subgroup.mem_centralizer_iff.mp (hNY hx) y (hQY hy)
  have hNp : N ≤ pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) :=
    (le_inf hNt hNQ).trans
      (CFSG.StandardType.FrameRoute.FS81.centralizer_inf_le_pCoreOf_of_isCharTwoType hchar hord)
  have hNcard : Nat.card N = 1 :=
    ((CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2
      (Subgroup.centralizer ({t} : Set G))).to_le hNp).card_eq_or_dvd.resolve_right
      (hF.odd_core N hNb hNnormal h3N).not_two_dvd_nat
  have hb : b ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hA.le hy) b (Set.mem_singleton b)).symm⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb) ?_).symm
  rw [hcard, hNcard, mul_one, Nat.card_zpowers, hA.ord]

end CFSG.StandardType.FF81.CentE6

end
