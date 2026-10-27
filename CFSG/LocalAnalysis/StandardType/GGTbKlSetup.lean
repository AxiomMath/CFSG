module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalTwo
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoOmegaNbr
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoOmegaEnd
import CFSG.LocalAnalysis.StandardType.GGHalfRowData
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGF4QTwoOmegaNbrCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
open CFSG.RankThree.PartOne.KCOrthogonal


theorem ggF4QTwoOmegaEnd_setup
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hIL : GGInnerDiagOn Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr 3 B x D J y K)
    (hL : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    ∃ (ψ : ↥L ≃* ↥Two.omega) (z : G) (hzL : z ∈ L) (k : ℤ) (u : Fin 3 → ZMod 3),
      z ∈ D ∧ y = x ^ k * z ∧ y ∉ Subgroup.zpowers x ∧ x ∉ L ∧ x ∈ D ∧ Nat.card ↥D = 9 ∧
      ((ψ ⟨z, hzL⟩ : ↥Two.omega) : Two.Aut) = Two.tor u ∧
      (∀ g : ↥L, (g : G) ∈ Bs ↔ ((ψ g : ↥Two.omega) : Two.Aut) ∈ (cm (ZMod 2)).range) ∧
      J ≤ L ∧ J ≤ Subgroup.centralizer (D : Set G) ∧ ⁅J, J⁆ = J ∧ J ≠ ⊥ ∧
      Bs ⊓ Subgroup.centralizer (J : Set G) = D ∧ L ≤ Subgroup.centralizer {x} ∧
      J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) := by
  have hBstar : GGBstar 3 B Bs := hC.2.1
  obtain ⟨hZ, hinner⟩ :=
    ggHalfRowDataInput_holds G Bs L hIL
      (Or.inl (ggF4QTwoOmegaNbr_hasLabel_of_marking_twD41 hL))
  have hnorm : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGInnerDiagOn.le_normalizer hIL
  have hCx : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hC.bstar_inf_centralizer_L
  have hLx : L ≤ Subgroup.centralizer {x} := hC.tableB_facts.2.2.2.1
  have hBea : CFSG.Open.IsElemAbelian 3 Bs := hBstar.2.1
  have hE : CFSG.Open.IsElemAbelian 3 ((Bs ⊓ L).subgroupOf L) :=
    (hBea.mono inf_le_left).subgroupOf L
  have hEcard : Nat.card ↥((Bs ⊓ L).subgroupOf L) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans
      (ggF4QTwoOmegaNbr_card_bstar_inf_L hC hIL hL)
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_twoOmega_of_marking_torus hZ hL hE hEcard
  have hmem : ∀ g : ↥L,
      (g : G) ∈ Bs ↔ ((ψ g : ↥Two.omega) : Two.Aut) ∈ (cm (ZMod 2)).range := by
    intro g
    have hg := hψ g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hg
    exact ⟨fun h => hg.mp ⟨h, g.2⟩, fun h => (hg.mpr h).1⟩
  have hyBs : y ∈ Bs := hBstar.1 hNb.1.2.1
  obtain ⟨-, hxD, hyD, hDcard⟩ := ggF4QTwoOmegaNbr_D_facts hC hNb
  have hynz : y ∉ Subgroup.zpowers x := ggF4QTwoOmegaNbr_y_not_mem_zpowers_x hC hNb
  obtain ⟨hJL, hJD⟩ := ggF4QTwoOmegaNbr_J_le hC
  obtain ⟨hJJ, hJbot⟩ := ggF4QTwoOmegaNbr_J_perfect_ne_bot hC
  have hJBD : Bs ⊓ Subgroup.centralizer (J : Set G) = D :=
    ggF4QTwoOmegaNbr_bstar_inf_centralizer_J hC hIL hL
  obtain ⟨k, z, hzBstarL, hyz⟩ :=
    ggF4QTwoOmegaNbr_bstar_split_zpowers hBstar hZ hnorm hinner hCx y hyBs
  have hzL : z ∈ L := hzBstarL.2
  have hzD : z ∈ D := by
    have hz_eq : z = x ^ (-k) * y := by rw [hyz]; group
    rw [hz_eq]
    exact D.mul_mem (D.zpow_mem hxD (-k)) hyD
  have hψz : ((ψ ⟨z, hzL⟩ : ↥Two.omega) : Two.Aut) ∈ (cm (ZMod 2)).range :=
    (hmem ⟨z, hzL⟩).mp hzBstarL.1
  obtain ⟨u, hu⟩ :
      ∃ u : Fin 3 → ZMod 3,
        ((ψ ⟨z, hzL⟩ : ↥Two.omega) : Two.Aut) = Two.tor u := by
    obtain ⟨w, hw⟩ := hψz
    exact ⟨Multiplicative.toAdd w,
      by rw [show Two.tor (Multiplicative.toAdd w) = cm (ZMod 2) w from rfl, hw]⟩
  have hxL : x ∉ L := by
    intro hx
    have hxcen : (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hLx g.2)
      first | exact h | exact h.symm
    rw [hZ, Subgroup.mem_bot] at hxcen
    have hx1 : x = 1 := by simpa using congrArg Subtype.val hxcen
    have hox := hC.orderOf_x
    rw [hx1, orderOf_one] at hox
    omega
  obtain ⟨-, -, -, -, hJLayer, -, -⟩ := hC.2.2.1
  exact ⟨ψ, z, hzL, k, u, hzD, hyz, hynz, hxL, hxD, hDcard, hu, hmem,
    hJL, hJD, hJJ, hJbot, hJBD, hLx, hJLayer⟩

end CFSG.StandardType

end
