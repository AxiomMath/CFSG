module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95COpp
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CTypeA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem hp95 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) {x : G}
    (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t) (hnA : ¬ IsTypeA2 M Q Z B t x) {w : G}
    (hw : w ∈ Wt Q (Vt M (LB M Q B) B Z t)) (hxw : ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t) :
    w ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  obtain ⟨K, fK, finK, hK2, E, hnrm, φ, ψ, u, hK, hφ, hker, hψ, hQu, hu0, hBiff, hW, hpol, hLB,
    hLA⟩ := exists_points95 h34 hs hr
  haveI := hnrm
  let C : Coord95 hc t K := ⟨E, φ, ψ, u, hK, hφ, hker, hψ, hQu, hu0, hBiff, hW, hLB⟩
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  have h4 : 4 ≤ Fintype.card (Fin 2 ⊕ Fin 2) := by
    rw [Fintype.card_sum, Fintype.card_fin]
  have hrX : φ ⟨r, hrR⟩ ∈ StatedOmega (StatedQuadPlus 2 K) :=
    hφ ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hQu' : quadPlus 2 K ((φ ⟨r, hrR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) = 0 := by
    have h1 := (E.equiv ⟨φ ⟨r, hrR⟩, hrX⟩).map_of_mem u
    rw [E.app] at h1
    rw [h1, hQu]
  have huu' : polar (quadPlus 2 K)
      ((φ ⟨r, hrR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) u ≠ 0 := by
    rw [polar_comm]
    exact hpol
  have hLA' : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      E.LomGL ((φ ⟨r, hrR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) := by
    rw [hc.LB_conj (hc.Rt_le_M t hrR)]
    exact hLA
  obtain ⟨-, hN⟩ := h91b G M Q Z B hc n t hs r hr _ _ rfl rfl
  have hd := isOppDecomp95 h34 h91b hs hr
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ρ * y * ρ⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun ρ hρ y hy =>
    sec9_conj_mem_Wt hc ht hρ hy
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      ρ * y * ρ⁻¹ ∈ Vt M (LB M Q B) B Z t := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) y).mp hy
  have hLB_R : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA_R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hn : ∃ v : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) v
      ((φ ⟨x, hxR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnA (typeA2_of_polar_zero C hs hxL hxN hcon)
  exact Om10.mem_of_comm_nonA2 E hQnd h4 φ hφ hker hP hI hN hd hLA_R hLB_R hQu' hQu huu' hLA'
    hLB (y := ⟨x, hxR⟩) hxL hn hw hxw

end HS9

end CFSG.RankThree.GF2n.Stroth80
