module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviCount
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofJoin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal.Symplectic CFSG.StandardType.SpJoin

section Facts

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.x_facts {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) :
    x ∈ Bs ∧ x ∈ Subgroup.centralizer (L : Set G) := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  refine ⟨hcfg.2.1.1 hS.2.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)

theorem GGNbr.facts {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hnbr : GGNbr p B x D J y K) :
    y ∈ Bs ∧ y ∈ Subgroup.centralizer (K : Set G) ∧ y ∈ D ∧ y ∉ Subgroup.zpowers x ∧ x ≠ 1 := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hDab : IsElemAbelian p D := hcfg.2.2.1.2.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)
  refine ⟨hcfg.2.1.1 hnbr.1.2.1, hyK, ?_, ?_, hS.2.2.1⟩
  · rw [hnbr.2.1]
    exact Subgroup.subset_closure (by simp)
  · intro hy
    have hD_le : D ≤ Subgroup.zpowers x := by
      rw [hnbr.2.1, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · exact hy
    have hzp_le : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
    have hD_eq : D = Subgroup.zpowers x := le_antisymm hD_le hzp_le
    have hxp : x ^ p = 1 := hDab.2 x hxD
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    have horder : orderOf x = p ^ 2 := by
      rw [← Nat.card_zpowers, ← hD_eq, hDcard]
    have hp2dvd : p ^ 2 ∣ p := by
      rw [← horder]
      exact hdvd
    have hp2le : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hp2dvd
    nlinarith [hp.two_le]

end Facts

end CFSG.StandardType
