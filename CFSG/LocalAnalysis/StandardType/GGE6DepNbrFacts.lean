module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_nbr_facts {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    ∃ _ : y ∈ Bs, y ∉ Subgroup.zpowers x ∧ K ≤ Subgroup.centralizer ({y} : Set G) ∧
      x ∉ Subgroup.centralizer (K : Set G) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hS : LargeEvenSHat p B y K := hnbr.1
  have hDab : IsElemAbelian p D := hcfg.2.2.1.2.1
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  refine ⟨hcfg.2.1.1 hS.2.1, ?_, hS.2.2.2.1, ?_⟩
  ·
    intro hy
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
  ·
    intro hx
    apply hnbr.2.2.2
    have hle : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hx
    rw [Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle]
    exact bot_le

end CFSG.StandardType

end
