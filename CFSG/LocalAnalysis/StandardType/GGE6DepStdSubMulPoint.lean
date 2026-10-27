module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggStdSub_mul_point {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K) :
    D = Subgroup.closure {x, x * y} ∧ Subgroup.zpowers (x * y) ≠ Subgroup.zpowers x ∧
      Subgroup.zpowers (x * y) ≠ Subgroup.zpowers y := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hI : GGThmIHyp p B x L := hcfg.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxD : x ∈ D := hDJ.1.2.2.2.1
  have hcardD : Nat.card D = p ^ 2 := hDJ.1.2.2.1
  have hcl : D = Subgroup.closure {x, y} := hK.2.1
  have hyD : y ∈ D := by
    rw [hcl]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hxyD : x * y ∈ D := D.mul_mem hxD hyD
  have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
  obtain ⟨-, -, -, hyp⟩ := facts_of_closure_pair hI hDJ hcl
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hy
    have hle : D ≤ Subgroup.zpowers x := by
      rw [hcl, closure_pair_eq_sup]
      exact sup_le le_rfl (Subgroup.zpowers_le.mpr hy)
    have hcardle : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [hcardD, Nat.card_zpowers] at hcardle
    have hle' : orderOf x ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
    nlinarith [hp.two_le]
  have hxyx : x * y ∉ Subgroup.zpowers x := by
    intro h
    apply hyx
    have hxinv : x⁻¹ ∈ Subgroup.zpowers x := Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
    have hmem := Subgroup.mul_mem _ hxinv h
    simpa using hmem
  refine ⟨eq_closure_pair_of_mem hI hDJ hxyD hxyx, ?_, ?_⟩
  · intro heq
    exact hxyx (heq ▸ Subgroup.mem_zpowers (x * y))
  · intro heq
    have hxyp : x * y ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers (x * y)
    have hyinv : y⁻¹ ∈ Subgroup.zpowers y := Subgroup.inv_mem _ (Subgroup.mem_zpowers y)
    have hx : x ∈ Subgroup.zpowers y := by
      have hmem := Subgroup.mul_mem _ hxyp hyinv
      simpa [mul_assoc] using hmem
    have hle : D ≤ Subgroup.zpowers y := by
      rw [hcl, closure_pair_eq_sup]
      exact sup_le (Subgroup.zpowers_le.mpr hx) le_rfl
    have hcardle : Nat.card D ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hle
    rw [hcardD, Nat.card_zpowers] at hcardle
    have hle' : orderOf y ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hyp)
    nlinarith [hp.two_le]

end CFSG.StandardType

end
