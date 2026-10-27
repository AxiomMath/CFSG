module

public import CFSG.RankThree.GF2n.Tim79aCase1Conj
public import CFSG.RankThree.GF2n.Tim79aCase1Four
public import CFSG.RankThree.GF2n.Tim79aCase1End
public import CFSG.RankThree.GF2n.Tim79aWCQInputs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem false_of_case_one (hq : Nat.card (barOf V H V) = 2)
    (hX : barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V) : False := by
  have hEx := hc.exists_conj_ne
  have hTI : ∀ g ∈ H, conjSubgroup g V ≠ V → ∀ x ∈ P, ∀ y ∈ conjSubgroup g P,
      (∀ w ∈ wOf V H, x * w * x⁻¹ = y * w * y⁻¹) → ∀ w ∈ wOf V H, x * w = w * x :=
    fun g hg hne x hx y hy hxy =>
      hc.centralizes_of_act_eq (fun g' hg' hne' => hc.wOf_eq_mul_of_case_one hX hg' hne')
        hg hne hx hy hxy
  have hfree : ∀ g ∈ H, conjSubgroup g V ≠ V → ∀ v ∈ V, v ∉ wOf V H →
      ∀ b ∈ conjSubgroup g V, b ≠ 1 → v * b ≠ b * v :=
    fun g hg hne v hv hvW b hb hb1 => hc.not_commute_of_case_one hq hX hg hne hv hvW hb hb1
  have hF1 : ∀ t ∈ P, (∀ w ∈ wOf V H, t * t * w = w * (t * t)) →
      ∃ v ∈ V, ∀ w ∈ wOf V H, t * w * t⁻¹ = v * w * v⁻¹ :=
    fun t ht ht2 => hc.act_eq_of_sq_central hq hX hEx hTI hfree ht ht2
  exact hc.false_of_eq_V (hc.eq_V_of_actions hF1 (hc.mem_P_of_commute_of_case_one hq hX)
    fun c hcH hcW => hc.commutator_mem_wOf_of_centralizes hq hcH hcW)

end MinCex

theorem tim79aCase1Statement_holds : Tim79aCase1Statement :=
  fun _ _ _ _ _ _ _ _ hc hq hX => hc.toMinCex.false_of_case_one hq hX

end CFSG.RankThree.GF2n.Tim79a
