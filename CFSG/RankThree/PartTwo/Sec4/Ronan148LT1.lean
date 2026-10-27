module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowGH
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowRuTh

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem commutator_self_eq_of_isPerfect {S : Type*} [Group S] {Y : Subgroup S}
    (hp : Group.IsPerfect ↥Y) : ⁅Y, Y⁆ = Y := by
  rw [← Subgroup.map_subtype_commutator, hp.commutator_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem eq_bot_of_layer {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hL : PerfectInLayer β)
    (h3 : ∀ J : Subgroup S, CFSG.Open.IsComponentOf J (fixSubgroup β) →
      3 ∣ Nat.card J)
    {Y : Subgroup S} (hY : Y ≤ Sec4.autFix β) (hsn : (Y.subgroupOf (Sec4.autFix β)).IsSubnormal)
    (hp : Group.IsPerfect ↥Y) (h3Y : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have hfix : Sec4.autFix β = fixSubgroup β := Subgroup.ext fun _ => Iff.rfl
  rw [hfix] at hY hsn
  have hYsn : CFSG.Open.IsSubnormal Y (fixSubgroup β) :=
    open_isSubnormal_of_subgroupOf hY hsn
  have hYY := commutator_self_eq_of_isPerfect hp
  have hYE := hL Y hY hYY
  have hcomm : ∀ J, J ∈ {K | CFSG.Open.IsComponentOf K (fixSubgroup β)} →
      J ≤ Subgroup.centralizer (Y : Set S) := by
    intro J hJ
    rcases b3Lie_comp_le_or_comm hJ hY hYsn with h | h
    · exact absurd ((h3 J hJ).trans (Subgroup.card_dvd_of_le h)) h3Y
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hEc : CFSG.Open.GLALayer (fixSubgroup β) ≤
      Subgroup.centralizer (Y : Set S) := sSup_le hcomm
  have hYc : Y ≤ Subgroup.centralizer (Y : Set S) := hYE.trans hEc
  have hbot : ⁅Y, Y⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hYc
  rwa [hYY] at hbot

theorem row143_of_layer {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (h3S : 3 ∣ Nat.card S) (hOut : Group.IsSolvable (Outer S))
    (h : ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → PerfectInLayer β ∧
      ∀ J : Subgroup S, CFSG.Open.IsComponentOf J (fixSubgroup β) →
        3 ∣ Nat.card J) : Row143 S := by
  refine row143_of_inner_kgroup hS hnc (fun P _ hPp _ => le_inner_of_perfect_outSolvable hOut P hPp)
    fun β hβ Y hY hsn _ hp h3Y => ?_
  by_cases hβ1 : β = 1
  · subst hβ1
    have htop : Sec4.autFix (1 : MulAut S) = ⊤ := Subgroup.ext fun x => by
      simp [Sec4.mem_autFix]
    rw [htop] at hY hsn
    have hsn' : Y.IsSubnormal := by
      have e : Y.subgroupOf ⊤ = Y.comap (⊤ : Subgroup S).subtype := rfl
      have := hsn.map (f := (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).toMonoidHom)
        Subgroup.topEquiv.surjective
      convert this using 1
      ext x
      simp [Subgroup.mem_subgroupOf]
    rcases hsn'.eq_bot_or_top_of_isSimpleGroup hS with h1 | h1
    · exact h1
    · exfalso
      apply h3Y
      rw [h1, Subgroup.card_top]
      exact h3S
  · obtain ⟨hL, h3⟩ := h β hβ hβ1
    exact eq_bot_of_layer hL h3 hY hsn hp h3Y

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
