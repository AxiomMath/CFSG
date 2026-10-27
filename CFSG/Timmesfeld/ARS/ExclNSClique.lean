module

public import CFSG.Timmesfeld.ARS.CaseEExtremal
public import CFSG.Timmesfeld.ARS.CaseHBasic
public import CFSG.Timmesfeld.ARS.Sec13Closed

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace ExclNS

variable {A A₀ : Subgroup G}

theorem exists_notMem_lambdaSet_of_mem_deltaSet (hS : Sec13 R A A₀) {B : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) :
    ∃ E ∈ deltaSet R A A₀ B, ∃ F ∈ deltaSet R A A₀ B, E ≠ F ∧ F ∉ lambdaSet R E := by
  have hR := hS.hyp.root
  obtain ⟨X, hX, x, hx, hne, F, hF, hF'⟩ := hS.exists_conjSub_ne_inter_nonempty hB
  have hxV : x ∈ levi R A A₀ := le_gen hX hx
  have hB' : conjSub B x ∈ lambdaStar R A A₀ := conjSub_mem_lambdaStar_of_mem_levi hR hB hxV
  rw [conjSet_deltaSet hR hxV] at hF'
  by_contra! hall
  have key : ∀ E ∈ deltaSet R A A₀ B, Commuting E (conjSub B x) := by
    intro E hE
    by_cases hEF : E = F
    · subst hEF
      exact hF'.2.1.2.2.symm
    · exact commuting_of_mem_deltaSet_of_mem_lambdaSet hS.hyp hS.mem hS.opp hB' hF' hE.1
        (hall F hF E hE (Ne.symm hEF))
  exact hne (hS.eq_of_forall_commuting hS.leviClosed hB' hB key).symm

theorem comp_eq (hS : Sec13 R A A₀) {E : Subgroup G} (hE : E ∈ leviSet R A A₀) :
    Levi.comp R A A₀ E = leviSet R A A₀ :=
  Set.Subset.antisymm (Levi.comp_subset hS.hyp hS.mem hS.sec8.2 hS.opp hE)
    fun F hF => hS.conn E hE F hF

theorem quotHyp (hS : Sec13 R A A₀) :
    Hyp (↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀))
      (quotClass (levi R A A₀) (leviSet R A A₀)) := by
  obtain ⟨E₀, hE₀, -⟩ := hS.nondeg
  have key := Levi.quotHyp hS.hyp hS.mem hS.sec8.2 hS.opp hE₀
    (by rw [comp_eq hS hE₀]; exact hS.nondeg)
  rw [comp_eq hS hE₀] at key
  exact key

theorem quot_injOn (hS : Sec13 R A A₀) :
    Set.InjOn (quotMap (levi R A A₀)) (leviSet R A A₀) := by
  obtain ⟨E₀, hE₀, -⟩ := hS.nondeg
  have key := Levi.quot_hinj hS.hyp hS.mem hS.sec8.2 hS.opp hE₀
  rw [comp_eq hS hE₀] at key
  exact key

theorem special_of_quot (hS : Sec13 R A A₀) {X Y : Subgroup G} (hX : X ∈ leviSet R A A₀)
    (hY : Y ∈ leviSet R A A₀)
    (h : Special (quotClass (levi R A A₀) (leviSet R A A₀)) (quotMap (levi R A A₀) X)
      (quotMap (levi R A A₀) Y)) : Special R X Y := by
  obtain ⟨E₀, hE₀, -⟩ := hS.nondeg
  have key := Levi.quot_hspec hS.hyp hS.mem hS.sec8.2 hS.opp hE₀
  rw [comp_eq hS hE₀] at key
  exact key X hX Y hY h

theorem quot_commutator (hS : Sec13 R A A₀) {X Y : Subgroup G} (hX : X ∈ leviSet R A A₀)
    (hY : Y ∈ leviSet R A A₀) (h : Special R X Y) : ⁅X, Y⁆ ∈ leviSet R A A₀ ∧
      quotMap (levi R A A₀) ⁅X, Y⁆ = ⁅quotMap (levi R A A₀) X, quotMap (levi R A A₀) Y⁆ := by
  obtain ⟨E₀, hE₀, -⟩ := hS.nondeg
  have key := Levi.quot_hcl hS.hyp hS.mem hS.sec8.2 hS.opp hE₀
  rw [comp_eq hS hE₀] at key
  exact key X hX Y hY h

theorem mem_lambdaSet_of_quot (hS : Sec13 R A A₀) {E F : Subgroup G} (hE : E ∈ leviSet R A A₀)
    (hF : F ∈ leviSet R A A₀)
    (h : quotMap (levi R A A₀) F ∈
      lambdaSet (quotClass (levi R A A₀) (leviSet R A A₀)) (quotMap (levi R A A₀) E)) :
    F ∈ lambdaSet R E := by
  have := hS.hyp.finite
  have hq := quotHyp hS
  have := hq.finite
  have hR' := hq.root
  have hiso' := hq.noIsolated
  set V := levi R A A₀
  set R' := quotClass V (leviSet R A A₀)
  have hER' : quotMap V E ∈ R' := ⟨E, hE, rfl⟩
  have hFR' : quotMap V F ∈ R' := ⟨F, hF, rfl⟩
  have hEF' : quotMap V E ∈ lambdaSet R' (quotMap V F) := mem_lambdaSet_comm hER' h
  obtain ⟨Q, hQ, hQle, hQE, hQF⟩ :=
    exists_mem_le_sup_ne_ne hR' hiso' hFR' hEF' (quotMap V E) (quotMap V F)
  obtain ⟨U', hU', u, hu, hEu⟩ := exists_mem_lambdaSet_conjSub_eq hR' hiso' hFR' hEF' hER'
    le_sup_right (Ne.symm h.1.2.1) hQ hQle hQF
  have hUE : U' ≠ quotMap V E := by
    rintro rfl
    exact hQE (hEu ▸ conjSub_eq_self_iff.2 (Subgroup.le_normalizer hu))
  rcases commuting_or_commutator_eq_of_mem_lambdaSet hq hFR' hU' hEF' hUE with hc | ⟨hs, hcomm⟩
  · exact absurd (hEu ▸ conjSub_of_forall_commute fun e he => hc u hu e he) hQE
  · obtain ⟨U, hU, rfl⟩ := hU'.1.1
    have hsU : Special R U E := special_of_quot hS hU hE hs
    obtain ⟨hUEΔ, hUEq⟩ := quot_commutator hS hU hE hsU
    have hUEF : ⁅U, E⁆ = F := quot_injOn hS hUEΔ hF (hUEq.trans hcomm)
    have := (mem_lambdaSet_commutator hS.hyp.root hS.hyp.noIsolated hU.1.1 hE.1.1 hsU).2
    rw [hUEF] at this
    exact mem_lambdaSet_comm hF.1.1 this

theorem not_sigmaEqLambda_quot (hS : Sec13 R A A₀) :
    ¬ SigmaEqLambda (quotClass (levi R A A₀) (leviSet R A A₀)) := by
  intro hSL
  have := hS.hyp.finite
  obtain ⟨B, hB⟩ := CaseD4.lambdaStar_nonempty hS.hyp hS.mem hS.opp
  obtain ⟨E, hE, F, hF, hEF, hFE⟩ := exists_notMem_lambdaSet_of_mem_deltaSet hS hB
  refine hFE (mem_lambdaSet_of_quot hS hE.1 hF.1 ?_)
  have hc : Commuting E F := commuting_of_mem_deltaSet hS.hyp hS.mem hS.opp hB hE hF
  have hσ : quotMap (levi R A A₀) F ∈
      sigmaSet (quotClass (levi R A A₀) (leviSet R A A₀)) (quotMap (levi R A A₀) E) :=
    ⟨⟨F, hF.1, rfl⟩, fun e => hEF (quot_injOn hS hE.1 hF.1 e.symm),
      LeviQuot.commuting_quotMap hc⟩
  rwa [hSL _ ⟨E, hE.1, rfl⟩] at hσ

end ExclNS

end CFSG.Timmesfeld.ARS
