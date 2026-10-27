module

public import CFSG.Timmesfeld.ARS.Sec9Comps
public import CFSG.Timmesfeld.ARS.CaseD4Frame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

section Family

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hA₀

theorem levi_eq_iSup_gen : levi R A A₀ = ⨆ Δ : leviComps R A A₀, gen (Δ : Set (Subgroup G)) := by
  apply le_antisymm
  · refine gen_le fun X hX => ?_
    obtain ⟨Δ, hΔ, hXΔ⟩ := mem_comp_self hX
    exact (le_gen hXΔ).trans (le_iSup (fun Δ : leviComps R A A₀ => gen (Δ : Set (Subgroup G)))
      ⟨Δ, hΔ⟩)
  · exact iSup_le fun Δ => gen_mono fun X hX =>
      mem_leviSet_of_mem_leviComps h hA hAne hA₀ Δ.2 hX

theorem leviSL2Family_of_forall (hall : ∀ Δ ∈ leviComps R A A₀, IsSL2Comp Δ) :
    ∃ P Q : leviComps R A A₀ → Subgroup G, LeviSL2Family R A A₀ P Q ∧
      ∀ Δ : leviComps R A A₀, P Δ ∈ (Δ : Set (Subgroup G)) ∧ Q Δ ∈ (Δ : Set (Subgroup G)) := by
  choose P hP Q hQ hPQ hgen using fun Δ : leviComps R A A₀ => hall Δ Δ.2
  refine ⟨P, Q, ⟨fun Δ => mem_leviSet_of_mem_leviComps h hA hAne hA₀ Δ.2 (hP Δ),
    fun Δ => mem_leviSet_of_mem_leviComps h hA hAne hA₀ Δ.2 (hQ Δ), hPQ, fun Δ Δ' hne => ?_,
    ?_⟩, fun Δ => ⟨hP Δ, hQ Δ⟩⟩
  · rw [← hgen, ← hgen]
    exact commuting_gen_of_ne h hA hAne hA₀ Δ.2 Δ'.2 fun e => hne (Subtype.ext e)
  · rw [levi_eq_iSup_gen h hA hAne hA₀]
    exact iSup_congr fun Δ => hgen Δ

end Family

theorem false_of_card_two (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (hall : ∀ Δ ∈ leviComps R A A₀, IsSL2Comp Δ)
    (hcard : Nat.card (leviComps R A A₀) = 2) : False := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨P, Q, hPQ, -⟩ := leviSL2Family_of_forall h hA hAne hA₀ hall
  obtain ⟨a, b, hab, hall2⟩ : ∃ a b : leviComps R A A₀, a ≠ b ∧ ∀ i, i = a ∨ i = b := by
    obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.1 hcard
    refine ⟨a, b, hab, fun i => ?_⟩
    have hi : i ∈ ({a, b} : Set (leviComps R A A₀)) := huniv ▸ Set.mem_univ i
    simpa using hi
  have hPR : ∀ i, P i ∈ R := fun i => (hPQ.mem_left i).1.1
  have hQR : ∀ i, Q i ∈ R := fun i => (hPQ.mem_right i).1.1
  have : Finite (leviComps R A A₀) := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite (leviComps R A A₀)
  have hQQ : ∀ i j, Commuting (Q i) (Q j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact hR.commuting_self (hQR i)
    · exact hPQ.commuting_of_le hij le_sup_right le_sup_right
  obtain ⟨E, hE, hEQ⟩ := CaseD4.exists_mem_lambdaStar_forall_commuting h hA hAne hA₀
    hPQ.mem_right hQQ (CaseD4.lambdaStar_nonempty h hA hA₀) Finset.univ
  replace hEQ : ∀ i, Commuting (Q i) E := fun i => hEQ i (Finset.mem_univ i)
  have hER : E ∈ R := hE.1.1.1
  have hsa : Special R (P a) E :=
    CaseD4.special_of_commuting h hA hAne hmax hA₀ hPQ.swap hE a (hEQ a)
  set X := ⁅P a, E⁆ with hXdef
  have hX : X ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ (hPQ.mem_left a) hE hsa.symm).1 X
      hsa.1
    rw [Subgroup.commutator_comm E (P a)] at this
    exact this le_sup_right
  have hXR : X ∈ R := hsa.1
  have hXQb : Commuting (Q b) X :=
    (commuting_commutator_of_commuting (hPQ.commuting_of_le hab le_sup_left le_sup_right)
      (hEQ b).symm).symm
  have hsb : Special R (P b) X :=
    CaseD4.special_of_commuting h hA hAne hmax hA₀ hPQ.swap hX b hXQb
  set C := ⁅P b, X⁆ with hCdef
  have hC : C ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ (hPQ.mem_left b) hX hsb.symm).1 C
      hsb.1
    rw [Subgroup.commutator_comm X (P b)] at this
    exact this le_sup_right
  have hCP : ∀ i, Commuting (P i) C := by
    intro i
    rcases hall2 i with rfl | rfl
    · exact (commuting_commutator_of_commuting
        (hPQ.commuting_of_le (Ne.symm hab) le_sup_left le_sup_left) hsa.2.1).symm
    · exact hsb.2.1.symm
  obtain ⟨-, hECA⟩ := CaseD4.commutator_eq_of_extremal h hA hAne hmax hA₀ hPQ hE hEQ hC hCP
  have hEX : E ∈ lambdaSet R X := (mem_lambdaSet_commutator hR hiso (hPR a) hER hsa).2
  have hCX : C ∈ lambdaSet R X :=
    mem_lambdaSet_comm hsb.1 (mem_lambdaSet_commutator hR hiso (hPR b) hXR hsb).2
  have hle : A ≤ X := by
    rw [← hECA, ← (Q_eq_M h hXR).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M hEX) (QD.le_M hCX)
  have hAX : A = X := Subgroup.eq_of_le_of_card_ge hle (hR.card_eq hXR hA).le
  exact hX.1.1.2.1 hAX.symm

end Sec9

end CFSG.Timmesfeld.ARS
