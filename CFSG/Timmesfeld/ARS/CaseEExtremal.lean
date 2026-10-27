module

public import CFSG.Timmesfeld.ARS.Sec8Hyp
public import CFSG.Timmesfeld.ARS.Sec13Connected

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem Sec13.leviClosed {A A₀ : Subgroup G} (hS : Sec13 R A A₀) : LeviClosed R A A₀ := by
  refine Levi.eq_of_commuting_iff_of_forall_special hS.hyp hS.mem hS.sec8.2 hS.opp fun E hE => ?_
  obtain ⟨X, hX, Y, hY, hXY⟩ := hS.nondeg
  exact ⟨X, hS.conn E hE X hX, Y, hS.conn E hE Y hY, hXY⟩

section Height

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hA₀

theorem exists_mem_lambdaStar_commuting_step {E X : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (S : Set (Subgroup G))
    (hES : ∀ Y ∈ S, Commuting E Y) (hXS : ∀ Y ∈ S, Commuting X Y ∨ Commuting E ⁅X, Y⁆) :
    ∃ E' ∈ lambdaStar R A A₀, Commuting E' X ∧ ∀ Y ∈ S, Commuting E' Y := by
  by_cases hEX : Commuting E X
  · exact ⟨E, hE, hEX, hES⟩
  have hs := special_of_not_commuting_of_mem_leviSet h hA hE hX hEX
  obtain ⟨hE', -, -⟩ := commutator_mem_lambdaStar h hA hAne hA₀ hE hX hs
  refine ⟨⁅E, X⁆, hE', hs.2.2, fun Y hY => ?_⟩
  refine commuting_iff_commutator_eq_bot.2 (Subgroup.commutator_commutator_eq_bot_of_rotate
    ?_ ?_)
  · rcases hXS Y hY with h1 | h1
    · rw [commuting_iff_commutator_eq_bot.1 h1, Subgroup.commutator_bot_left]
    · rw [Subgroup.commutator_comm]
      exact commuting_iff_commutator_eq_bot.1 h1
  · rw [Subgroup.commutator_comm Y E, commuting_iff_commutator_eq_bot.1 (hES Y hY),
      Subgroup.commutator_bot_left]

theorem exists_mem_lambdaStar_forall_commuting_of_height_le {ι : Type*} [Finite ι]
    (N : ι → Subgroup G) (hN : ∀ a, N a ∈ leviSet R A A₀) (ht : ι → ℕ)
    (hcl : ∀ a b, Commuting (N a) (N b) ∨ ∃ S : Set ι, (∀ c ∈ S, ht a < ht c ∧ ht b < ht c) ∧
      ⁅N a, N b⁆ ≤ ⨆ c ∈ S, N c) :
    ∃ E ∈ lambdaStar R A A₀, ∀ a, Commuting E (N a) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨E₀, hE₀⟩ := CaseD4.lambdaStar_nonempty h hA hA₀
  obtain ⟨m, hm⟩ : ∃ m, ∀ a, ht a < m := ⟨Finset.univ.sup ht + 1, fun a =>
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))⟩
  suffices ∀ d, ∃ E ∈ lambdaStar R A A₀, ∀ a, m - d ≤ ht a → Commuting E (N a) by
    obtain ⟨E, hE, hEa⟩ := this m
    exact ⟨E, hE, fun a => hEa a (by omega)⟩
  intro d
  induction d with
  | zero => exact ⟨E₀, hE₀, fun a ha => absurd (hm a) (by omega)⟩
  | succ d ih =>
    obtain ⟨E, hE, hEa⟩ := ih
    suffices ∀ T : Finset ι, (∀ a ∈ T, ht a = m - (d + 1)) → ∃ E' ∈ lambdaStar R A A₀,
        (∀ a, m - d ≤ ht a → Commuting E' (N a)) ∧ ∀ a ∈ T, Commuting E' (N a) by
      obtain ⟨E', hE', h1, h2⟩ := this (Finset.univ.filter fun a => ht a = m - (d + 1))
        fun a ha => (Finset.mem_filter.1 ha).2
      refine ⟨E', hE', fun a ha => ?_⟩
      by_cases hda : m - d ≤ ht a
      · exact h1 a hda
      · exact h2 a (Finset.mem_filter.2 ⟨Finset.mem_univ a, by omega⟩)
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨E, hE, hEa, fun a ha => absurd ha (Finset.notMem_empty a)⟩
    | insert b T hbT ihT =>
      intro hT
      obtain ⟨E', hE', h1, h2⟩ := ihT fun a ha => hT a (Finset.mem_insert_of_mem ha)
      have hb : ht b = m - (d + 1) := hT b (Finset.mem_insert_self b T)
      set S := {Y | ∃ a, Y = N a ∧ (m - d ≤ ht a ∨ a ∈ T)} with hSdef
      have hES : ∀ Y ∈ S, Commuting E' Y := by
        rintro _ ⟨a, rfl, ha | ha⟩
        · exact h1 a ha
        · exact h2 a ha
      have hXS : ∀ Y ∈ S, Commuting (N b) Y ∨ Commuting E' ⁅N b, Y⁆ := by
        rintro _ ⟨a, rfl, ha⟩
        rcases hcl b a with h3 | ⟨S', hS', hle⟩
        · exact Or.inl h3
        · right
          refine Commuting.mono ?_ le_rfl hle
          rw [commuting_iff_le_centralizer]
          refine iSup₂_le fun c hc => commuting_iff_le_centralizer.1 (h1 c ?_)
          have := (hS' c hc).1
          omega
      obtain ⟨E'', hE'', hE''b, hE''S⟩ :=
        exists_mem_lambdaStar_commuting_step h hA hAne hA₀ hE' (hN b) S hES hXS
      refine ⟨E'', hE'', fun a ha => hE''S _ ⟨a, rfl, Or.inl ha⟩, fun a ha => ?_⟩
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hE''b
      · exact hE''S _ ⟨a, rfl, Or.inr ha⟩

theorem exists_mem_lambdaStar_forall_commuting_of_height {ι : Type*} [Finite ι]
    (N : ι → Subgroup G) (hN : ∀ a, N a ∈ leviSet R A A₀) (ht : ι → ℕ)
    (hcl : ∀ a b, Commuting (N a) (N b) ∨ ∃ c, ⁅N a, N b⁆ = N c ∧ ht a < ht c ∧ ht b < ht c) :
    ∃ E ∈ lambdaStar R A A₀, ∀ a, Commuting E (N a) := by
  refine exists_mem_lambdaStar_forall_commuting_of_height_le h hA hAne hA₀ N hN ht
    fun a b => (hcl a b).imp_right fun ⟨c, hc, hac, hbc⟩ => ⟨{c}, ?_, ?_⟩
  · rintro _ rfl
    exact ⟨hac, hbc⟩
  · rw [hc]
    exact le_iSup₂_of_le (f := fun c' (_ : c' ∈ ({c} : Set ι)) => N c') c rfl le_rfl

end Height

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
include hS

theorem exists_mem_lambdaStar_commuting_step {E X : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (S : Set (Subgroup G))
    (hES : ∀ Y ∈ S, Commuting E Y) (hXS : ∀ Y ∈ S, Commuting X Y ∨ Commuting E ⁅X, Y⁆) :
    ∃ E' ∈ lambdaStar R A A₀, Commuting E' X ∧ ∀ Y ∈ S, Commuting E' Y :=
  _root_.CFSG.Timmesfeld.ARS.exists_mem_lambdaStar_commuting_step hS.hyp hS.mem hS.sec8.2 hS.opp
    hE hX S hES hXS

theorem exists_mem_lambdaStar_forall_commuting_of_height {ι : Type*} [Finite ι]
    (N : ι → Subgroup G) (hN : ∀ a, N a ∈ leviSet R A A₀) (ht : ι → ℕ)
    (hcl : ∀ a b, Commuting (N a) (N b) ∨ ∃ c, ⁅N a, N b⁆ = N c ∧ ht a < ht c ∧ ht b < ht c) :
    ∃ E ∈ lambdaStar R A A₀, ∀ a, Commuting E (N a) :=
  _root_.CFSG.Timmesfeld.ARS.exists_mem_lambdaStar_forall_commuting_of_height hS.hyp hS.mem
    hS.sec8.2 hS.opp N hN ht hcl

theorem exists_mem_lambdaStar_forall_commuting_of_height_le {ι : Type*} [Finite ι]
    (N : ι → Subgroup G) (hN : ∀ a, N a ∈ leviSet R A A₀) (ht : ι → ℕ)
    (hcl : ∀ a b, Commuting (N a) (N b) ∨ ∃ S : Set ι, (∀ c ∈ S, ht a < ht c ∧ ht b < ht c) ∧
      ⁅N a, N b⁆ ≤ ⨆ c ∈ S, N c) :
    ∃ E ∈ lambdaStar R A A₀, ∀ a, Commuting E (N a) :=
  _root_.CFSG.Timmesfeld.ARS.exists_mem_lambdaStar_forall_commuting_of_height_le hS.hyp hS.mem
    hS.sec8.2 hS.opp N hN ht hcl

end Sec13

end CFSG.Timmesfeld.ARS
