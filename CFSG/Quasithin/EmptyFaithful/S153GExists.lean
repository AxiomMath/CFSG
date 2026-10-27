module

public import CFSG.Quasithin.EmptyFaithful.S153GJS0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Tools

variable {G : Type} [Group G]

private theorem cex_mem_normalizer_commutator {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

private theorem cex_commutator_eq_bot_of_perfect {N L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (h : ⁅⁅N, L⁆, L⁆ = ⊥) : ⁅N, L⁆ = ⊥ := by
  have h1 : ⁅⁅L, L⁆, N⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := L) (H₂ := L) (H₃ := N) ?_ h
    rw [Subgroup.commutator_comm L N]
    exact h
  rw [hL] at h1
  rw [Subgroup.commutator_comm N L]
  exact h1

end Tools

theorem countExists_of_ctx : CountExists := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := c25.facts.toFacts153.sylow
  have hLJ : L ≤ thompsonJ I := le_of_mem_cComp c25.conc.1
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIUI : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hIU : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := fun g hg =>
    cex_mem_normalizer_commutator (hIUI hg) (hIL hg)
  suffices h : ∃ A₀ : Subgroup G, IsMaxElemAbelian (Sgp153 T V₁) A₀ ∧
      ¬ A₀ ≤ Subgroup.centralizer (UL153 T I L : Set G) by
    obtain ⟨A₀, hA₀, hnc⟩ := h
    obtain ⟨B, hB, -⟩ := js0_exists_offender hA₀ hnc
    exact ⟨B, hB⟩
  by_contra hcon
  push Not at hcon
  have hJS : thompsonJ (Sgp153 T V₁) ≤ Subgroup.centralizer (UL153 T I L : Set G) :=
    iSup₂_le fun A hA => hcon A hA
  have hJI : thompsonJ I ≤ Subgroup.centralizer (UL153 T I L : Set G) :=
    thompsonJ_le_of_normalizer hsyl (B2F.le_normalizer_centralizer hIU) hJS
  have hLC : L ≤ Subgroup.centralizer (UL153 T I L : Set G) := hLJ.trans hJI
  have hUL : ⁅UL153 T I L, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (UL153 T I L) L]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLC
  have hU : UL153 T I L = ⊥ := cex_commutator_eq_bot_of_perfect (perfect_of_mem_cComp c25.conc.1) hUL
  obtain ⟨q, -, -, -, hcard, -⟩ := cc.orthogonal
  rw [hU, Subgroup.card_bot] at hcard
  omega

end CFSG.Quasithin
