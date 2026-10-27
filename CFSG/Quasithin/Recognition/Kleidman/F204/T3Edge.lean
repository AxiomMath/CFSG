module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalFixed
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPath

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Edge

variable (F : Frame L1 L2 S D X)
include F

theorem exists_three_ball {β : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hβ : vtype β = false) :
    ∃ t : G, t ≠ 1 ∧ t ^ 3 = 1 ∧ ∀ ε, dist β ε ≤ 1 → t ∈ stab ε := by
  obtain ⟨E, hEβ, hE3, -, hball⟩ := ballStab_one_false F hβ
  have hE1 : E ≠ ⊥ := by
    intro h
    rw [h] at hE3
    simp at hE3
  obtain ⟨⟨t, htE⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht3 : t ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥E) (x := ⟨t, htE⟩)
    rw [hE3] at this
    simpa using congrArg Subtype.val this
  refine ⟨t, ht1', ht3, fun ε hε => ?_⟩
  have : t ∈ ballStab 1 β := by
    rw [hball]; exact Subgroup.mem_sup_right htE
  exact mem_ballStab.mp this ε hε

theorem exists_three_two {α β β' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = true)
    (hβ : β ∈ nbrs α) (hβ' : β' ∈ nbrs α) :
    ∃ r : G, r ∈ stab α ∧ r ∈ stab β ∧ r ∈ stab β' ∧ r ^ 3 = 1 ∧ r ≠ 1 := by
  have hA := Amal.of_frame F
  have hβf : vtype β = false := by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj α β from hβ)
    rw [hα] at this
    simpa using this.symm
  obtain ⟨t, ht1, ht3, htb⟩ := exists_three_ball F hβf
  have htα : t ∈ stab α := htb α ((dist_le_one_iff rfl).mpr (Or.inr
    (show (graph _ _ _).Adj β α from mem_nbrs_symm hβ)))
  have htβ : t ∈ stab β := htb β ((dist_le_one_iff rfl).mpr (Or.inl rfl))
  have hcard := card_fixed_nbrs_three F hα htα ht3 ht1
  obtain ⟨β₂, hβ₂, hβ₂t, hβ₂ne⟩ : ∃ β₂, β₂ ∈ nbrs α ∧ t ∈ stab β₂ ∧ β₂ ≠ β := by
    obtain ⟨y, hy, -⟩ := (Nat.card_eq_two_iff' ⟨β, hβ, htβ⟩).mp hcard
    exact ⟨y.1, y.2.1, y.2.2, fun h => hy (Subtype.ext h)⟩
  by_cases hb2 : β' = β
  · subst hb2
    exact ⟨t, htα, htβ, htβ, ht3, ht1⟩
  obtain ⟨q, hq, hqβ₂⟩ := exists_Qv_smul_nbr F hα hβ hβ₂ hβ' hβ₂ne hb2
  have hqβ : (q : G) ∈ stab β := pCoreOf_le 2 (stab β) hq
  have hqα : (q : G) ∈ stab α := hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hβ) hq
  refine ⟨(q : G) * t * (q : G)⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact (stab α).mul_mem ((stab α).mul_mem hqα htα) ((stab α).inv_mem hqα)
  · exact (stab β).mul_mem ((stab β).mul_mem hqβ htβ) ((stab β).inv_mem hqβ)
  · have : (q : G) * t * (q : G)⁻¹ ∈ stab (q • β₂) := by
      rw [stab_smul, mem_conjSub]
      have e : (q : G)⁻¹ * ((q : G) * t * (q : G)⁻¹) * (q : G) = t := by group
      rw [e]; exact hβ₂t
    rwa [hqβ₂] at this
  · calc ((q : G) * t * (q : G)⁻¹) ^ 3 = (q : G) * t ^ 3 * (q : G)⁻¹ := by
          rw [conj_pow]
      _ = 1 := by rw [ht3]; group
  · intro h
    apply ht1
    have : t = (q : G)⁻¹ * ((q : G) * t * (q : G)⁻¹) * (q : G) := by group
    rw [this, h]; group

end Edge

end CFSG.Quasithin.Kleidman.F204
