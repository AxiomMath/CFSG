module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bTab
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Tr
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Good

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 L0S image_lineSet lineSet_eq_of_sameSet repL_x)

noncomputable def t0A : Ah :=
  Classical.choose (exists_That_of_mem_Thl t0L_mem)

theorem t0A_mem_That : t0A ∈ That :=
  (Classical.choose_spec (exists_That_of_mem_Thl t0L_mem)).1

theorem repL_t0A : RepL (Tl.getD 20 []) (t0A : P45) :=
  (Classical.choose_spec (exists_That_of_mem_Thl t0L_mem)).2

@[expose] noncomputable def repA (j : ℕ) : Ah :=
  if j = 0 then xA else if j = 1 then t0A else if j = 2 then fhatA else e0A

theorem repL_repA {j : ℕ} (hj : j < 4) :
    RepL (invRep.getD j []) (repA j : P45) := by
  have hx : RepL xL (xA : P45) := repL_x
  have h6 : Tl.getD 6 [] = xL := invRep_x
  interval_cases j
  · have e : repA 0 = xA := by simp [repA]
    rw [e]
    exact h6 ▸ hx
  · have e : repA 1 = t0A := by simp [repA]
    rw [e]
    exact repL_t0A
  · have e : repA 2 = fhatA := by simp [repA]
    rw [e]
    exact repL_fhat
  · have e : repA 3 = e0A := by simp [repA]
    rw [e]
    exact repL_e0A

theorem inv_type {u : Ah} (hu : u ∈ That) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) :
    ∃ k < 43, RepL (invL k) (u : P45) ∧ ∃ g : Ah, (g ∈ P1h ∨ g ∈ P2h) ∧
      g * u * g⁻¹ = repA (invTgt.getD k 0) := by
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff u).1 hu
  have hl2 : comp l l = idL := repL_unique (repL_mul hrep hrep) (by
    have : (u : P45) * (u : P45) = 1 := congrArg Subtype.val hu2
    rw [this]
    exact repL_one 45)
  have hl1 : l ≠ idL := fun h => hu1 (Subtype.ext (eq_of_repL hrep (h ▸ repL_one 45)))
  obtain ⟨k, hk, rfl⟩ := inv_check.2.1 l hl hl2 hl1
  refine ⟨k, hk, hrep, ?_⟩
  obtain ⟨-, -, hconj, hP⟩ := inv_check.1 k hk
  set w := invW.getD k [] with hw
  have hg : RepL (evalAL w) ((wordAP w : P45)) := repL_wordAP w
  have hinvrep : RepL (evalAL (invAL w)) ((wordAP w : P45)⁻¹) := by
    rw [← wordAP_invAL]
    exact repL_wordAP _
  have h1 : RepL (comp (comp (evalAL w) (invL k)) (evalAL (invAL w)))
      ((wordAP w : P45) * (u : P45) * (wordAP w : P45)⁻¹) :=
    repL_mul (repL_mul hg hrep) hinvrep
  rw [hconj] at h1
  refine ⟨⟨wordAP w, wordAP_mem w⟩, ?_, ?_⟩
  · rcases hP with h | h
    · left
      rw [mem_P1h_iff]
      apply Fin.ext
      rw [← hg.2 0]
      exact h
    · right
      rw [mem_P2h_iff]
      show (wordAP w) '' L0S = L0S
      rw [L0S, image_lineSet hg (by decide), lineSet_eq_of_sameSet h]
  · apply Subtype.ext
    exact eq_of_repL h1 (repL_repA (inv_check.2.2 k hk))

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

theorem AutIso.isConj_toG (iso : AutIso M₁ M₂) {u v : Bh} {g : Ah} (hg : g ∈ P1h ∨ g ∈ P2h)
    (h : g * (u : Ah) * g⁻¹ = (v : Ah)) : IsConj (iso.toG u) (iso.toG v) := by
  rcases hg with hg | hg
  · refine isConj_iff.2 ⟨iso.toG1 ⟨g, hg⟩, ?_⟩
    have e : (⟨g, hg⟩ : ↥P1h) * Subgroup.inclusion Bh_le_P1h u * (⟨g, hg⟩ : ↥P1h)⁻¹ =
        Subgroup.inclusion Bh_le_P1h v := Subtype.ext h
    have := congrArg iso.toG1 e
    simpa only [map_mul, map_inv, AutIso.toG1_inclusion] using this
  · refine isConj_iff.2 ⟨iso.toG2 ⟨g, hg⟩, ?_⟩
    have e : (⟨g, hg⟩ : ↥P2h) * Subgroup.inclusion Bh_le_P2h u * (⟨g, hg⟩ : ↥P2h)⁻¹ =
        Subgroup.inclusion Bh_le_P2h v := Subtype.ext h
    have := congrArg iso.toG2 e
    simpa only [map_mul, map_inv, AutIso.toG2_inclusion] using this

end CFSG.Quasithin.H13.F431.U42Aut
