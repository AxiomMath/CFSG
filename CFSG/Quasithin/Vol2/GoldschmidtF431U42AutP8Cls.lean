module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

@[expose] def conjWL (vL : PL) (w : List ℕ) : PL := comp (comp (evalAL w) vL) (evalAL (invAL w))

theorem repL_conjW {v : Ah} {vL : PL} (hv : RepL vL (v : P45)) (w : List ℕ) :
    RepL (conjWL vL w) ((aW w * v * (aW w)⁻¹ : Ah) : P45) :=
  repL_mul (repL_mul (repL_aW w) hv) (repL_aW_inv w)

theorem card_inf_centralizer_of {H : Subgroup Ah} {v : Ah} (hv : v ∈ H) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({v} : Set Ah)) =
      Nat.card ↥(Subgroup.centralizer ({(⟨v, hv⟩ : ↥H)} : Set ↥H)) := by
  have e : (H ⊓ Subgroup.centralizer ({v} : Set Ah)).subgroupOf H =
      Subgroup.centralizer ({(⟨v, hv⟩ : ↥H)} : Set ↥H) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using h
    · intro h
      refine ⟨x.2, ?_⟩
      have h' := congrArg (fun y : ↥H => (y : Ah)) h
      simpa only [Subgroup.coe_mul] using h'
  rw [← e]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem card_cent_of_class {H : Subgroup Ah} {Γ : Set Ah} (hΓ : Subgroup.closure Γ = H)
    {v : Ah} {vL : PL} (hvL : RepL vL (v : P45)) (hv : v ∈ H) (ws : List (List ℕ)) (gl : List PL)
    (hgl : ∀ s ∈ Γ, ∃ sL ∈ gl, RepL sL (s : P45)) (hws : ∀ w ∈ ws, aW w ∈ H)
    (hnd : (ws.map (conjWL vL)).Nodup) (hid : ([] : List ℕ) ∈ ws) (hnil : conjWL vL [] = vL)
    (hcl : ∀ w ∈ ws, ∀ s ∈ gl, ∃ w' ∈ ws, comp s (conjWL vL w) = comp (conjWL vL w') s) :
    Nat.card ↥(Subgroup.centralizer ({(⟨v, hv⟩ : ↥H)} : Set ↥H)) * ws.length =
      Nat.card ↥H := by
  have h := card_centralizer_mul_of_closed_class (Γ := Γ) hΓ hv
    (cl := ws.map fun w => aW w * v * (aW w)⁻¹) ?_ ?_ ?_ ?_
  · rwa [List.length_map] at h
  · refine List.Nodup.of_map (fun a : Ah => permL (a : P45)) ?_
    rw [List.map_map]
    have : ((fun a : Ah => permL (a : P45)) ∘ fun w => aW w * v * (aW w)⁻¹) = conjWL vL :=
      funext fun w => permL_eq_of_repL (repL_conjW hvL w)
    rw [this]
    exact hnd
  · intro c hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    exact ⟨aW w, hws w hw, rfl⟩
  · refine List.mem_map.2 ⟨[], hid, ?_⟩
    apply Subtype.ext
    apply eq_of_repL (repL_conjW hvL [])
    rw [hnil]
    exact hvL
  · intro c hc s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    obtain ⟨sL, hsL, hrep⟩ := hgl s hs
    obtain ⟨w', hw', hcomm⟩ := hcl w hw sL hsL
    refine List.mem_map.2 ⟨w', hw', ?_⟩
    have h1 : s * (aW w * v * (aW w)⁻¹) = (aW w' * v * (aW w')⁻¹) * s := by
      apply Subtype.ext
      apply eq_of_repL (l := comp sL (conjWL vL w))
      · exact repL_mul hrep (repL_conjW hvL w)
      · rw [hcomm]
        exact repL_mul (repL_conjW hvL w') hrep
    calc aW w' * v * (aW w')⁻¹ = (aW w' * v * (aW w')⁻¹ * s) * s⁻¹ := by group
      _ = s * (aW w * v * (aW w)⁻¹) * s⁻¹ := by rw [← h1]

@[expose] def clsDw : List (List ℕ) :=
  [[], [1, 0, 3, 2], [2, 0, 1, 3, 2], [1, 3, 2, 0, 1], [2, 2, 3, 1, 1], [2, 0, 2, 0, 1, 0, 1],
    [1, 0, 1, 3, 1, 3, 1], [2, 3, 2, 3, 2, 3, 2], [1, 0, 1, 0, 2, 3, 2], [2, 3, 1, 0, 2, 3, 1],
    [1, 3, 1, 3, 1, 3, 1], [1, 0, 2, 0, 2, 3, 1, 1], [2, 0, 2, 0, 1, 1, 0, 2],
    [1, 0, 2, 2, 0, 1, 0, 1], [2, 3, 2, 3, 2, 2, 0, 1], [3, 1, 0, 1, 0, 2, 3, 2],
    [1, 3, 2, 2, 0, 1, 0, 1], [1, 3, 1, 0, 2, 2, 0, 1]]

theorem clsD_check : (clsDw.map (conjWL dL)).Nodup ∧ ([] : List ℕ) ∈ clsDw ∧ conjWL dL [] = dL ∧
    ∀ w ∈ clsDw, ∀ s ∈ genP1L, ∃ w' ∈ clsDw, comp s (conjWL dL w) = comp (conjWL dL w') s := by
  decide +kernel

theorem clsD_mem : ∀ w ∈ clsDw, (evalAL w).getD 0 0 = 0 := by decide +kernel

theorem clsD_length : clsDw.length = 18 := by decide +kernel

theorem dA_mem_P1h : dA ∈ P1h :=
  Bh_le_P1h (Kl1h_le_Bh dA_mem_Kl1h)

theorem card_C1_d :
    Nat.card ↥(P1h ⊓ Subgroup.centralizer ({dA} : Set Ah)) = 64 := by
  rw [card_inf_centralizer_of dA_mem_P1h]
  have hgl : ∀ s ∈ gensP1, ∃ sL ∈ genP1L, RepL sL (s : P45) := by
    intro s hs
    rw [gensP1] at hs
    rcases hs with ⟨k, rfl⟩ | rfl | rfl | rfl
    · exact ⟨gTL k, List.mem_append.2 (Or.inl (List.mem_map.2 ⟨k, List.mem_range.2 k.2, rfl⟩)),
        repL_gTA k⟩
    · exact ⟨fhatL, by simp [genP1L], repL_fhat⟩
    · exact ⟨c3L, by simp [genP1L], U42.repL_c3⟩
    · exact ⟨DL 1, by simp [genP1L], U42.repL_Dj 1⟩
  have h := card_cent_of_class closure_gensP1 repL_dA dA_mem_P1h clsDw genP1L hgl
    (fun w hw => mem_P1h_of_repL (repL_aW w) (clsD_mem w hw)) clsD_check.1 clsD_check.2.1
    clsD_check.2.2.1 clsD_check.2.2.2
  rw [clsD_length, card_P1h] at h
  omega

end CFSG.Quasithin.H13.F431.U42Aut
