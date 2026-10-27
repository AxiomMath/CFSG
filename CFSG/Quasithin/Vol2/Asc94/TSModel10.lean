module

public import CFSG.Quasithin.Vol2.Asc94.TSModel8
public import CFSG.Quasithin.Vol2.Asc94.TSModel7

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

abbrev SBs (i j : Fin 5) : Prop := (i = 0 ∧ (j = 3 ∨ j = 4)) ∨ (i = 1 ∧ j = 4)

theorem hSBs : ∀ i k j, SBs i k → SBs k j → False := by decide

theorem lt_SBs : ∀ i j, SBs i j → i < j := by decide

@[expose] def Bs : Subgroup Hc := patSub SBs hSBs

theorem card_Bs : Nat.card Bs = 2 ^ 3 := by
  have h := patSub_card hSBs lt_SBs
  rw [Nat.card_eq_fintype_card (α := {p : Fin 5 × Fin 5 // SBs p.1 p.2})] at h
  have h3 : Fintype.card {p : Fin 5 × Fin 5 // SBs p.1 p.2} = 3 := by decide
  rw [h3] at h
  exact h

theorem bs_aux1 : ∀ i j : Fin 5, ¬ SBs i j → ¬ SA i j ∨ ¬ SA2 i j ∨ ¬ S1 i j := by decide

theorem bs_aux2 : ∀ i j : Fin 5, ¬ SBs i j → ¬ SA i j ∨ ¬ SA2 i j ∨ ¬ S2 i j := by decide

theorem B_inf_U1_le_Bs : A1 ⊓ A2 ⊓ U1 ≤ Bs := by
  intro x hx
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  have h1 : SuppIn SA (cm x - 1) := (mem_patSub hSA).1 hx1
  have h2 : SuppIn SA2 (cm x - 1) := (mem_patSub hSA2).1 hx2
  have h3 : SuppIn S1 (cm x - 1) := (mem_patSub hS1).1 hx3
  refine (mem_patSub hSBs).2 fun i j hij => ?_
  rcases bs_aux1 i j hij with h | h | h
  · exact h1 i j h
  · exact h2 i j h
  · exact h3 i j h

theorem B_inf_U2_le_Bs : A1 ⊓ A2 ⊓ U2 ≤ Bs := by
  intro x hx
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  have h1 : SuppIn SA (cm x - 1) := (mem_patSub hSA).1 hx1
  have h2 : SuppIn SA2 (cm x - 1) := (mem_patSub hSA2).1 hx2
  have h3 : SuppIn S2 (cm x - 1) := (mem_patSub hS2).1 hx3
  refine (mem_patSub hSBs).2 fun i j hij => ?_
  rcases bs_aux2 i j hij with h | h | h
  · exact h1 i j h
  · exact h2 i j h
  · exact h3 i j h

theorem zt_mem_B_inf_U1 : zt ∈ A1 ⊓ A2 ⊓ U1 := ⟨⟨zt_mem_A1, zt_mem_A2⟩, zt_mem_U1⟩

theorem Gamma012_le_Bs {Γ : Fin 6 → Set Hc} (h0 : Γ 0 = {zt})
    (h1 : Γ 1 = ((A1 ⊓ A2 ⊓ U1 : Subgroup Hc) : Set Hc) \ {1, zt})
    (h2 : Γ 2 = ((A1 ⊓ A2 ⊓ U2 : Subgroup Hc) : Set Hc) \ {1, zt}) :
    ∀ i : Fin 6, i.val ≤ 2 → ∀ a ∈ Γ i, a ∈ Bs := by
  intro i hi a ha
  have hfin : ∀ i : Fin 6, i.val ≤ 2 → i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases hfin i hi with rfl | rfl | rfl
  · rw [h0] at ha
    rw [Set.mem_singleton_iff.1 ha]
    exact B_inf_U1_le_Bs zt_mem_B_inf_U1
  · rw [h1] at ha
    exact B_inf_U1_le_Bs ha.1
  · rw [h2] at ha
    exact B_inf_U2_le_Bs ha.1


theorem Delta_le_Qh {Δ : Fin 7 → Set Hc} (h0 : Δ 0 = {zt})
    (h1 : Δ 1 = ((A1 ⊓ U1 : Subgroup Hc) : Set Hc) \ {1, zt})
    (h2 : Δ 2 = ((A1 ⊓ U2 : Subgroup Hc) : Set Hc) \ {1, zt})
    (h3 : Δ 3 = {a | a ∈ A1 ∧ a ∈ Qh ∧ a ≠ 1 ∧ a ∉ U1 ∧ a ∉ U2}) :
    ∀ i : Fin 7, i.val ≤ 3 → ∀ a ∈ Δ i, a ∈ Qh := by
  intro i hi a ha
  have hfin : ∀ i : Fin 7, i.val ≤ 3 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases hfin i hi with rfl | rfl | rfl | rfl
  · rw [h0] at ha
    rw [Set.mem_singleton_iff.1 ha]
    exact U1_le_Qh zt_mem_U1
  · rw [h1] at ha
    exact U1_le_Qh (Subgroup.mem_inf.1 ha.1).2
  · rw [h2] at ha
    exact U2_le_Qh (Subgroup.mem_inf.1 ha.1).2
  · rw [h3] at ha
    exact ha.2.1

end CFSG.Quasithin.A94.L52
