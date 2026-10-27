module

public import CFSG.Quasithin.Vol2.Asc94.TSModel3
public import CFSG.Quasithin.Vol2.Asc94.TSModel1

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

theorem hSAQ : ∀ i k j, (SA i k ∧ SQ i k) → (SA k j ∧ SQ k j) → False :=
  fun i k j a b => hSA i k j a.1 b.1

theorem lt_SAQ : ∀ i j, (SA i j ∧ SQ i j) → i < j := fun i j h => lt_SA i j h.1

theorem A1_inf_Qh_eq : A1 ⊓ Qh = patSub (fun i j => SA i j ∧ SQ i j) hSAQ := by
  ext x
  simp only [Subgroup.mem_inf, mem_patSub, mem_Qh_iff]
  constructor
  · rintro ⟨hx1, hx2⟩ i j hij
    by_cases h : SA i j
    · exact hx2 i j (fun h2 => hij ⟨h, h2⟩)
    · exact hx1 i j h
  · intro hx
    exact ⟨fun i j hij => hx i j (fun h => hij h.1), fun i j hij => hx i j (fun h => hij h.2)⟩

theorem card_A1_inf_Qh : Nat.card ↥(A1 ⊓ Qh) = 2 ^ 4 := by
  rw [A1_inf_Qh_eq]
  have h := patSub_card hSAQ lt_SAQ
  rw [Nat.card_eq_fintype_card (α := {p : Fin 5 × Fin 5 // SA p.1 p.2 ∧ SQ p.1 p.2})] at h
  have h4 : Fintype.card {p : Fin 5 × Fin 5 // SA p.1 p.2 ∧ SQ p.1 p.2} = 4 := by decide
  rw [h4] at h
  exact h

@[expose] def d1 : Hc := mkH !![1, 0, 1, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def d2 : Hc := mkH !![1, 0, 1, 0, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def TQA : Set Hc := {a | a ∈ A1 ∧ a ∈ Qh ∧ a ≠ 1 ∧ a ∉ U1 ∧ a ∉ U2}

theorem d1_mem : d1 ∈ TQA := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_patSub hSA).2 (suppIn_iff_pairs.2 (by decide +kernel))
  · exact (mem_Qh_iff d1).2 (suppIn_iff_pairs.2 (by decide +kernel))
  · intro h
    have h' := congrArg cm h
    rw [cm_one] at h'
    exact absurd h' (by decide +kernel)
  · intro h
    have h' := (mem_patSub hS1).1 h
    exact absurd (h' 1 4 (by decide)) (by decide +kernel)
  · intro h
    have h' := (mem_patSub hS2).1 h
    exact absurd (h' 0 2 (by decide)) (by decide +kernel)

theorem d2_mem : d2 ∈ TQA := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_patSub hSA).2 (suppIn_iff_pairs.2 (by decide +kernel))
  · exact (mem_Qh_iff d2).2 (suppIn_iff_pairs.2 (by decide +kernel))
  · intro h
    have h' := congrArg cm h
    rw [cm_one] at h'
    exact absurd h' (by decide +kernel)
  · intro h
    have h' := (mem_patSub hS1).1 h
    exact absurd (h' 1 4 (by decide)) (by decide +kernel)
  · intro h
    have h' := (mem_patSub hS2).1 h
    exact absurd (h' 0 2 (by decide)) (by decide +kernel)

theorem d1_mul_d2 : d1 * d2 = zt :=
  cm_injective (by rw [cm_mul, cm_zt]; decide +kernel)

theorem zt_mem_closure_TQA : zt ∈ Subgroup.closure TQA := by
  rw [← d1_mul_d2]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure d1_mem) (Subgroup.subset_closure d2_mem)

end CFSG.Quasithin.A94.L52
