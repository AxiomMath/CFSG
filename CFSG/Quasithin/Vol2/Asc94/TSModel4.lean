module

public import CFSG.Quasithin.Vol2.Asc94.TSModel1

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S
open scoped Pointwise

private theorem suppIn_mul_eq_zero_two {S T : Fin 5 → Fin 5 → Prop}
    (hST : ∀ i k j, S i k → T k j → False) {A B : Mt} (hA : SuppIn S A) (hB : SuppIn T B) :
    A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : S i k
  · rw [hB k j (fun h' => hST i k j h h'), mul_zero]
  · rw [hA i k h, zero_mul]

private theorem hSA_S1 : ∀ i k j, SA i k → S1 k j → False := by
  intro i k j h1 h2
  have h := h1.2
  rw [h2.1] at h
  exact absurd h (by decide)

private theorem supp_of_mem_A1 {a : Hc} (ha : a ∈ A1) : SuppIn SA (cm a - 1) :=
  (mem_patSub hSA).1 ha

private theorem supp_of_mem_U1 {u : Hc} (hu : u ∈ U1) : SuppIn S1 (cm u - 1) :=
  (mem_patSub hS1).1 hu

private theorem A1_rows {a : Hc} (ha : a ∈ A1) :
    ∀ k : Fin 5, 2 ≤ k.val → ∀ j, (cm a - 1) k j = 0 :=
  fun k hk j => supp_of_mem_A1 ha k j (fun h => by have := h.1; omega)

private theorem fin5_SA_notS1 : ∀ i j : Fin 5, SA i j → ¬ S1 i j → i = 1 := by decide

private theorem fin5_row0_one : ∀ j : Fin 5, ¬ SA 0 j → j ≠ 0 → j = 1 := by decide

private theorem zmod2_eq_one_of_ne_zero : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

private theorem zmod2_mul_ne_zero : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by decide

private theorem cm_mul_A1_U1 {a u : Hc} (ha : a ∈ A1) (hu : u ∈ U1) :
    cm (a * u) = 1 + ((cm a - 1) + (cm u - 1)) := by
  have hNP := suppIn_mul_eq_zero_two hSA_S1 (supp_of_mem_A1 ha) (supp_of_mem_U1 hu)
  rw [cm_mul]
  have e : cm a * cm u = 1 + ((cm a - 1) + (cm u - 1)) + (cm a - 1) * (cm u - 1) := by
    noncomm_ring
  rw [e, hNP, add_zero]

private theorem invol_aux (N P : Mt) (hNN : N * N = 0) (hNP : N * P = 0) (hPP : P * P = 0)
    (h : (1 + (N + P)) * (1 + (N + P)) = 1) : P * N = 0 := by
  have e : (1 + (N + P)) * (1 + (N + P)) = 1 + P * N := by
    calc (1 + (N + P)) * (1 + (N + P))
        = 1 + ((N + P) + (N + P)) + (N * N + N * P + P * N + P * P) := by noncomm_ring
      _ = 1 + P * N := by
        rw [mat_add_self (N + P), hNN, hNP, hPP]
        abel
  rw [e] at h
  exact add_left_cancel (h.trans (add_zero (1 : Mt)).symm)

private theorem PN_eq_zero_of_sq {a u : Hc} (ha : a ∈ A1) (hu : u ∈ U1)
    (h : cm (a * u) * cm (a * u) = 1) : (cm u - 1) * (cm a - 1) = 0 := by
  rw [cm_mul_A1_U1 ha hu] at h
  exact invol_aux (cm a - 1) (cm u - 1)
    (suppIn_mul_eq_zero_two hSA (supp_of_mem_A1 ha) (supp_of_mem_A1 ha))
    (suppIn_mul_eq_zero_two hSA_S1 (supp_of_mem_A1 ha) (supp_of_mem_U1 hu))
    (suppIn_mul_eq_zero_two hS1 (supp_of_mem_U1 hu) (supp_of_mem_U1 hu)) h

private theorem entry_PN (P N : Mt) (hP00 : P 0 0 = 0)
    (hNr : ∀ k : Fin 5, 2 ≤ k.val → ∀ j, N k j = 0) (j : Fin 5) :
    (P * N) 0 j = P 0 1 * N 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_five, hP00, hNr 2 (by decide) j, hNr 3 (by decide) j,
    hNr 4 (by decide) j]
  simp

private theorem not_comm_aux (N P : Mt) (hN : SuppIn SA N) (hP : SuppIn S1 P)
    (hP00 : P 0 0 = 0) (hNP : N * P = 0) (hcomm : (1 + N) * (1 + P) = (1 + P) * (1 + N))
    (hN1 : ¬ SuppIn S1 N) (hP01 : P 0 1 ≠ 0) : False := by
  have hPN : P * N = 0 := by
    have e : P * N = (1 + P) * (1 + N) - (1 + N) * (1 + P) + N * P := by noncomm_ring
    rw [e, hcomm, sub_self, zero_add, hNP]
  have hNr : ∀ k : Fin 5, 2 ≤ k.val → ∀ j, N k j = 0 :=
    fun k hk j => hN k j (fun h => by have := h.1; omega)
  obtain ⟨i, j, hij, hNij⟩ : ∃ i j, ¬ S1 i j ∧ N i j ≠ 0 := by
    by_contra hcon
    exact hN1 (fun i j h => by
      by_contra hne
      exact hcon ⟨i, j, h, hne⟩)
  have hSAij : SA i j := by
    by_contra h
    exact hNij (hN i j h)
  obtain rfl : i = 1 := fin5_SA_notS1 i j hSAij hij
  have h0 : (P * N) 0 j = 0 := by rw [hPN, Matrix.zero_apply]
  rw [entry_PN P N hP00 hNr j] at h0
  exact zmod2_mul_ne_zero _ _ hP01 hNij h0

private theorem not_comm_A1_U1 {x y : Hc} (hx : x ∈ A1) (hy : y ∈ U1) (hxU : x ∉ U1)
    (hyA : y ∉ A1) : x * y ≠ y * x := by
  intro hxy
  have hcomm : (1 + (cm x - 1)) * (1 + (cm y - 1)) = (1 + (cm y - 1)) * (1 + (cm x - 1)) := by
    have e := congrArg cm hxy
    rw [cm_mul, cm_mul] at e
    have ex : (1 : Mt) + (cm x - 1) = cm x := by abel
    have ey : (1 : Mt) + (cm y - 1) = cm y := by abel
    rw [ex, ey]
    exact e
  have hP01 : (cm y - 1) 0 1 ≠ 0 := by
    intro h0
    apply hyA
    refine (mem_patSub hSA).2 fun i j hij => ?_
    by_cases hS : S1 i j
    · obtain ⟨rfl, hj⟩ := hS
      rw [fin5_row0_one j hij hj]
      exact h0
    · exact supp_of_mem_U1 hy i j hS
  have hN1 : ¬ SuppIn S1 (cm x - 1) := fun h => hxU ((mem_patSub hS1).2 h)
  have hP00 : (cm y - 1) 0 0 = 0 := by simp [cm_00]
  exact not_comm_aux (cm x - 1) (cm y - 1) (supp_of_mem_A1 hx) (supp_of_mem_U1 hy) hP00
    (suppIn_mul_eq_zero_two hSA_S1 (supp_of_mem_A1 hx) (supp_of_mem_U1 hy)) hcomm hN1 hP01

private theorem inv_mem_A1_or_U1 {x : Hc} (hx : x ∈ (A1 : Set Hc) * (U1 : Set Hc))
    (hx2 : x * x = 1) : x ∈ A1 ∨ x ∈ U1 := by
  obtain ⟨a, ha, u, hu, rfl⟩ := Set.mem_mul.1 hx
  have hsq : cm (a * u) * cm (a * u) = 1 := by
    have h := congrArg cm hx2
    rwa [cm_mul, cm_one] at h
  have hPN := PN_eq_zero_of_sq ha hu hsq
  by_cases hu01 : cm u 0 1 = 0
  · left
    have huA : u ∈ A1 := by
      refine (mem_patSub hSA).2 fun i j hij => ?_
      by_cases hS : S1 i j
      · obtain ⟨rfl, hj⟩ := hS
        rw [fin5_row0_one j hij hj, Matrix.sub_apply,
          Matrix.one_apply_ne (show (0 : Fin 5) ≠ 1 by decide)]
        exact (sub_zero _).trans hu01
      · exact supp_of_mem_U1 hu i j hS
    exact A1.mul_mem ha huA
  · right
    have hu1 : cm u 0 1 = 1 := zmod2_eq_one_of_ne_zero _ hu01
    have hP00 : (cm u - 1) 0 0 = 0 := by simp [cm_00]
    have hP01 : (cm u - 1) 0 1 = 1 := by
      rw [Matrix.sub_apply, Matrix.one_apply_ne (show (0 : Fin 5) ≠ 1 by decide)]
      exact (sub_zero _).trans hu1
    have haU : a ∈ U1 := by
      refine (mem_patSub hS1).2 fun i j hij => ?_
      by_cases hSA' : SA i j
      · obtain rfl := fin5_SA_notS1 i j hSA' hij
        have h0 : ((cm u - 1) * (cm a - 1)) 0 j = 0 := by rw [hPN, Matrix.zero_apply]
        rw [entry_PN (cm u - 1) (cm a - 1) hP00 (A1_rows ha) j, hP01, one_mul] at h0
        exact h0
      · exact supp_of_mem_A1 ha i j hSA'
    exact U1.mul_mem haU hu

theorem A1U1_pair {x y : Hc} (hx : x ∈ (A1 : Set Hc) * (U1 : Set Hc))
    (hy : y ∈ (A1 : Set Hc) * (U1 : Set Hc)) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hxy : x * y = y * x) : (x ∈ A1 ∧ y ∈ A1) ∨ (x ∈ U1 ∧ y ∈ U1) := by
  rcases inv_mem_A1_or_U1 hx hx2 with hxA | hxU <;>
    rcases inv_mem_A1_or_U1 hy hy2 with hyA | hyU
  · exact Or.inl ⟨hxA, hyA⟩
  · by_cases hxU' : x ∈ U1
    · exact Or.inr ⟨hxU', hyU⟩
    · by_cases hyA' : y ∈ A1
      · exact Or.inl ⟨hxA, hyA'⟩
      · exact absurd hxy (not_comm_A1_U1 hxA hyU hxU' hyA')
  · by_cases hyU' : y ∈ U1
    · exact Or.inr ⟨hxU, hyU'⟩
    · by_cases hxA' : x ∈ A1
      · exact Or.inl ⟨hxA', hyA⟩
      · exact absurd hxy.symm (not_comm_A1_U1 hyA hxU hyU' hxA')
  · exact Or.inr ⟨hxU, hyU⟩

theorem elemAbelian_le_A1_or_U1 {E : Subgroup Hc} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hEC : E ≤ Subgroup.centralizer ((A1 ⊓ U1 : Subgroup Hc) : Set Hc)) : E ≤ A1 ∨ E ≤ U1 := by
  by_contra hcon
  have hA : ¬ E ≤ A1 := fun h => hcon (Or.inl h)
  have hU : ¬ E ≤ U1 := fun h => hcon (Or.inr h)
  obtain ⟨x, hxE, hxA⟩ := SetLike.not_le_iff_exists.1 hA
  obtain ⟨y, hyE, hyU⟩ := SetLike.not_le_iff_exists.1 hU
  have hxB : x ∈ (A1 : Set Hc) * (U1 : Set Hc) := by
    rw [← centralizer_B_eq]
    exact hEC hxE
  have hyB : y ∈ (A1 : Set Hc) * (U1 : Set Hc) := by
    rw [← centralizer_B_eq]
    exact hEC hyE
  have hx2 : x * x = 1 := by
    rw [← sq]
    exact hE.2 x hxE
  have hy2 : y * y = 1 := by
    rw [← sq]
    exact hE.2 y hyE
  have hxy : x * y = y * x := comm_of_isElemAbelian hE hxE hyE
  rcases A1U1_pair hxB hyB hx2 hy2 hxy with ⟨hxA', _⟩ | ⟨_, hyU'⟩
  · exact hxA hxA'
  · exact hyU hyU'

end CFSG.Quasithin.A94.L52
