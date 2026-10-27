module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Lit
public import CFSG.Quasithin.Recognition.CertOvergroup

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

@[expose] def sT (i : Fin 45) : P45 :=
  wordP (wpW.getD i []) * x45 * (wordP (wpW.getD i []))⁻¹

theorem repL_sT (i : Fin 45) : RepL (tpL i) (sT i) := by
  have h1 := repL_wordP (wpW.getD i [])
  have h2 : RepL (evalW (invW (wpW.getD i []))) (wordP (wpW.getD i []))⁻¹ := by
    rw [← wordP_invW]
    exact repL_wordP _
  exact repL_mul (repL_mul h1 repL_x) h2

theorem sT_mem (i : Fin 45) : sT i ∈ Xs :=
  Xs.mul_mem (Xs.mul_mem (wordP_mem _) x45_mem) (Xs.inv_mem (wordP_mem _))

theorem chkTau_spec : chkTau = true :=
  Certificates.certificate4161.1

theorem chkTau_pts : ∀ j : Fin 45, applyW (wpW.getD j []) 0 = j := by
  intro j
  have h := chkTau_spec
  simp only [chkTau, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.1.1 j j.2

theorem sT_zero : sT 0 = x45 := by
  have h : wpW.getD ((0 : Fin 45) : ℕ) [] = [] := by decide
  simp only [sT, h]
  simp [wordP]

theorem point_move (j : Fin 45) : (wordP (wpW.getD j [])) 0 = j := by
  apply Fin.ext
  rw [applyW_eq]
  exact chkTau_pts j

theorem gen_conj (k : ℕ) (i : Fin 45) :
    gP k * sT i * (gP k)⁻¹ = sT (gP k i) := by
  have h := chkTau_spec
  simp only [chkTau, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hk : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h2 := h.1.2 i i.2 (k % 3) hk
  have hgi : ((gP k) i : ℕ) = (genL k).getD i 0 := ((repL_gP k).2 i).symm
  have hlt : (genL k).getD i 0 < 45 := by rw [← hgi]; exact ((gP k) i).2
  have h3 : comp (comp (genL k) (tpL i)) (genL (invLet k)) = tpL ((gP k) i) := by
    have e1 : genL (k % 3) = genL k := by simp [genL]
    have e2 : invLet (k % 3) = invLet k := by simp [invLet]
    rw [e1, e2, tpTab_getD _ i.2] at h2
    rw [h2, hgi, tpTab_getD _ hlt]
  refine eq_of_repL (l := comp (comp (genL k) (tpL i)) (genL (invLet k))) ?_ ?_
  · refine repL_mul (repL_mul (repL_gP k) (repL_sT i)) ?_
    rw [← gP_invLet]
    exact repL_gP _
  · rw [h3]
    exact repL_sT _

theorem tau_conj {g : P45} (hg : g ∈ Xs) (i : Fin 45) :
    g * sT i * g⁻¹ = sT (g i) := by
  have key : ((Xs : Subgroup P45) : Set P45) ⊆
      {g : P45 | ∀ i : Fin 45, g * sT i * g⁻¹ = sT (g i)} := by
    refine closure_subset_of_right_closed (S := ({x45, y45} : Set P45)) ?_ ?_ ?_
    · intro s _
      obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
      exact ⟨n, hn, h⟩
    · intro i
      simp
    · intro p hp s hs i
      have hs' : ∃ k, k < 2 ∧ s = gP k := by
        rcases hs with rfl | rfl
        · exact ⟨0, by norm_num, by simp [gP]⟩
        · exact ⟨1, by norm_num, by simp [gP]⟩
      obtain ⟨k, -, rfl⟩ := hs'
      have h1 := hp (gP k i)
      have h2 := gen_conj k i
      calc p * gP k * sT i * (p * gP k)⁻¹ = p * (gP k * sT i * (gP k)⁻¹) * p⁻¹ := by group
        _ = p * sT (gP k i) * p⁻¹ := by rw [h2]
        _ = sT (p (gP k i)) := h1
        _ = sT ((p * gP k) i) := rfl
  exact key hg i

theorem sT_injective : Function.Injective sT := by
  intro i j hij
  by_contra hne
  have h := chkTau_spec
  simp only [chkTau, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h2 := h.2 i i.2 j j.2
  have hij' : (i : ℕ) ≠ j := fun e => hne (Fin.ext e)
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h2
  rcases h2 with h2 | h2
  · exact hij' h2
  · apply h2
    rw [tpTab_getD _ i.2, tpTab_getD _ j.2]
    exact repL_unique (repL_sT i) (hij ▸ repL_sT j)

theorem mem_centralizer_x_iff {g : P45} (hg : g ∈ Xs) :
    g * x45 = x45 * g ↔ g 0 = 0 := by
  have h := tau_conj hg 0
  rw [sT_zero] at h
  constructor
  · intro hc
    have : sT (g 0) = sT 0 := by
      rw [← h, sT_zero, hc]
      group
    exact sT_injective this
  · intro h0
    rw [h0, sT_zero] at h
    calc g * x45 = g * x45 * g⁻¹ * g := by group
      _ = x45 * g := by rw [h]

end CFSG.Quasithin.H13.F431.U42
