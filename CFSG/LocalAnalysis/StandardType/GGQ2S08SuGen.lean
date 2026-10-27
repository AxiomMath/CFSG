module

public import CFSG.ClassicalGroups.Unitary.Generation
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

private theorem ggQ2s08r3_mem_stab_e0_of_smul {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}
    {g : SUid σ (n + 1)} {c : K}
    {b : Fin (n + 1) → K} (h : ∀ v, g • v = v + (c * herm σ b v) • b) (hb : b 0 = 0) :
    g ∈ MulAction.stabilizer (SUid σ (n + 1)) (e0 K n) := by
  rw [MulAction.mem_stabilizer_iff, h]
  have hz : herm σ b (e0 K n) = 0 := by
    rw [herm_single_right, hb, map_zero, mul_one]
  rw [hz, mul_zero, zero_smul, add_zero]

private theorem ggQ2s08r3_mem_stab_last_of_smul {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}
    {g : SUid σ (n + 1)} {c : K}
    {b : Fin (n + 1) → K} (h : ∀ v, g • v = v + (c * herm σ b v) • b)
    (hb : b (Fin.last n) = 0) :
    g ∈ MulAction.stabilizer (SUid σ (n + 1))
      (Pi.single (Fin.last n) (1 : K) : Fin (n + 1) → K) := by
  rw [MulAction.mem_stabilizer_iff, h]
  have hz : herm σ b (Pi.single (Fin.last n) (1 : K)) = 0 := by
    rw [herm_single_right, hb, map_zero, mul_one]
  rw [hz, mul_zero, zero_smul, add_zero]

private theorem ggQ2s08r3_exists_stab_smul_last_eq_zero {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 4 ≤ n) {a : Fin (n + 1) → K}
    (ha : herm σ a a = 0) (ha0 : a 0 ≠ 0) :
    ∃ h ∈ MulAction.stabilizer (SUid σ (n + 1)) (e0 K n), (h • a) (Fin.last n) = 0 := by
  set w : Fin n → K := Pi.single (⟨0, by omega⟩ : Fin n) 1 with hw
  set a' : Fin (n + 1) → K := consL n (Fin.tail a) with ha'def
  have ha'_zero : a' 0 = 0 := by
    rw [ha'def, consL_apply, Fin.cons_zero]
  have ha_split : a = a 0 • e0 K n + a' := by
    rw [ha'def]
    exact eq_smul_single_add_consL a
  have hcross1 : herm σ (a 0 • e0 K n) a' = 0 := by
    rw [herm_smul_left, herm_single_left, ha'_zero, mul_zero, mul_zero]
  have hcross2 : herm σ a' (a 0 • e0 K n) = 0 := by
    rw [herm_smul_right, herm_single_right, ha'_zero, map_zero, mul_one, mul_zero]
  have hself : herm σ (a 0 • e0 K n) (a 0 • e0 K n) = σ (a 0) * a 0 := by
    rw [herm_smul_left, herm_smul_right, herm_e0_e0, mul_one]
  have hsum : σ (a 0) * a 0 + herm σ a' a' = 0 := by
    have h := ha
    rw [ha_split] at h
    simp only [herm_add_left, herm_add_right, hself, hcross1, hcross2] at h
    simpa using h
  have hherm_a' : herm σ a' a' = -(σ (a 0) * a 0) := by
    linear_combination hsum
  have hσa0 : σ (a 0) ≠ 0 := (map_ne_zero σ).mpr ha0
  have hd0 : -(σ (a 0) * a 0) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hσa0 ha0)
  have hd : σ (-(σ (a 0) * a 0)) = -(σ (a 0) * a 0) := by
    rw [map_neg, hσ.norm_fixed]
  obtain ⟨s, hs⟩ := hσ.exists_norm hd
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hs
    exact hd0 hs.symm
  set y : Fin (n + 1) → K := s⁻¹ • a' with hy
  have hy0 : y 0 = 0 := by
    rw [hy, Pi.smul_apply, ha'_zero, smul_eq_mul, mul_zero]
  have hyy : herm σ y y = 1 := by
    have hσsne : σ s ≠ 0 := (map_ne_zero σ).mpr hs0
    rw [hy, herm_smul_left, herm_smul_right, hherm_a', ← hs]
    calc σ s⁻¹ * (s⁻¹ * (σ s * s))
        = (σ s)⁻¹ * s⁻¹ * (σ s * s) := by rw [map_inv₀]; ring
      _ = (σ s)⁻¹ * σ s * (s⁻¹ * s) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hσsne, inv_mul_cancel₀ hs0, mul_one]
  have hy_eq : y = consL n (Fin.tail y) := by
    nth_rewrite 1 [eq_smul_single_add_consL y]
    rw [hy0, zero_smul, zero_add]
  have htail : herm σ (Fin.tail y) (Fin.tail y) = 1 := by
    rw [← herm_consL (Fin.tail y) (Fin.tail y), ← hy_eq]
    exact hyy
  have hsingle : herm σ w w = 1 := by
    rw [hw, herm_single_left, map_one, one_mul, Pi.single_eq_same]
  obtain ⟨t₀, ht₀T, ht₀⟩ :=
    exists_mem_T_smul_eq_of_norm_one hσ (Or.inl (by omega : 4 ≤ n)) htail hsingle
  obtain ⟨h, -, hφ, hfix⟩ :=
    transport hσ.invol (consL n) (fun u v => herm_consL u v) ht₀T
  have hhe0 : h • (e0 K n) = e0 K n :=
    hfix (e0 K n) (fun u => herm_consL_single_zero u)
  have hhP : h ∈ MulAction.stabilizer (SUid σ (n + 1)) (e0 K n) := by
    rw [MulAction.mem_stabilizer_iff]
    exact hhe0
  have ha'eq : a' = s • y := by
    rw [hy, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  have hha : h • a = a 0 • e0 K n + s • (consL n w) := by
    nth_rewrite 1 [ha_split]
    rw [ha'eq, smul_add, smul_comm h (a 0) (e0 K n), smul_comm h s y, hhe0, hy_eq,
      hφ (Fin.tail y), ht₀]
  have hlast : (h • a) (Fin.last n) = 0 := by
    rw [hha]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : (e0 K n) (Fin.last n) = 0 := by
      have hne : (Fin.last n : Fin (n + 1)) ≠ 0 := by
        intro hcon
        have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hcon
        simp only [Fin.val_last, Fin.val_zero] at this
        omega
      exact Pi.single_eq_of_ne hne 1
    have h2 : (consL n w) (Fin.last n) = 0 := by
      rw [hw]
      have hlast_eq : (Fin.last n : Fin (n + 1)) = Fin.succ (⟨n - 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        simp only [Fin.val_last, Fin.val_succ]
        omega
      rw [hlast_eq, consL_apply, Fin.cons_succ]
      have hne : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by
        intro hcon
        have := congrArg (fun x : Fin n => (x : ℕ)) hcon
        simp only [Fin.val_zero] at this
        omega
      exact Pi.single_eq_of_ne hne 1
    rw [h1, h2, mul_zero, mul_zero, add_zero]
  exact ⟨h, hhP, hlast⟩

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary in
theorem ggQ2s08_su_stab_generate {K : Type*} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 4 ≤ n) :
    MulAction.stabilizer (SUid σ (n + 1)) (e0 K n) ⊔
      MulAction.stabilizer (SUid σ (n + 1)) (Pi.single (Fin.last n) (1 : K) : Fin (n + 1) → K) = ⊤ := by
  set P := MulAction.stabilizer (SUid σ (n + 1)) (e0 K n) with hP
  set Q := MulAction.stabilizer (SUid σ (n + 1))
    (Pi.single (Fin.last n) (1 : K) : Fin (n + 1) → K) with hQ
  have hT : T σ (n + 1) = ⊤ := T_eq_top hσ (by omega) (fun h3 => absurd h3 (by omega))
  apply top_le_iff.mp
  rw [← hT]
  rw [T, Subgroup.closure_le]
  intro t ht
  obtain ⟨a, c, ha, hc, hact⟩ := ht
  by_cases ha0 : a 0 = 0
  · exact Subgroup.mem_sup_left (ggQ2s08r3_mem_stab_e0_of_smul hact ha0)
  · by_cases halast : a (Fin.last n) = 0
    · exact Subgroup.mem_sup_right (ggQ2s08r3_mem_stab_last_of_smul hact halast)
    · obtain ⟨h, hhP, hhlast⟩ := ggQ2s08r3_exists_stab_smul_last_eq_zero hσ hn ha ha0
      have hconj : h * t * h⁻¹ ∈ Q :=
        ggQ2s08r3_mem_stab_last_of_smul (conj_smul_of_tv h t hact) hhlast
      have hmem : h⁻¹ * (h * t * h⁻¹) * h ∈ P ⊔ Q :=
        (P ⊔ Q).mul_mem
          ((P ⊔ Q).mul_mem ((P ⊔ Q).inv_mem (Subgroup.mem_sup_left hhP))
            (Subgroup.mem_sup_right hconj))
          (Subgroup.mem_sup_left hhP)
      have heq : h⁻¹ * (h * t * h⁻¹) * h = t := by group
      rw [heq] at hmem
      exact hmem

end CFSG.StandardType

end
