module

public import CFSG.Quasithin.Recognition.CertU33Outer

public section

namespace CFSG.Quasithin

open CFSG.Sporadic.Bridge

namespace F6

@[expose] def g22gl (k : ℕ) : List ℕ := u33GenTab.getD k []

@[expose] def g22gil (k : ℕ) : List ℕ := u33GenInvTab.getD k []

@[expose] def g22id : List ℕ := List.range 28

@[expose] def g22ConjIn (ks : List ℕ) (L : List ℕ) (j : ℕ) : Bool :=
  ks.all (fun g => L.any (fun k => compL (compL (g22gl g) (u33XL j)) (g22gil g) == u33XL k) &&
    L.any (fun k => compL (compL (g22gil g) (u33XL j)) (g22gl g) == u33XL k)) &&
  L.any (fun k => compL (compL u33PiTab (u33XL j)) u33PiTab == u33XL k)

@[expose] def g22ZIdx : List ℕ := [0, 4, 12, 2, 3, 9, 19, 7, 8, 17, 26, 16, 1, 11, 22, 6]

@[expose] def g22z4Idx (g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) : ℕ :=
  ([[0, 4, 12, 2], [3, 9, 19, 7], [8, 17, 26, 16], [1, 11, 22, 6]].getD g.1.toAdd.val []).getD
    g.2.toAdd.val 0

theorem g22_z4_mul_chk : ∀ g h : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    compL (u33XL (g22z4Idx g)) (u33XL (g22z4Idx h)) = u33XL (g22z4Idx (g * h)) := by
  decide +kernel

theorem g22_z4_inj_chk : ∀ g h : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    g22z4Idx g = g22z4Idx h → g = h := by decide +kernel

theorem g22_z4_one_chk : g22z4Idx 1 = 0 := by decide +kernel

theorem g22_z4_mem_chk : ∀ g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    g22z4Idx g ∈ g22ZIdx := by decide +kernel

theorem g22_z4_surj_chk : ∀ i ∈ g22ZIdx, ∃ g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    g22z4Idx g = i := by decide +kernel

theorem g22_Z_lt_chk : ∀ i ∈ g22ZIdx, i < 64 := by decide +kernel

theorem g22_Z_norm_chk : ∀ j ∈ g22ZIdx, g22ConjIn [0, 1, 2, 3] g22ZIdx j = true := by
  decide +kernel

theorem g22_S_sq_chk : ∀ i < 64, ∃ k ∈ g22ZIdx, compL (u33XL i) (u33XL i) = u33XL k := by
  decide +kernel

@[expose] def g22R1Idx : List ℕ := [0, 1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 16, 17, 19, 22, 26, 32, 33,
  34, 35, 36, 38, 39, 40, 41, 43, 44, 48, 49, 51, 54, 58]

theorem g22_R1_mul_chk : ∀ i ∈ g22R1Idx, ∀ j ∈ g22R1Idx, ∃ k ∈ g22R1Idx,
    compL (u33XL i) (u33XL j) = u33XL k := by decide +kernel

theorem g22_R1_inv_chk : ∀ i ∈ g22R1Idx, ∃ k ∈ g22R1Idx, compL (u33XL i) (u33XL k) = g22id := by
  decide +kernel

theorem g22_R1_norm_chk : ∀ j ∈ g22R1Idx, g22ConjIn [0, 1, 2, 3] g22R1Idx j = true := by
  decide +kernel

theorem g22_R1_lt_chk : ∀ i ∈ g22R1Idx, i < 64 := by decide +kernel

theorem g22_R1_len_chk : g22R1Idx.length = 32 ∧ g22R1Idx.Nodup := by decide +kernel

theorem g22_R1_center_chk : (∀ j ∈ g22R1Idx, compL (u33XL 8) (u33XL j) = compL (u33XL j) (u33XL 8) ∧
    compL (u33XL 12) (u33XL j) = compL (u33XL j) (u33XL 12)) ∧ 8 ∈ g22R1Idx ∧ 12 ∈ g22R1Idx :=
  by decide +kernel

@[expose] def g22R2Idx : List ℕ := [0, 5, 6, 7, 8, 9, 11, 12, 18, 20, 21, 23, 24, 25, 26, 31, 32,
  37, 38, 39, 40, 41, 43, 44, 50, 52, 53, 55, 56, 57, 58, 63]

theorem g22_R2_mul_chk : ∀ i ∈ g22R2Idx, ∀ j ∈ g22R2Idx, ∃ k ∈ g22R2Idx,
    compL (u33XL i) (u33XL j) = u33XL k := by decide +kernel

theorem g22_R2_inv_chk : ∀ i ∈ g22R2Idx, ∃ k ∈ g22R2Idx, compL (u33XL i) (u33XL k) = g22id := by
  decide +kernel

theorem g22_R2_norm_chk : ∀ j ∈ g22R2Idx, g22ConjIn [0, 1, 2, 4] g22R2Idx j = true := by
  decide +kernel

theorem g22_R2_lt_chk : ∀ i ∈ g22R2Idx, i < 64 := by decide +kernel

theorem g22_R2_len_chk : g22R2Idx.length = 32 ∧ g22R2Idx.Nodup := by decide +kernel

@[expose] def g22qAIdx : QuaternionGroup 2 → ℕ
  | .a i => [0, 18, 26, 23].getD i.val 0
  | .xa i => [11, 20, 7, 25].getD i.val 0

@[expose] def g22qBIdx : QuaternionGroup 2 → ℕ
  | .a i => [0, 63, 26, 37].getD i.val 0
  | .xa i => [6, 57, 9, 52].getD i.val 0

theorem g22_qA_mul_chk : ∀ g h : QuaternionGroup 2,
    compL (u33XL (g22qAIdx g)) (u33XL (g22qAIdx h)) = u33XL (g22qAIdx (g * h)) := by
  decide +kernel

theorem g22_qB_mul_chk : ∀ g h : QuaternionGroup 2,
    compL (u33XL (g22qBIdx g)) (u33XL (g22qBIdx h)) = u33XL (g22qBIdx (g * h)) := by
  decide +kernel

theorem g22_qA_inj_chk : ∀ g h : QuaternionGroup 2, g22qAIdx g = g22qAIdx h → g = h := by
  decide +kernel

theorem g22_qB_inj_chk : ∀ g h : QuaternionGroup 2, g22qBIdx g = g22qBIdx h → g = h := by
  decide +kernel

theorem g22_q_one_chk : g22qAIdx 1 = 0 ∧ g22qBIdx 1 = 0 := by decide +kernel

theorem g22_q_mem_chk : ∀ g : QuaternionGroup 2, g22qAIdx g ∈ g22R2Idx ∧ g22qBIdx g ∈ g22R2Idx :=
  by decide +kernel

theorem g22_q_comm_chk : ∀ g h : QuaternionGroup 2,
    compL (u33XL (g22qAIdx g)) (u33XL (g22qBIdx h)) =
      compL (u33XL (g22qBIdx h)) (u33XL (g22qAIdx g)) := by decide +kernel

theorem g22_q_gen_chk : ∀ i ∈ g22R2Idx, ∃ g h : QuaternionGroup 2,
    compL (u33XL (g22qAIdx g)) (u33XL (g22qBIdx h)) = u33XL i := by decide +kernel

theorem g22_q_inf_chk : ∀ g h : QuaternionGroup 2, g22qAIdx g = g22qBIdx h →
    (g = 1 ∧ h = 1) ∨ (g = .a 2 ∧ h = .a 2) := by decide +kernel

@[expose] def g22rhoL : List ℕ := compL u33PiTab (g22gl 3)

@[expose] def g22rhoPowL : ℕ → List ℕ
  | 0 => g22id
  | m + 1 => compL (g22rhoPowL m) g22rhoL

theorem g22_sigma_sq_chk : ∃ k ∈ g22ZIdx, compL (g22gl 2) (g22gl 2) = u33XL k := by
  decide +kernel

theorem g22_sigma_rho_chk : ∃ k ∈ g22ZIdx,
    compL (compL (compL (g22gl 2) g22rhoL) (g22gil 2)) g22rhoL = u33XL k := by decide +kernel

theorem g22_rho_six_chk : ∃ k ∈ g22ZIdx, g22rhoPowL 6 = u33XL k := by decide +kernel

theorem g22_rho_two_chk : ∀ k ∈ g22ZIdx, g22rhoPowL 2 ≠ u33XL k := by decide +kernel

theorem g22_rho_three_chk : ∀ k ∈ g22ZIdx, g22rhoPowL 3 ≠ u33XL k := by decide +kernel

theorem g22_sigma_not_chk : ∀ m < 6, ∀ k ∈ g22ZIdx, compL (g22rhoPowL m) (u33XL k) ≠ g22gl 2 := by
  decide +kernel

end F6

end CFSG.Quasithin
