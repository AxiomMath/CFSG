module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94M1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F93b

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem zMu_eq_z_muV (j : Fin 3) : S.zMu j = L.z (S.muV j) := rfl

theorem z_smul_eq_of_dist (F : FanTree Γ G) (h71c : Fan71c F L) {l v : V}
    (hl : valence Γ l = 5) (hlβ : Γ.dist S.beta l ≤ 3) (hv : Γ.dist S.beta v ≤ 1) :
    L.z l • v = v := by
  rw [h71c.z_smul_eq_iff hl]
  calc Γ.dist l v ≤ Γ.dist l S.beta + Γ.dist S.beta v := F.isTree.connected.dist_triangle
    _ ≤ 3 + 1 := by
        gcongr
        rw [SimpleGraph.dist_comm]
        exact hlβ
    _ = 4 := rfl

theorem z_muV_mem_edge (F : FanTree Γ G) (h71c : Fan71c F L) (i j : Fin 3) :
    S.zMu j ∈ MulAction.stabilizer G (S.alphaV i) ⊓ MulAction.stabilizer G S.beta := by
  have hl := S.valence_muV F j
  have hd : Γ.dist S.beta (S.muV j) ≤ 3 := (S.dist_beta_muV F h71c j).le
  refine ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩
  · exact S.z_smul_eq_of_dist F h71c hl hd (by rw [S.dist_beta_alphaV F])
  · exact S.z_smul_eq_of_dist F h71c hl hd (by rw [SimpleGraph.dist_self]; norm_num)

theorem z_alphaV_one_mem_edge (F : FanTree Γ G) (h71c : Fan71c F L) (i : Fin 3) :
    S.zNb 1 ∈ MulAction.stabilizer G (S.alphaV i) ⊓ MulAction.stabilizer G S.beta := by
  have hl := S.valence_alphaV F 1
  have hd : Γ.dist S.beta (S.alphaV 1) ≤ 3 := by rw [S.dist_beta_alphaV F]; norm_num
  refine ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩
  · exact S.z_smul_eq_of_dist F h71c hl hd (by rw [S.dist_beta_alphaV F])
  · exact S.z_smul_eq_of_dist F h71c hl hd (by rw [SimpleGraph.dist_self]; norm_num)

theorem ubs_mem_nbrStab (F : FanTree Γ G) (h71c : Fan71c F L) (i : Fin 3) :
    S.ubs ∈ nbrStab Γ G (S.alphaV i) := by
  obtain ⟨φ, hφ⟩ := S.exists_arm_char F i
  have hmem := S.z_muV_mem_edge F h71c i
  have hN := S.z_alphaV_one_mem_edge F h71c i
  have hU : S.ubs ∈ MulAction.stabilizer G (S.alphaV i) ⊓ MulAction.stabilizer G S.beta :=
    mul_mem (mul_mem (mul_mem (hmem 0) (hmem 1)) (hmem 2)) hN
  have hval : ∀ j : Fin 3, φ ⟨S.zMu j, hmem j⟩ = if j = i then 1 else -1 := by
    intro j
    by_cases hji : j = i
    · have h1 : (if j = i then (1 : (ZMod 5)ˣ) else -1) = 1 := by simp [hji]
      rw [h1]
      refine (hφ _).1 (mem_nbrStab.2 fun w hw => ?_)
      subst hji
      change L.z (S.muV j) • w = w
      rw [h71c.z_smul_eq_iff (S.valence_muV F j)]
      calc Γ.dist (S.muV j) w ≤ Γ.dist (S.muV j) (S.alphaV j) + Γ.dist (S.alphaV j) w :=
            F.isTree.connected.dist_triangle
        _ ≤ 2 + 1 := by
            rw [SimpleGraph.dist_comm, S.dist_alphaV_muV F, dist_eq_one_iff_adj.2 hw]
        _ ≤ 4 := by norm_num
    · have h1 : (if j = i then (1 : (ZMod 5)ˣ) else -1) = -1 := by simp [hji]
      rw [h1]
      refine edge_char_eq_neg_one hφ ?_ ?_
      · show S.zMu j * S.zMu j ∈ nbrStab Γ G (S.alphaV i)
        rw [S.zMu_eq_z_muV, L.z_mul_self (S.valence_muV F j)]
        exact one_mem _
      · intro hK
        have hfix : L.z (S.muV j) • S.xiV i = S.xiV i :=
          mem_nbrStab.1 hK (S.xiV i) (S.adj_alphaV_xiV F i)
        rw [h71c.z_smul_eq_iff (S.valence_muV F j), S.dist_muV_xiV_ne F h71c hji] at hfix
        omega
  have hNval : φ ⟨S.zNb 1, hN⟩ = 1 := by
    refine (hφ _).1 (mem_nbrStab.2 fun w hw => ?_)
    change L.z (S.alphaV 1) • w = w
    rw [h71c.z_smul_eq_iff (S.valence_alphaV F 1)]
    calc Γ.dist (S.alphaV 1) w ≤ Γ.dist (S.alphaV 1) (S.alphaV i) + Γ.dist (S.alphaV i) w :=
          F.isTree.connected.dist_triangle
      _ ≤ 2 + 1 := by
          rw [dist_eq_one_iff_adj.2 hw]
          gcongr
          calc Γ.dist (S.alphaV 1) (S.alphaV i)
              ≤ Γ.dist (S.alphaV 1) S.beta + Γ.dist S.beta (S.alphaV i) :=
                F.isTree.connected.dist_triangle
            _ = 1 + 1 := by
                rw [SimpleGraph.dist_comm, S.dist_beta_alphaV F, S.dist_beta_alphaV F]
      _ ≤ 4 := by norm_num
  refine (hφ ⟨S.ubs, hU⟩).2 ?_
  have : (⟨S.ubs, hU⟩ : ↥(MulAction.stabilizer G (S.alphaV i) ⊓ MulAction.stabilizer G S.beta)) =
      ⟨S.zMu 0, hmem 0⟩ * ⟨S.zMu 1, hmem 1⟩ * ⟨S.zMu 2, hmem 2⟩ * ⟨S.zNb 1, hN⟩ := rfl
  rw [this, map_mul, map_mul, map_mul, hval 0, hval 1, hval 2, hNval]
  fin_cases i <;> decide

theorem ubs_mem_ballStab_two (F : FanTree Γ G) (h71c : Fan71c F L) :
    S.ubs ∈ ballStab Γ G 2 S.beta :=
  (S.mem_ballStab_two_beta_iff F).2 (S.ubs_mem_nbrStab F h71c)

theorem ubs_smul_muV_zero_ne (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L)
    (h83b : Fan83b F L) (h512 : Fan512 F L) : S.ubs • S.muV 0 ≠ S.muV 0 := by
  intro hfix
  have hc : S.ubs * L.z (S.muV 0) = L.z (S.muV 0) * S.ubs :=
    (h71c.comm_z_iff (S.valence_muV F 0) S.ubs).2 hfix
  have hrot := S.zMu_rot F h71c h81 h83b h512
  have hcomm : S.zNb 1 * S.zMu 0 = S.zMu 0 * S.zNb 1 := by
    have hd : Γ.dist (S.alphaV 1) (S.muV 0) ≤ 4 := by
      rw [SimpleGraph.dist_comm, S.dist_muV_alphaV_ne F h71c (i := 1) (j := 0) (by decide)]
    exact h71c.z_comm_of_dist_le (a := S.alphaV 1) (b := S.muV 0) (S.valence_alphaV F 1)
      (S.valence_muV F 0) hd
  have h1 : S.zMu 0 * S.zMu 1 * S.zMu 2 * S.zNb 1 * S.zMu 0 =
      S.zMu 0 * (S.zMu 0 * S.zMu 1 * S.zMu 2 * S.zNb 1) := hc
  have h2 : S.zMu 0 * S.zMu 1 * S.zMu 2 * S.zNb 1 * S.zMu 0 =
      (S.zMu 0 * S.zMu 1 * S.zMu 2 * S.zMu 0) * S.zNb 1 := by
    calc _ = S.zMu 0 * S.zMu 1 * S.zMu 2 * (S.zNb 1 * S.zMu 0) := by group
      _ = S.zMu 0 * S.zMu 1 * S.zMu 2 * (S.zMu 0 * S.zNb 1) := by rw [hcomm]
      _ = _ := by group
  rw [h2, show S.zMu 0 * (S.zMu 0 * S.zMu 1 * S.zMu 2 * S.zNb 1) =
    (S.zMu 0 * (S.zMu 0 * S.zMu 1 * S.zMu 2)) * S.zNb 1 by group] at h1
  have h3 := mul_right_cancel h1
  have h4 : S.zMu 1 * S.zMu 2 * S.zMu 0 = S.zMu 0 * S.zMu 1 * S.zMu 2 := by
    refine mul_left_cancel (a := S.zMu 0) ?_
    calc S.zMu 0 * (S.zMu 1 * S.zMu 2 * S.zMu 0) = S.zMu 0 * S.zMu 1 * S.zMu 2 * S.zMu 0 := by
          group
      _ = S.zMu 0 * (S.zMu 0 * S.zMu 1 * S.zMu 2) := h3
  have h5 : S.zMu 0 * S.zMu 1 * S.zMu 2 * L.z S.α = S.zMu 0 * S.zMu 1 * S.zMu 2 :=
    hrot.symm.trans h4
  have h6 : L.z S.α = 1 := mul_left_cancel (a := S.zMu 0 * S.zMu 1 * S.zMu 2) (by rw [h5, mul_one])
  exact L.z_ne_one S.D.val h6

theorem ubs_smul_muV_ne (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L)
    (h83b : Fan83b F L) (h512 : Fan512 F L) (i : Fin 3) : S.ubs • S.muV i ≠ S.muV i := by
  have hcomm : Commute S.xβ S.ubs :=
    mul_comm_of_fcomm_eq_one (S.fcomm_ubs F h71c h81 h83b h512)
  have hc := hcomm.inv_left.eq
  have key : ∀ j : Fin 3, S.ubs • S.muV (j + 1) = S.muV (j + 1) ↔ S.ubs • S.muV j = S.muV j := by
    intro j
    rw [← S.xβ_inv_smul_muV j, ← mul_smul, ← hc, mul_smul]
    exact smul_left_cancel_iff _
  have h0 := S.ubs_smul_muV_zero_ne F h71c h81 h83b h512
  fin_cases i
  · exact h0
  · intro h
    exact h0 ((key 0).1 h)
  · intro h
    exact h0 ((key 0).1 ((key 1).1 h))

end Sec9Cfg

end CFSG.Quasithin.Fan86
