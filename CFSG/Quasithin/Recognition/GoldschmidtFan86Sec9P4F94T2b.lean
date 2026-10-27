module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Card
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94M1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94T1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem muV_two : S.muV 2 = S.D.delta 2 := by
  rw [muV_eq]
  exact S.collar_three

theorem xβ_inv_smul_alphaV (j : Fin 3) : S.xβ⁻¹ • S.alphaV j = S.alphaV (j + 1) := by
  rw [alphaV_eq, alphaV_eq, S.xβ_inv_smul_family]

theorem wA_one_mem_iff (F : FanTree Γ G) (j : Fin 3) :
    S.wA 1 ∈ nbrStab Γ G (S.alphaV (j + 1)) ↔ S.w ∈ nbrStab Γ G (S.alphaV j) := by
  rw [← S.xβ_inv_smul_alphaV j, F.mem_nbrStab_smul_iff]
  have : (S.xβ⁻¹)⁻¹ * S.wA 1 * S.xβ⁻¹ = S.w := by
    simp only [wA, Fin.val_one, pow_one]
    group
  rw [this]

theorem wA_one_sq_mem_iff (F : FanTree Γ G) (j : Fin 3) :
    S.wA 1 * S.wA 1 ∈ nbrStab Γ G (S.alphaV (j + 1)) ↔
      S.w * S.w ∈ nbrStab Γ G (S.alphaV j) := by
  rw [← S.xβ_inv_smul_alphaV j, F.mem_nbrStab_smul_iff]
  have : (S.xβ⁻¹)⁻¹ * (S.wA 1 * S.wA 1) * S.xβ⁻¹ = S.w * S.w := by
    simp only [wA, Fin.val_one, pow_one]
    group
  rw [this]

theorem w_mem_alphaV_two (F : FanTree Γ G) : S.w ∈ nbrStab Γ G (S.alphaV 2) := by
  have h := (Arc.mem_stab G).1 S.isW1.fixes
  rw [S.alphaV_two]
  exact F.fix_two_nbrs (S.D.adj_beta_alpha 2).symm (S.D.adj_alpha_xi 2)
    (S.D.xi_ne_beta 2).symm (h 1 (by norm_num)) (h 3 (by norm_num))

theorem w_sq_not_mem (F : FanTree Γ G) (h71c : Fan71c F L) (j : Fin 3) (hj : j ≠ 2) :
    S.w * S.w ∉ nbrStab Γ G (S.alphaV j) := by
  intro hmem
  have hx := mem_nbrStab.1 hmem (S.xiV j) (S.adj_alphaV_xiV F j)
  have hza : L.z S.α • S.xiV j = S.xiV j := by
    refine (h71c.z_smul_eq_iff S.D.val _).2 ?_
    have := F.isTree.connected.dist_triangle (u := S.α) (v := S.beta) (w := S.xiV j)
    have h1 : Γ.dist S.α S.beta = 1 := S.D.dist_start_beta F 2
    have h2 := S.dist_beta_xiV F h71c j
    show Γ.dist S.α (S.xiV j) ≤ 4
    omega
  have hzd : L.z (S.D.delta 2) • S.xiV j ≠ S.xiV j := by
    intro h
    have := (h71c.z_smul_eq_iff (S.D.valence_delta F 2) _).1 h
    have h5 := S.dist_muV_xiV_ne F h71c (i := j) (j := 2) hj.symm
    rw [S.muV_two] at h5
    omega
  rcases S.isW1.sq with h | h
  · rw [h, mul_smul, hza] at hx
    exact hzd hx
  · rw [h] at hx
    exact hzd hx

theorem c_mem_alphaV_zero : S.c ∈ nbrStab Γ G (S.alphaV 0) := by
  rw [S.alphaV_zero]
  have : S.c ∈ S.D.calpha := by
    rw [S.gen]
    exact Subgroup.mem_zpowers _
  exact (Subgroup.mem_inf.1 this).1

theorem c_mem_alphaV_two (F : FanTree Γ G) (h7 : Fan7 F L) : S.c ∈ nbrStab Γ G (S.alphaV 2) := by
  have : S.c ∈ S.D.calpha := by
    rw [S.gen]
    exact Subgroup.mem_zpowers _
  rw [S.alphaV_two]
  exact P2c.calpha_mem_nbrStab_alpha S.D h7 this 2

theorem c_sq_eq (F : FanTree Γ G) (h71c : Fan71c F L) (h512 : Fan512 F L)
    (hc4 : Nat.card S.D.calpha = 4) : S.c * S.c = L.z S.α := by
  rw [← pow_two]
  exact S.D.sq_eq_z_of_card_four F h71c h512 S.gen hc4

theorem z_mem_nbrStab_alphaV (F : FanTree Γ G) (h71c : Fan71c F L) (j : Fin 3) :
    L.z S.α ∈ nbrStab Γ G (S.alphaV j) := by
  refine mem_nbrStab.2 fun w hw => (h71c.z_smul_eq_iff S.D.val w).2 ?_
  have h1 : Γ.dist S.α S.beta = 1 := S.D.dist_start_beta F 2
  have h2 := S.dist_beta_alphaV F j
  have h3 := SimpleGraph.dist_eq_one_iff_adj.2 hw
  have t1 := F.isTree.connected.dist_triangle (u := S.α) (v := S.beta) (w := S.alphaV j)
  have t2 := F.isTree.connected.dist_triangle (u := S.α) (v := S.alphaV j) (w := w)
  show Γ.dist S.α w ≤ 4
  omega

theorem c_not_mem_alphaV_one (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h512 : Fan512 F L) (hc4 : Nat.card S.D.calpha = 4) :
    S.c ∉ nbrStab Γ G (S.alphaV 1) := by
  intro hK
  have hc : S.c ∈ S.D.calpha := by
    rw [S.gen]
    exact Subgroup.mem_zpowers _
  have hz := S.calpha_inf_nbrStab_alphaV_one_le F h7 h81 h512 hc hK
  have h1 : S.c * S.c = 1 := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← hn, ← zpow_add, ← two_mul, zpow_mul, zpow_two, L.z_mul_self S.D.val, one_zpow]
  have h2 := S.c_sq_eq F h7.2.2.1 h512 hc4
  exact L.z_ne_one S.D.val (h2.symm.trans h1)

end Sec9Cfg

end CFSG.Quasithin.Fan86
