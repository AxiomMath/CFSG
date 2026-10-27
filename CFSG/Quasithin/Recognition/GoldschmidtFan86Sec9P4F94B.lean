module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lbl

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L) {F : FanTree Γ G}

theorem f94_xβ_pow_smul_beta (n : ℕ) : S.xβ ^ n • S.beta = S.beta := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, S.xβ_smul_beta, ih]

theorem f94_adj_bv_beta (F : FanTree Γ G) (i : Fin 3) : Γ.Adj S.beta (S.D.bv S.xβ i 1) := by
  have hbv : S.D.bv S.xβ i 1 = (S.xβ ^ (i : ℕ))⁻¹ • S.α := by simp [D10Set.bv, S.D.start 0]
  have hfix : (S.xβ ^ (i : ℕ))⁻¹ • S.beta = S.beta := by
    rw [inv_smul_eq_iff]
    exact (S.f94_xβ_pow_smul_beta _).symm
  have h := (F.adj_smul (S.xβ ^ (i : ℕ))⁻¹ S.beta S.α).2 (S.D.adj_start_beta 2).symm
  rwa [hfix, ← hbv] at h

theorem f94_valence_bv (F : FanTree Γ G) (i : Fin 3) : valence Γ (S.D.bv S.xβ i 1) = 5 := by
  have hbv : S.D.bv S.xβ i 1 = (S.xβ ^ (i : ℕ))⁻¹ • S.α := by simp [D10Set.bv, S.D.start 0]
  rw [hbv, valence_smul F]
  exact S.D.val

theorem zNb_mem_ballStab_three (h71c : Fan71c F L) (i : Fin 3) :
    S.zNb i ∈ ballStab Γ G 3 S.beta := by
  refine mem_ballStab.2 fun w hw => ?_
  refine (h71c.z_smul_eq_iff (S.f94_valence_bv F i) w).2 ?_
  have h1 := F.isTree.connected.dist_triangle (u := S.D.bv S.xβ i 1) (v := S.beta) (w := w)
  have h2 : Γ.dist (S.D.bv S.xβ i 1) S.beta = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2 (S.f94_adj_bv_beta F i).symm
  omega

theorem ub_mem_ballStab_three (F : FanTree Γ G) (h71c : Fan71c F L) (h82c : Fan82c F L) :
    S.ub ∈ ballStab Γ G 3 S.beta := by
  have h1 := (h82c S.α S.D 1 3 (by decide)).1
  have hm : midlab (1 : Fin 5) 3 = 2 := by decide
  rw [hm] at h1
  have h2 : L.z S.α ∈ ballStab Γ G 3 S.beta := by
    have := S.zNb_mem_ballStab_three h71c 0
    rwa [S.zNb_zero] at this
  rw [S.ub_eq]
  exact (ballStab Γ G 3 S.beta).mul_mem h1 h2

end Sec9Cfg

end CFSG.Quasithin.Fan86
