module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Ord
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem w_fix_vert (m : ℕ) (hm : m ≤ 4) : S.w • (S.D.P 2).vert m = (S.D.P 2).vert m :=
  (Arc.mem_stab G).1 S.isW1.fixes m hm

theorem w_mem_stabilizer : S.w ∈ MulAction.stabilizer G S.α := by
  have := S.w_fix_vert 0 (by norm_num)
  rw [S.D.start 2] at this
  exact MulAction.mem_stabilizer_iff.2 this

theorem w_fix_alpha2 : S.w • S.D.alpha 2 = S.D.alpha 2 := S.w_fix_vert 2 (by norm_num)

theorem x_w : S.w⁻¹ * S.D.x * S.w = S.D.x ^ 2 := S.isW1.conj

theorem w_y2 : S.w⁻¹ * S.yEta 2 * S.w = S.yEta 2 :=
  conj_eq_of_fcomm_eq_one S.commutes

theorem dist_start_eta' : Γ.dist S.α S.η' = 4 := by
  have := S.isBeta.pair.2.2.2.2.2.2.1
  omega

theorem dist_alpha0_eta' : Γ.dist (S.D.alpha 0) S.η' = 2 := S.isBeta.pair.2.2.2.2.1

theorem w_z2 (F : FanTree Γ G) : S.w⁻¹ * S.zMu1 2 * S.w = S.zMu1 2 := by
  have := L.z_inv_smul S.w (S.D.valence_alpha F 2)
  rw [show S.w⁻¹ • S.D.alpha 2 = S.D.alpha 2 from inv_smul_eq_iff.2 S.w_fix_alpha2.symm] at this
  exact this.symm

theorem valence_eta' (F : FanTree Γ G) : valence Γ S.η' = 5 :=
  valence_of_dist_even F S.D.val (by rw [S.dist_start_eta'])

theorem dist_delta_eta' (F : FanTree Γ G) : Γ.dist (S.D.delta 0) S.η' ≤ 4 := by
  have h1 : Γ.dist (S.D.alpha 0) (S.D.delta 0) = 2 := S.D.dist_alpha_delta F 0
  calc Γ.dist (S.D.delta 0) S.η'
      ≤ Γ.dist (S.D.delta 0) (S.D.alpha 0) + Γ.dist (S.D.alpha 0) S.η' :=
        F.isTree.connected.dist_triangle
    _ = 4 := by rw [SimpleGraph.dist_comm, h1, S.dist_alpha0_eta']

theorem xy (j : Fin 5) : S.D.x⁻¹ * S.yEta j * S.D.x = S.yEta (j + 1) := by
  have hv : ((j + 1 : Fin 5) : ℕ) = (j.val + 1) % 5 := by
    rw [Fin.val_add]
    rfl
  have hp : S.D.x ^ ((j + 1 : Fin 5) : ℕ) = S.D.x ^ (j.val + 1) := by
    rw [hv]
    exact (pow_eq_pow_mod (j.val + 1) S.D.x_pow_five).symm
  show S.D.x⁻¹ * ((S.D.x ^ (j : ℕ))⁻¹ * (L.z (S.D.delta 0) * L.z S.η') * S.D.x ^ (j : ℕ)) *
      S.D.x = (S.D.x ^ ((j + 1 : Fin 5) : ℕ))⁻¹ * (L.z (S.D.delta 0) * L.z S.η') *
      S.D.x ^ ((j + 1 : Fin 5) : ℕ)
  rw [hp, pow_succ]
  group

variable (F : FanTree Γ G) (h : Fan71c F L)

include h

theorem z_eta'_mem_stabilizer : L.z S.η' ∈ MulAction.stabilizer G S.α :=
  (h.z_mem_stabilizer_iff (S.valence_eta' F) S.α).2
    (by rw [SimpleGraph.dist_comm, S.dist_start_eta'])

theorem z_delta0_eta'_comm : L.z (S.D.delta 0) * L.z S.η' = L.z S.η' * L.z (S.D.delta 0) :=
  h.z_comm_of_dist_le (S.D.valence_delta F 0) (S.valence_eta' F) (S.dist_delta_eta' F)

theorem t_mul_self : (L.z (S.D.delta 0) * L.z S.η') * (L.z (S.D.delta 0) * L.z S.η') = 1 :=
  mul_mul_self_eq_one (L.z_mul_self (S.D.valence_delta F 0)) (L.z_mul_self (S.valence_eta' F))
    (S.z_delta0_eta'_comm F h)

theorem y_sq (j : Fin 5) : S.yEta j ^ 2 = 1 :=
  conj_sq_eq_one (S.t_mul_self F h)

theorem y_mem_stabilizer (j : Fin 5) : S.yEta j ∈ MulAction.stabilizer G S.α := by
  have hx := S.D.x_mem_stabilizer F h
  refine mul_mem (mul_mem (inv_mem (pow_mem hx _)) (mul_mem ?_ ?_)) (pow_mem hx _)
  · exact S.D.z_delta_mem_stabilizer F h 0
  · exact S.z_eta'_mem_stabilizer F h

theorem z_alpha_mem_stabilizer (j : Fin 5) : L.z (S.D.alpha j) ∈ MulAction.stabilizer G S.α :=
  (h.z_mem_stabilizer_iff (S.D.valence_alpha F j) S.α).2
    (by rw [SimpleGraph.dist_comm, S.D.dist_start_alpha F j]; norm_num)

theorem xz (j : Fin 5) : S.D.x⁻¹ * S.zMu1 j * S.D.x = S.zMu1 (j + 1) := by
  have := L.z_inv_smul S.D.x (S.D.valence_alpha F j)
  rw [show S.D.x⁻¹ • S.D.alpha j = S.D.alpha (j + 1) from
    S.D.x_inv_smul_vert F h j (m := 2) (by norm_num)] at this
  exact this.symm

omit h in
theorem wy (j : Fin 5) : S.w⁻¹ * S.yEta j * S.w = S.yEta (tauLab j) :=
  conj_tauLab S.D.x_pow_five S.x_w S.xy S.w_y2 j

theorem wz (j : Fin 5) : S.w⁻¹ * S.zMu1 j * S.w = S.zMu1 (tauLab j) :=
  conj_tauLab S.D.x_pow_five S.x_w (S.xz F h) (S.w_z2 F) j

theorem w_pow_four : S.w ^ 4 = 1 := by
  have hw4 : S.w ^ 4 = (S.w * S.w) * (S.w * S.w) := by
    rw [show 4 = 2 + 2 from rfl, pow_add, pow_two]
  rw [hw4]
  rcases S.isW1.sq with hq | hq
  · rw [hq]
    refine mul_mul_self_eq_one (L.z_mul_self (S.D.valence_delta F 2)) (L.z_mul_self S.D.val) ?_
    exact h.z_comm_of_dist_le (S.D.valence_delta F 2) S.D.val
      (by rw [SimpleGraph.dist_comm, S.D.dist_delta F 2])
  · rw [hq]
    exact L.z_mul_self (S.D.valence_delta F 2)

theorem zMu1_comm (k l : Fin 5) : fcomm (S.zMu1 k) (S.zMu1 l) = 1 := by
  by_cases hkl : k = l
  · subst hkl
    unfold fcomm
    group
  · refine fcomm_eq_one_of_mul_comm ?_
    exact h.z_comm_of_dist_le (S.D.valence_alpha F k) (S.D.valence_alpha F l)
      (by rw [S.D.dist_alpha_alpha F h hkl])

theorem p1Rel_of (h82a : Fan82a F L) (h83b : Fan83b F L) (h83d : Fan83d F L) (h85 : Fan85 F L) :
    P1Rel S.D.x S.w (L.z S.α) S.yEta S.zMu1 where
  x5 := S.D.x_pow_five
  w4 := S.w_pow_four F h
  y2 := S.y_sq F h
  z2 := fun j => by
    rw [pow_two]
    exact L.z_mul_self (S.D.valence_alpha F j)
  za2 := by
    rw [pow_two]
    exact L.z_mul_self S.D.val
  xw := S.x_w
  xy := S.xy
  xz := S.xz F h
  wy := S.wy
  wz := S.wz F h
  yy := fun k l hkl => h83d.2 S.α S.D S.η' S.isBeta.pair k l hkl
  yz := fun k l => h83b S.α S.D S.η' S.isBeta.pair k l
  zz := S.zMu1_comm F h
  prod_y := h85 S.α S.D S.η' S.isBeta.pair
  prod_z := h82a S.α S.D
  cent_x := fcomm_eq_one_of_mul_comm (L.comm_z_of_mem_stabilizer S.D.val (S.D.x_mem_stabilizer F h))
  cent_w := fcomm_eq_one_of_mul_comm (L.comm_z_of_mem_stabilizer S.D.val S.w_mem_stabilizer)
  cent_y := fun j => fcomm_eq_one_of_mul_comm
    (L.comm_z_of_mem_stabilizer S.D.val (S.y_mem_stabilizer F h j))
  cent_z := fun j => fcomm_eq_one_of_mul_comm
    (h.z_comm_of_dist_le (S.D.valence_alpha F j) S.D.val
      (by rw [SimpleGraph.dist_comm, S.D.dist_start_alpha F j]; norm_num))

end Sec9Cfg

end CFSG.Quasithin.Fan86
