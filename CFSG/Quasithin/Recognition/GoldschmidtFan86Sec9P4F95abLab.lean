module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95Ex
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3B1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Card
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lbl2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem f95_labelTriple (F : FanTree Γ G) (h71c : Fan71c F L) :
    Sec9P4F95Alg.LabelTriple (S.zMu1 0) (S.zMu1 2) (L.z S.α) := by
  have hd02 : S.D.alpha 0 ≠ S.D.alpha 2 := fun h => by
    have := S.D.dist_alpha_alpha F h71c (show (0 : Fin 5) ≠ 2 by decide)
    rw [h, SimpleGraph.dist_self] at this
    omega
  have hd0 : S.D.alpha 0 ≠ S.α := fun h => by
    have := S.D.dist_start_alpha F 0
    rw [h, SimpleGraph.dist_self] at this
    omega
  have hd2 : S.D.alpha 2 ≠ S.α := fun h => by
    have := S.D.dist_start_alpha F 2
    rw [h, SimpleGraph.dist_self] at this
    omega
  have hnn : ¬ ∃ β', ({S.D.alpha 0, S.D.alpha 2, S.α} : Set V) = Γ.neighborSet β' := by
    rintro ⟨β', hβ'⟩
    have h0 : S.D.alpha 0 ∈ Γ.neighborSet β' := by rw [← hβ']; simp
    have h2 : S.D.alpha 2 ∈ Γ.neighborSet β' := by rw [← hβ']; simp
    have hd := S.D.dist_alpha_alpha F h71c (show (0 : Fin 5) ≠ 2 by decide)
    have ht := F.isTree.connected.dist_triangle (u := S.D.alpha 0) (v := β') (w := S.D.alpha 2)
    have e0 : Γ.dist (S.D.alpha 0) β' = 1 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_one_iff_adj.2 h0
    have e2 : Γ.dist β' (S.D.alpha 2) = 1 := dist_eq_one_iff_adj.2 h2
    omega
  exact
    { pq := S.D.za_comm F h71c 0 2
      pr := S.D.za_comm_start F h71c 0
      qr := S.D.za_comm_start F h71c 2
      p2 := S.zMu1_mul_self F 0
      q2 := S.zMu1_mul_self F 2
      r2 := L.z_mul_self S.D.val
      p1 := L.z_ne_one (S.D.valence_alpha F 0)
      q1 := L.z_ne_one (S.D.valence_alpha F 2)
      pq' := h71c.2.1 _ _ (S.D.valence_alpha F 0) (S.D.valence_alpha F 2) hd02
      pr' := h71c.2.1 _ _ (S.D.valence_alpha F 0) S.D.val hd0
      qr' := h71c.2.1 _ _ (S.D.valence_alpha F 2) S.D.val hd2
      pqr := h71c.2.2 _ _ _ (S.D.valence_alpha F 0) (S.D.valence_alpha F 2) S.D.val hd02 hd0 hd2
        hnn }

theorem f95_c_cases (F : FanTree Γ G) (h71c : Fan71c F L) (h512 : Fan512 F L)
    (hc4 : Nat.card S.D.calpha = 4) {c' : G} (hc' : c' ∈ S.D.calpha) (ho : orderOf c' = 4) :
    ∃ m : ℕ, c' = S.c * L.z S.α ^ m := by
  have hord : orderOf S.c = 4 := by rw [← Nat.card_zpowers, ← S.gen, hc4]
  have hc2 : S.c ^ 2 = L.z S.α := S.D.sq_eq_z_of_card_four F h71c h512 S.gen hc4
  rw [S.gen] at hc'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc'
  have hmod : S.c ^ (k % 4) = c' := by
    rw [← hk]
    have := zpow_mod_orderOf S.c k
    rwa [hord, Nat.cast_ofNat] at this
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg _ (by norm_num)
  have h4 : k % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  generalize k % 4 = m at hmod h0 h4
  interval_cases m
  · exfalso
    have h1 : c' = 1 := by simpa using hmod.symm
    rw [h1, orderOf_one] at ho
    omega
  · exact ⟨0, by simpa using hmod.symm⟩
  · exfalso
    have h2 : c' = L.z S.α := by rw [← hmod, ← hc2]; simp
    rw [h2, L.orderOf_z S.D.val] at ho
    omega
  · refine ⟨1, ?_⟩
    rw [← hmod, pow_one, ← hc2]
    simp [pow_succ']

theorem f95_card_eq_four (F : FanTree Γ G) (h84a : Fan84a F L) {c' : G} (hc' : c' ∈ S.D.calpha)
    (ho : orderOf c' = 4) : Nat.card S.D.calpha = 4 := by
  have hdvd := Subgroup.orderOf_dvd_natCard S.D.calpha hc'
  have hle := (h84a S.α S.D).2
  have hfin := Sec8P3.finite_calpha S.D F
  have hpos : 0 < Nat.card S.D.calpha := Nat.card_pos
  rw [ho] at hdvd
  have := Nat.le_of_dvd hpos hdvd
  omega

end Sec9Cfg

end CFSG.Quasithin.Fan86
