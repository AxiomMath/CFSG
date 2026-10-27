module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94B
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lbl2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem f94_not_nbrs_of_dist_four (F : FanTree Γ G) {u v : V} (h : Γ.dist u v = 4) :
    ¬ ∃ β : V, ({u, v} : Set V) ⊆ Γ.neighborSet β := by
  rintro ⟨β, hβ⟩
  have hu : Γ.Adj β u := hβ (Set.mem_insert _ _)
  have hv : Γ.Adj β v := hβ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have h1 := F.isTree.connected.dist_triangle (u := u) (v := β) (w := v)
  have h2 : Γ.dist u β = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hu.symm
  have h3 : Γ.dist β v = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hv
  omega

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L) {F : FanTree Γ G}

theorem f94_dist_bv_le_two (F : FanTree Γ G) (i j : Fin 3) :
    Γ.dist (S.D.bv S.xβ i 1) (S.D.bv S.xβ j 1) ≤ 2 := by
  have h1 := F.isTree.connected.dist_triangle (u := S.D.bv S.xβ i 1) (v := S.beta)
    (w := S.D.bv S.xβ j 1)
  have h2 : Γ.dist (S.D.bv S.xβ i 1) S.beta = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2 (S.f94_adj_bv_beta F i).symm
  have h3 : Γ.dist S.beta (S.D.bv S.xβ j 1) = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2 (S.f94_adj_bv_beta F j)
  omega

theorem f94_zNb_commute (F : FanTree Γ G) (h71c : Fan71c F L) (i j : Fin 3) :
    S.zNb i * S.zNb j = S.zNb j * S.zNb i :=
  h71c.z_comm_of_dist_le (S.f94_valence_bv F i) (S.f94_valence_bv F j)
    (by have := S.f94_dist_bv_le_two F i j; omega)

theorem f94_zNb_mul_self (F : FanTree Γ G) (i : Fin 3) : S.zNb i * S.zNb i = 1 :=
  L.z_mul_self (S.f94_valence_bv F i)

theorem f94_not_triple_nbrs (F : FanTree Γ G) {a b c : V} (h : Γ.dist a b = 4) :
    ¬ ∃ β : V, ({a, b, c} : Set V) = Γ.neighborSet β := by
  rintro ⟨β, hβ⟩
  refine f94_not_nbrs_of_dist_four F h ⟨β, ?_⟩
  intro x hx
  rw [← hβ]
  rcases hx with rfl | hx
  · exact Set.mem_insert _ _
  · rw [Set.mem_singleton_iff.1 hx]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem f94_ub_ne (F : FanTree Γ G) (h71c : Fan71c F L) (h82a : Fan82a F L) (h512 : Fan512 F L) :
    S.ub ≠ 1 ∧ S.ub ≠ L.z S.α ∧ S.ub ≠ S.zNb 1 ∧ S.ub ≠ S.zNb 2 := by
  have hv : ∀ i, valence Γ (S.D.alpha i) = 5 := fun i => S.D.valence_alpha F i
  have hα : valence Γ S.α = 5 := S.D.val
  have hd : ∀ i j : Fin 5, i ≠ j → Γ.dist (S.D.alpha i) (S.D.alpha j) = 4 :=
    fun i j h => S.D.dist_alpha_alpha F h71c h
  have hne : ∀ i j : Fin 5, i ≠ j → S.D.alpha i ≠ S.D.alpha j := fun i j h e => by
    have := hd i j h
    rw [e, SimpleGraph.dist_self] at this
    omega
  have hca : ∀ j : Fin 5, L.z (S.D.alpha j) * L.z S.α = L.z S.α * L.z (S.D.alpha j) :=
    fun j => (S.zMu1_comm_alpha F h71c j).eq
  have hsq : ∀ i : Fin 5, L.z (S.D.alpha i) * L.z (S.D.alpha i) = 1 :=
    fun i => L.z_mul_self (hv i)
  have hu : S.ub = L.z (S.D.alpha 1) * L.z (S.D.alpha 3) * L.z S.α := S.ub_eq
  have t1 := h71c.2.2 (S.D.alpha 1) (S.D.alpha 3) S.α (hv 1) (hv 3) hα (hne 1 3 (by decide))
    (fun e => S.D.alpha_ne_start 1 e) (fun e => S.D.alpha_ne_start 3 e)
    (f94_not_triple_nbrs F (hd 1 3 (by decide)))
  refine ⟨by rw [hu]; exact t1, ?_, ?_, ?_⟩
  · intro h
    rw [hu] at h
    have h1 : (L.z (S.D.alpha 1) * L.z (S.D.alpha 3)) * L.z S.α = 1 * L.z S.α := by
      rw [one_mul]; exact h
    have h2 := mul_right_cancel h1
    have h4 : L.z (S.D.alpha 1) = L.z (S.D.alpha 3) := by
      calc L.z (S.D.alpha 1) = L.z (S.D.alpha 1) * (L.z (S.D.alpha 3) * L.z (S.D.alpha 3)) := by
            rw [hsq 3, mul_one]
        _ = (L.z (S.D.alpha 1) * L.z (S.D.alpha 3)) * L.z (S.D.alpha 3) := by rw [mul_assoc]
        _ = L.z (S.D.alpha 3) := by rw [h2, one_mul]
    exact hne 1 3 (by decide) (h71c.z_injective (hv 1) (hv 3) h4)
  · intro h
    rw [hu, ← S.zalpha_mul_zNb_two F h71c h512, S.zNb_two] at h
    have h1 : L.z S.α * (L.z (S.D.alpha 1) * L.z (S.D.alpha 3)) = L.z S.α * L.z (S.D.alpha 2) := by
      rw [← h]
      calc L.z S.α * (L.z (S.D.alpha 1) * L.z (S.D.alpha 3))
          = (L.z S.α * L.z (S.D.alpha 1)) * L.z (S.D.alpha 3) := by rw [mul_assoc]
        _ = (L.z (S.D.alpha 1) * L.z S.α) * L.z (S.D.alpha 3) := by rw [hca 1]
        _ = L.z (S.D.alpha 1) * (L.z S.α * L.z (S.D.alpha 3)) := by rw [mul_assoc]
        _ = L.z (S.D.alpha 1) * (L.z (S.D.alpha 3) * L.z S.α) := by rw [hca 3]
        _ = L.z (S.D.alpha 1) * L.z (S.D.alpha 3) * L.z S.α := by rw [mul_assoc]
    have h2 := mul_left_cancel h1
    have t2 := h71c.2.2 (S.D.alpha 1) (S.D.alpha 3) (S.D.alpha 2) (hv 1) (hv 3) (hv 2)
      (hne 1 3 (by decide)) (hne 1 2 (by decide)) (hne 3 2 (by decide))
      (f94_not_triple_nbrs F (hd 1 3 (by decide)))
    exact t2 (by rw [h2, hsq 2])
  · intro h
    rw [hu, S.zNb_two] at h
    have hprod : L.z (S.D.alpha 0) * L.z (S.D.alpha 1) * L.z (S.D.alpha 2) * L.z (S.D.alpha 3) *
        L.z (S.D.alpha 4) = 1 := h82a S.α S.D
    rw [← h] at hprod
    have e1 : L.z (S.D.alpha 1) * (L.z (S.D.alpha 1) * L.z (S.D.alpha 3) * L.z S.α) *
        L.z (S.D.alpha 3) = L.z S.α := by
      calc _ = (L.z (S.D.alpha 1) * L.z (S.D.alpha 1)) *
            (L.z (S.D.alpha 3) * L.z S.α * L.z (S.D.alpha 3)) := by simp only [mul_assoc]
        _ = L.z (S.D.alpha 3) * L.z S.α * L.z (S.D.alpha 3) := by rw [hsq 1, one_mul]
        _ = L.z S.α * L.z (S.D.alpha 3) * L.z (S.D.alpha 3) := by rw [hca 3]
        _ = L.z S.α := by rw [mul_assoc, hsq 3, mul_one]
    have e2 : L.z (S.D.alpha 0) * L.z S.α * L.z (S.D.alpha 4) = 1 := by
      calc L.z (S.D.alpha 0) * L.z S.α * L.z (S.D.alpha 4)
          = L.z (S.D.alpha 0) * (L.z (S.D.alpha 1) * (L.z (S.D.alpha 1) * L.z (S.D.alpha 3) *
              L.z S.α) * L.z (S.D.alpha 3)) * L.z (S.D.alpha 4) := by rw [e1]
        _ = 1 := by rw [← hprod]; simp only [mul_assoc]
    have t3 := h71c.2.2 (S.D.alpha 0) (S.D.alpha 4) S.α (hv 0) (hv 4) hα (hne 0 4 (by decide))
      (fun e => S.D.alpha_ne_start 0 e) (fun e => S.D.alpha_ne_start 4 e)
      (f94_not_triple_nbrs F (hd 0 4 (by decide)))
    apply t3
    calc L.z (S.D.alpha 0) * L.z (S.D.alpha 4) * L.z S.α
        = L.z (S.D.alpha 0) * (L.z (S.D.alpha 4) * L.z S.α) := mul_assoc _ _ _
      _ = L.z (S.D.alpha 0) * (L.z S.α * L.z (S.D.alpha 4)) := by rw [hca 4]
      _ = L.z (S.D.alpha 0) * L.z S.α * L.z (S.D.alpha 4) := (mul_assoc _ _ _).symm
      _ = 1 := e2

end Sec9Cfg

end CFSG.Quasithin.Fan86
