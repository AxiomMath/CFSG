module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Asm2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Asm1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Key3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P72

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem mid_surj (F : FanTree Γ G) {α : V} (hα : valence Γ α = 5) {l ν : Fin 5 → V}
    (hν : ∀ i, Br Γ α (ν i) (l i)) (hd : ∀ i j, i ≠ j → Γ.dist (l i) (l j) = 4) :
    Function.Injective ν ∧ ∀ w, Γ.Adj α w → ∃ i, ν i = w := by
  have hinj : Function.Injective ν := by
    intro i j hij
    by_contra hne
    have h4 := hd i j hne
    have e1 : Γ.dist (l i) (ν j) = 1 := by
      rw [← hij]
      exact dist_eq_one_iff_adj.mpr (hν i).a2.symm
    have e2 : Γ.dist (ν j) (l j) = 1 := dist_eq_one_iff_adj.mpr (hν j).a2
    have := F.isTree.connected.dist_triangle (u := l i) (v := ν j) (w := l j)
    omega
  refine ⟨hinj, ?_⟩
  have hα' : Nat.card (Γ.neighborSet α) = 5 := hα
  have hfin : Finite (Γ.neighborSet α) := Nat.finite_of_card_ne_zero (by omega)
  let f : Fin 5 → Γ.neighborSet α := fun i => ⟨ν i, (hν i).a1⟩
  have hf : Function.Injective f := fun i j e => hinj (congrArg Subtype.val e)
  have hb := hf.bijective_of_nat_card_le (by rw [hα']; simp)
  intro w hw
  obtain ⟨i, hi⟩ := hb.2 ⟨w, hw⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem fan72a_of (h : Fan71c F L) (hlab : Lab3 F L) : Fan72a F L := by
  intro α l hα hl hd
  obtain ⟨x1, x2, x3, x4, a01, a12, a23, a34, n02, n13, n24⟩ := exists_arc4 F α
  have A : Arc4 Γ α x1 x2 x3 x4 := ⟨a01, a12, a23, a34, n02, n13, n24⟩
  obtain ⟨sα, -, -⟩ := s_facts h a01 a12 a23 a34 n02 n13 n24 hα
  obtain ⟨y₁, y₂, hy₁, hy₂, hnd, -⟩ := exists_pairs F h hα A
  have hadjs : ∀ w, Γ.Adj α w → Γ.Adj α (L.z x4 • w) := fun w hw => by
    have := (F.adj_smul (L.z x4) α w).2 hw
    rwa [sα] at this
  choose ν hν using fun i => br_of_dist_two F.isTree (hl i).1
  obtain ⟨-, hsurj⟩ := mid_surj F hα hν hd
  obtain ⟨k, hk⟩ := hsurj x1 a01
  obtain ⟨a, ha⟩ := hsurj y₁ hy₁
  obtain ⟨b, hb⟩ := hsurj (L.z x4 • y₁) (hadjs _ hy₁)
  obtain ⟨c, hc⟩ := hsurj y₂ hy₂
  obtain ⟨d, hdd⟩ := hsurj (L.z x4 • y₂) (hadjs _ hy₂)
  have hnd' : [k, a, b, c, d].Nodup := by
    apply List.Nodup.of_map ν
    simp only [List.map_cons, List.map_nil, hk, ha, hb, hc, hdd]
    exact hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10⟩ := hnd
  have hcomm : ∀ i j, L.z (l i) * L.z (l j) = L.z (l j) * L.z (l i) := fun i j =>
    z_comm_two h (hl i).2 (hl j).2 (by rw [(hl i).1]) (by rw [(hl j).1])
  have hprod := prod_ofFn_five (fun i => L.z (l i)) hcomm k a b c d hnd'
  rw [hprod]
  have := zGroup_comm h α
  have bk : Br Γ α x1 (l k) := by
    have := hν k
    rwa [hk] at this
  have bx : Br Γ α x1 x2 := ⟨a01, a12, n02.symm⟩
  have bb : Br Γ α (ν b) (L.z x4 • l a) := by
    rw [show ν b = L.z x4 • ν a by rw [hb, ha]]
    exact br_smul_s h hα A (hν a)
  have bd : Br Γ α (ν d) (L.z x4 • l c) := by
    rw [show ν d = L.z x4 • ν c by rw [hdd, hc]]
    exact br_smul_s h hα A (hν c)
  have hkey := key h hlab hα A (hν a) (hν c) (by rw [ha]; exact fun e => n1 e.symm)
    (by rw [hc]; exact fun e => n3 e.symm) (by rw [ha, hc]; exact n6)
    (by rw [hc, ha]; exact fun e => n8 e.symm)
  refine alg5_sub (L.zGroup 2 α) (br_z_mem F hα (hν k)) (br_z_mem F hα (hν a))
    (br_z_mem F hα (br_smul_s h hα A (hν a))) (br_z_mem F hα (hν b)) (br_z_mem F hα (hν c))
    (br_z_mem F hα (br_smul_s h hα A (hν c))) (br_z_mem F hα (hν d)) (br_z_mem F hα bx)
    (z_mem_zGroup (by rw [SimpleGraph.dist_self]; omega) hα) hkey
    (branch_alt hlab hα bk bx) (branch_alt hlab hα bb (hν b)) (branch_alt hlab hα bd (hν d))
    (L.z_mul_self (hl k).2) (L.z_mul_self hα)

end P72

end CFSG.Quasithin.Fan86
