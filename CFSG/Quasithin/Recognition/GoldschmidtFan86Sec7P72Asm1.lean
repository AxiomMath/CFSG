module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Key

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P72

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem br_of_dist_two (hT : Γ.IsTree) {α l : V} (h : Γ.dist α l = 2) : ∃ ν, Br Γ α ν l := by
  obtain ⟨ν, hνl, hν⟩ := IsTree.exists_adj_dist_succ hT (u := α) (v := l) (n := 1) h
  have hlα : l ≠ α := fun e => by rw [e, SimpleGraph.dist_self] at h; omega
  exact ⟨ν, dist_eq_one_iff_adj.mp hν, hνl, hlα⟩

theorem branch_alt (hlab : Lab3 F L) {α ν l l' : V} (hα : valence Γ α = 5) (b : Br Γ α ν l)
    (b' : Br Γ α ν l') : L.z l' = L.z l ∨ L.z l' = L.z l * L.z α := by
  by_cases hll : l = l'
  · exact Or.inl (by rw [hll])
  · right
    have hv3 := (b.valence F hα).1
    have hl := (b.valence F hα).2
    have hset := nbrSet_eq_three hv3 b.a1.symm b.a2 b'.a2 b.ne.symm b'.ne.symm hll
    have h3 := hlab ν α l l' hv3 hset b.ne.symm b'.ne.symm hll
    rw [eq_inv_of_mul_eq_one_right h3, mul_inv_rev, L.z_inv hl, L.z_inv hα]

theorem z_comm_two (h : Fan71c F L) {α a b : V} (ha : valence Γ a = 5) (hb : valence Γ b = 5)
    (da : Γ.dist α a ≤ 2) (db : Γ.dist α b ≤ 2) : L.z a * L.z b = L.z b * L.z a := by
  apply Fan71c.z_comm_of_dist_le h ha hb
  have h1 := F.isTree.connected.dist_triangle (u := a) (v := α) (w := b)
  have h2 : Γ.dist a α = Γ.dist α a := SimpleGraph.dist_comm
  omega

theorem zGroup_comm (h : Fan71c F L) (α : V) : IsMulCommutative (L.zGroup 2 α) := by
  refine Subgroup.isMulCommutative_closure ?_
  rintro _ ⟨a, da, ha, rfl⟩ _ ⟨b, db, hb, rfl⟩ -
  exact z_comm_two h ha hb da db

theorem z_mem_zGroup {α δ : V} (hd : Γ.dist α δ ≤ 2) (hδ : valence Γ δ = 5) :
    L.z δ ∈ L.zGroup 2 α :=
  Subgroup.subset_closure (L.z_mem_zSet hd hδ)

theorem br_z_mem (F : FanTree Γ G) {α ν l : V} (hα : valence Γ α = 5) (b : Br Γ α ν l) :
    L.z l ∈ L.zGroup 2 α :=
  z_mem_zGroup (by rw [SimpleGraph.dist_comm, b.dist_alpha F.isTree]) (b.valence F hα).2

theorem exists_pairs (F : FanTree Γ G) (h : Fan71c F L) {α x1 x2 x3 x4 : V}
    (hα : valence Γ α = 5) (A : Arc4 Γ α x1 x2 x3 x4) :
    ∃ y₁ y₂ : V, Γ.Adj α y₁ ∧ Γ.Adj α y₂ ∧ [x1, y₁, L.z x4 • y₁, y₂, L.z x4 • y₂].Nodup ∧
      ∀ w, Γ.Adj α w → w = x1 ∨ w = y₁ ∨ w = L.z x4 • y₁ ∨ w = y₂ ∨ w = L.z x4 • y₂ := by
  classical
  obtain ⟨-, -, -, vx4⟩ := val_arc4 F A.a01 A.a12 A.a23 A.a34 hα
  obtain ⟨sα, sx1, smove⟩ := s_facts h A.a01 A.a12 A.a23 A.a34 A.n02 A.n13 A.n24 hα
  have hss : ∀ w : V, L.z x4 • L.z x4 • w = w := fun w => by
    rw [smul_smul, L.z_mul_self vx4, one_smul]
  have hinv : ∀ u w : V, L.z x4 • u = w → L.z x4 • w = u := fun u w e => by rw [← e, hss]
  have hadjs : ∀ w, Γ.Adj α w → Γ.Adj α (L.z x4 • w) := fun w hw => by
    have := (F.adj_smul (L.z x4) α w).2 hw
    rwa [sα] at this
  have hN : (Γ.neighborSet α).ncard = 5 := by
    rw [← Nat.card_coe_set_eq]
    exact hα
  have hfin : (Γ.neighborSet α).Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨y₁, hy₁, hy₁x⟩ := F.exists_adj_ne α x1
  have hex : ∃ y₂, Γ.Adj α y₂ ∧ y₂ ≠ x1 ∧ y₂ ≠ y₁ ∧ y₂ ≠ L.z x4 • y₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : Γ.neighborSet α ⊆ ({x1, y₁, L.z x4 • y₁} : Set V) := by
      intro w hw
      by_cases h1 : w = x1
      · simp [h1]
      by_cases h2 : w = y₁
      · simp [h2]
      have := hcon w hw h1 h2
      simp [this]
    have h3 : ({x1, y₁, L.z x4 • y₁} : Set V).ncard ≤ 3 := by
      have e1 := Set.ncard_insert_le x1 ({y₁, L.z x4 • y₁} : Set V)
      have e2 := Set.ncard_insert_le y₁ ({L.z x4 • y₁} : Set V)
      have e3 := Set.ncard_singleton (L.z x4 • y₁)
      omega
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  obtain ⟨y₂, hy₂, hy₂x, hy₂y, hy₂s⟩ := hex
  have n1 : x1 ≠ y₁ := hy₁x.symm
  have n2 : x1 ≠ L.z x4 • y₁ := fun e => hy₁x (by rw [← hinv _ _ e.symm, sx1])
  have n3 : x1 ≠ y₂ := hy₂x.symm
  have n4 : x1 ≠ L.z x4 • y₂ := fun e => hy₂x (by rw [← hinv _ _ e.symm, sx1])
  have n5 : y₁ ≠ L.z x4 • y₁ := (smove y₁ hy₁ n1).symm
  have n6 : y₁ ≠ y₂ := hy₂y.symm
  have n7 : y₁ ≠ L.z x4 • y₂ := fun e => hy₂s (hinv _ _ e.symm).symm
  have n8 : L.z x4 • y₁ ≠ y₂ := hy₂s.symm
  have n9 : L.z x4 • y₁ ≠ L.z x4 • y₂ := fun e => n6 (MulAction.injective (L.z x4) e)
  have n10 : y₂ ≠ L.z x4 • y₂ := (smove y₂ hy₂ n3).symm
  have hnd : [x1, y₁, L.z x4 • y₁, y₂, L.z x4 • y₂].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    exact ⟨⟨n1, n2, n3, n4⟩, ⟨n5, n6, n7⟩, ⟨n8, n9⟩, n10⟩
  refine ⟨y₁, y₂, hy₁, hy₂, hnd, ?_⟩
  have hsub : ({x1, y₁, L.z x4 • y₁, y₂, L.z x4 • y₂} : Set V) ⊆ Γ.neighborSet α := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact A.a01
    · exact hy₁
    · exact hadjs _ hy₁
    · exact hy₂
    · exact hadjs _ hy₂
  have h5 : ({x1, y₁, L.z x4 • y₁, y₂, L.z x4 • y₂} : Set V).ncard = 5 := by
    have : ({x1, y₁, L.z x4 • y₁, y₂, L.z x4 • y₂} : Set V) =
        ↑([x1, y₁, L.z x4 • y₁, y₂, L.z x4 • y₂].toFinset) := by
      ext w
      simp
    rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
    rfl
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
  intro w hw
  have hw' : w ∈ ({x1, y₁, L.z x4 • y₁, y₂, L.z x4 • y₂} : Set V) := by rw [heq]; exact hw
  simpa using hw'

end P72

end CFSG.Quasithin.Fan86
