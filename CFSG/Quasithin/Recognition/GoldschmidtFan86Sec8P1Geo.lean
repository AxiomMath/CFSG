module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Arc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Arc.vert_eq_of_ends' (hT : Γ.IsTree) {m n : ℕ} (P : Arc Γ m) (Q : Arc Γ n)
    (hmn : m = n) (h0 : P.vert 0 = Q.vert 0) (hn : P.vert m = Q.vert n) :
    ∀ k, k ≤ m → P.vert k = Q.vert k := by
  subst hmn
  exact Arc.vert_eq_of_ends hT P Q h0 hn

theorem Arc.mem_pathSet_iff (hT : Γ.IsTree) {n : ℕ} (Q : Arc Γ n) (v : V) :
    v ∈ pathSet Γ (Q.vert 0) (Q.vert n) ↔ ∃ k, k ≤ n ∧ v = Q.vert k := by
  have hQ : Γ.dist (Q.vert 0) (Q.vert n) = n := Arc.dist_eq hT Q n le_rfl
  constructor
  · intro hv
    have hv' : Γ.dist (Q.vert 0) v + Γ.dist v (Q.vert n) = n := by
      have := hv
      rw [pathSet, hQ] at this
      exact this
    obtain ⟨k, hk⟩ : ∃ k, Γ.dist (Q.vert 0) v = k := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, Γ.dist v (Q.vert n) = r := ⟨_, rfl⟩
    rw [hk, hr] at hv'
    obtain ⟨A, hA0, hAk⟩ := IsTree.exists_arc hT k (Q.vert 0) v hk
    obtain ⟨B, hB0, hBr⟩ := IsTree.exists_arc hT r v (Q.vert n) hr
    have hj : A.vert k = B.vert 0 := by rw [hAk, hB0]
    have hnb : 1 ≤ k → 1 ≤ r → A.vert (k - 1) ≠ B.vert 1 := fun hk1 hr1 h' => by
      have d1 : Γ.dist (A.vert 0) (A.vert (k - 1)) = k - 1 :=
        Arc.dist_eq hT A (k - 1) (by omega)
      have d2 : Γ.dist (B.vert 1) (B.vert r) = r - 1 := by
        have := Arc.dist_vert hT B (i := 1) (j := r) hr1 le_rfl
        exact this
      rw [hA0, h'] at d1
      rw [hBr] at d2
      have := hT.connected.dist_triangle (u := Q.vert 0) (v := B.vert 1) (w := Q.vert n)
      omega
    have hC0 : (Arc.append A B hj hnb).vert 0 = (Q.vert 0) := by
      rw [Arc.append_vert_le _ _ _ _ (Nat.zero_le k), hA0]
    have hCn : (Arc.append A B hj hnb).vert (k + r) = Q.vert n := by
      rw [Arc.append_vert_ge _ _ _ _ (Nat.le_add_right k r), Nat.add_sub_cancel_left, hBr]
    have := Arc.vert_eq_of_ends' hT (Arc.append A B hj hnb) Q hv' hC0 hCn k (Nat.le_add_right k r)
    refine ⟨k, by omega, ?_⟩
    rw [← this, Arc.append_vert_le _ _ _ _ le_rfl, hAk]
  · rintro ⟨k, hk, rfl⟩
    show Γ.dist (Q.vert 0) (Q.vert k) + Γ.dist (Q.vert k) (Q.vert n) =
      Γ.dist (Q.vert 0) (Q.vert n)
    rw [hQ, Arc.dist_vert hT Q (Nat.zero_le k) hk, Arc.dist_vert hT Q hk le_rfl]
    omega

theorem fixes_pathSet (F : FanTree Γ G) {g : G} {u v w : V} (hu : g • u = u) (hv : g • v = v)
    (hw : w ∈ pathSet Γ u v) : g • w = w := by
  obtain ⟨P, hP0, hPn⟩ := IsTree.exists_arc F.isTree _ u v rfl
  have h1 : w ∈ pathSet Γ (P.vert 0) (P.vert (Γ.dist u v)) := by rw [hP0, hPn]; exact hw
  obtain ⟨k, hk, rfl⟩ := (Arc.mem_pathSet_iff F.isTree P w).1 h1
  exact Arc.fixes_of_ends F.isTree F.adj_smul P (by rw [hP0]; exact hu)
    (by rw [hPn]; exact hv) k hk

theorem IsTree.dist_succ_of_ne (hT : Γ.IsTree) {a b b' w : V} (hb : Γ.Adj a b)
    (hb' : Γ.Adj a b') (hne : b ≠ b') (h : Γ.dist w b + 1 = Γ.dist w a) :
    Γ.dist w b' = Γ.dist w a + 1 := by
  rcases IsTree.dist_adj_cases hT (r := w) hb' with h1 | h1
  · exact h1
  · exact absurd (IsTree.eq_of_dist_succ hT (r := w) hb.symm hb'.symm h h1.symm) hne

@[expose] def Arc.act (F : FanTree Γ G) (g : G) {n : ℕ} (P : Arc Γ n) : Arc Γ n where
  vert i := g • P.vert i
  adj i hi := (F.adj_smul g _ _).2 (P.adj i hi)
  nb i hi h := P.nb i hi (MulAction.injective g h)

theorem Arc.act_vert (F : FanTree Γ G) (g : G) {n : ℕ} (P : Arc Γ n) (i : ℕ) :
    (Arc.act F g P).vert i = g • P.vert i := rfl

theorem dist_smul (F : FanTree Γ G) (g : G) (u v : V) :
    Γ.dist (g • u) (g • v) = Γ.dist u v := by
  obtain ⟨P, hP0, hPn⟩ := IsTree.exists_arc_between F.isTree u v
  have := Arc.dist_eq F.isTree (Arc.act F g P) (Γ.dist u v) le_rfl
  rwa [Arc.act_vert, Arc.act_vert, hP0, hPn] at this

theorem smul_vert_eq_of_ends (F : FanTree Γ G) {n : ℕ} (P Q : Arc Γ n) (g : G)
    (h0 : g • P.vert 0 = Q.vert 0) (hn : g • P.vert n = Q.vert n) :
    ∀ k, k ≤ n → g • P.vert k = Q.vert k :=
  Arc.vert_eq_of_ends F.isTree (Arc.act F g P) Q h0 hn

theorem valence_adj_three (F : FanTree Γ G) {u v : V} (hu : valence Γ u = 5) (h : Γ.Adj u v) :
    valence Γ v = 3 := by
  have h1 := F.alternating u v h
  have h2 := F.valence v
  unfold valence at hu ⊢
  omega

theorem valence_adj_five (F : FanTree Γ G) {u v : V} (hu : valence Γ u = 3) (h : Γ.Adj u v) :
    valence Γ v = 5 := by
  have h1 := F.alternating u v h
  have h2 := F.valence v
  unfold valence at hu ⊢
  omega

theorem valence_of_dist (F : FanTree Γ G) :
    ∀ (n : ℕ) {u v : V}, Γ.dist u v = n → valence Γ u = 5 →
      (n % 2 = 0 → valence Γ v = 5) ∧ (n % 2 = 1 → valence Γ v = 3)
  | 0, u, v, h, hu => by
    have huv : u = v := by
      by_contra hne
      exact absurd h (F.isTree.connected.pos_dist_of_ne hne).ne'
    subst huv
    exact ⟨fun _ => hu, fun h => by omega⟩
  | n + 1, u, v, h, hu => by
    obtain ⟨w, hwv, hw⟩ := IsTree.exists_adj_dist_succ F.isTree h
    obtain ⟨ih1, ih2⟩ := valence_of_dist F n hw hu
    exact ⟨fun hn => valence_adj_five F (ih2 (by omega)) hwv,
      fun hn => valence_adj_three F (ih1 (by omega)) hwv⟩

theorem valence_of_dist_even (F : FanTree Γ G) {u v : V} (hu : valence Γ u = 5)
    (hd : Γ.dist u v % 2 = 0) : valence Γ v = 5 :=
  (valence_of_dist F _ rfl hu).1 hd

theorem valence_of_dist_odd (F : FanTree Γ G) {u v : V} (hu : valence Γ u = 5)
    (hd : Γ.dist u v % 2 = 1) : valence Γ v = 3 :=
  (valence_of_dist F _ rfl hu).2 hd

theorem exists_third_neighbor {v a b : V} (hv : valence Γ v = 3) (ha : Γ.Adj v a)
    (hb : Γ.Adj v b) (hab : a ≠ b) :
    ∃ c, Γ.neighborSet v = {a, b, c} ∧ a ≠ c ∧ b ≠ c := by
  have h3 : (Γ.neighborSet v).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hv
  have hsub : ({a, b} : Set V) ⊆ Γ.neighborSet v := by
    intro w hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  have hd : (Γ.neighborSet v \ {a, b}).ncard = 1 := by
    rw [Set.ncard_sdiff hsub, h3, Set.ncard_pair hab]
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 hd
  have hcm : c ∈ Γ.neighborSet v \ {a, b} := by rw [hc]; exact rfl
  obtain ⟨hcv, hcab⟩ := hcm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcab
  refine ⟨c, ?_, fun h => hcab.1 h.symm, fun h => hcab.2 h.symm⟩
  ext w
  constructor
  · intro hw
    by_cases h1 : w = a
    · exact Or.inl h1
    by_cases h2 : w = b
    · exact Or.inr (Or.inl h2)
    have : w ∈ Γ.neighborSet v \ {a, b} := ⟨hw, by simp [h1, h2]⟩
    rw [hc] at this
    exact Or.inr (Or.inr this)
  · rintro (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hcv

end CFSG.Quasithin.Fan86
