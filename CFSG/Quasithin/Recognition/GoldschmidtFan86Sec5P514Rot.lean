module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514E4

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_x5 (F : FanTree Γ G) (h40 : Fan40 F) (h51a : Fan51a F) (T : Track Γ G) (a : ℤ) :
    ∃ x : G, x ∈ MulAction.stabilizer G (T.line.vert (a + 2)) ∧
      orderOf x = valence Γ (T.line.vert (a + 2)) := by
  obtain ⟨x, ⟨-, hxst⟩, hxord⟩ := h51a h40 T.line (a + 1) 2 le_rfl
    (not_lineSingLe_of_fan40 h40 T.line (by norm_num)) 1 le_rfl (by norm_num)
  have e1 : a + 1 + ((1 : ℕ) : ℤ) = a + 2 := by push_cast; ring
  rw [e1] at hxst hxord
  exact ⟨x, hxst, hxord⟩

theorem iter_periodic {β : Type*} {f : ℕ → β} {c : ℕ} (h : ∀ k, f (k + c) = f k) :
    ∀ n k, f (k + c * n) = f k := by
  intro n
  induction n with
  | zero => intro k; simp
  | succ n ih =>
    intro k
    rw [Nat.mul_succ, ← add_assoc, h, ih]

theorem period_one {β : Type*} {f : ℕ → β} {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (h5 : ∀ k, f (k + 5) = f k) (hm : ∀ k, f (k + m) = f k) : ∀ k, f k = f 0 := by
  have h1 : ∀ k, f (k + 1) = f k := by
    intro k
    obtain ⟨t, s, hts⟩ : ∃ t s : ℕ, m * t = 1 + 5 * s := by
      interval_cases m
      · exact ⟨1, 0, by norm_num⟩
      · exact ⟨3, 1, by norm_num⟩
      · exact ⟨2, 1, by norm_num⟩
      · exact ⟨4, 3, by norm_num⟩
    have e1 := iter_periodic h5 s (k + 1)
    have e2 := iter_periodic hm t k
    rw [show k + 1 + 5 * s = k + m * t by omega] at e1
    rw [← e1, e2]
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [h1, ih]

theorem LblBase.ne_of_rot (F : FanTree Γ G) {z : G} {α o : V} (B : LblBase Γ z α o) {x : G}
    (hord : orderOf x = 5) (hxo : x ∈ MulAction.stabilizer G o) {u u' : V} (hu : Γ.Adj o u)
    (hu' : Γ.Adj o u') (hne : u ≠ u') : Lb z α u ≠ Lb z α u' := by
  intro heq
  have hxo' : x • o = o := MulAction.mem_stabilizer_iff.1 hxo
  have hx5 : x ^ 5 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  obtain ⟨uu, huu⟩ : ∃ uu : ℕ → V, ∀ k, uu k = x ^ k • u := ⟨fun k => x ^ k • u, fun _ => rfl⟩
  have hpo : ∀ k : ℕ, x ^ k • o = o := fun k => MulAction.mem_stabilizer_iff.1 (pow_mem hxo k)
  have hadj : ∀ k, Γ.Adj o (uu k) := fun k => by
    rw [huu]
    have := (F.adj_smul (x ^ k) o u).2 hu
    rwa [hpo] at this
  have hper : ∀ k, uu (k + 5) = uu k := fun k => by
    rw [huu, huu, pow_add, hx5, mul_one]
  have hfree : ∀ d : ℕ, 1 ≤ d → d ≤ 4 → x ^ d • u ≠ u := by
    intro d hd1 hd4 h
    have hcop : (orderOf x).Coprime d := by
      rw [hord]
      interval_cases d <;> norm_num
    exact five_not_fix F (by rw [hcop.orderOf_pow, hord]) (pow_mem hxo d) hu h
  have hlt : ∀ i j : ℕ, i < j → j < 5 → uu i ≠ uu j := by
    intro i j hij hj h
    rw [huu, huu, show j = i + (j - i) by omega, pow_add, mul_smul] at h
    exact hfree (j - i) (by omega) (by omega) (MulAction.injective (x ^ i) h.symm)
  have hinj : ∀ i j : ℕ, i < 5 → j < 5 → uu i = uu j → i = j := by
    intro i j hi hj h
    rcases lt_trichotomy i j with h1 | h1 | h1
    · exact absurd h (hlt i j h1 hj)
    · exact h1
    · exact absurd h.symm (hlt j i h1 hi)
  have hnd : ((List.range 5).map uu).Nodup :=
    List.Nodup.map_on (fun i hi j hj h => hinj i j (List.mem_range.1 hi) (List.mem_range.1 hj) h)
      List.nodup_range
  have hmem := mem_of_five B.v5 hnd (by simp) (fun w hw => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hw
    exact hadj k) u' hu'
  obtain ⟨m, hm5, hmu⟩ := List.mem_map.1 hmem
  rw [List.mem_range] at hm5
  have hm0 : m ≠ 0 := fun h0 => hne (by rw [← hmu, h0, huu]; simp)
  have hex : ∀ k, ∃ g : G, g • α = uu k := fun k => exists_conj_of_adj F B.adj (hadj k)
  have hconj : ∀ k j : ℕ, x ^ k * Lb z α (uu j) * (x ^ k)⁻¹ = Lb z α (uu (j + k)) := fun k j => by
    rw [Lb_conj B.cinv (hex j) (x ^ k), huu, huu, ← mul_smul, ← pow_add, add_comm]
  have hu0 : uu 0 = u := by rw [huu]; simp
  have hfm : ∀ k, Lb z α (uu (k + m)) = Lb z α (uu k) := fun k => by
    have e1 := hconj k m
    have e2 := hconj k 0
    rw [hmu, ← heq] at e1
    rw [hu0] at e2
    calc Lb z α (uu (k + m)) = Lb z α (uu (m + k)) := by rw [add_comm]
      _ = Lb z α (uu (0 + k)) := e1.symm.trans e2
      _ = Lb z α (uu k) := by rw [zero_add]
  have hf5 : ∀ k, Lb z α (uu (k + 5)) = Lb z α (uu k) := fun k => by rw [hper]
  have hconst := period_one (f := fun k => Lb z α (uu k)) (m := m) (by omega) (by omega) hf5 hfm
  have hprod := B.prod5 ((List.range 5).map uu) hnd (by simp) (fun w hw => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hw
    exact hadj k)
  have hrep : ((List.range 5).map uu).map (Lb z α) = List.replicate 5 (Lb z α (uu 0)) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    simp only [List.map_map, List.mem_map, List.mem_range] at hb
    obtain ⟨k, -, rfl⟩ := hb
    exact hconst k
  rw [hrep, List.prod_replicate] at hprod
  have hsq := Lb_mul_self B.cinv (hex 0)
  have hone : Lb z α (uu 0) = 1 := by
    calc Lb z α (uu 0) = Lb z α (uu 0) ^ 5 := by
          rw [show 5 = 2 + 2 + 1 from rfl, pow_add, pow_add, pow_two, hsq, one_mul, one_mul,
            pow_one]
      _ = 1 := hprod
  exact Lb_ne_one B.cinv (hex 0) hone

end P514

end CFSG.Quasithin.Fan86
