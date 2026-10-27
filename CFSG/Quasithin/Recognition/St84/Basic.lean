module

public import CFSG.Quasithin.Recognition.St84.Hyp
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.St84

open scoped Pointwise

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Hyp30.locTrans (h : Hyp30 Γ G) {v a b : V} (ha : Γ.Adj v a) (hb : Γ.Adj v b) :
    ∃ g ∈ MulAction.stabilizer G v, g • a = b := by
  obtain ⟨N, hN⟩ := h.locL2 v
  obtain ⟨g, hg, hgab⟩ := hN.trans a b ha hb
  exact ⟨g, hN.le hg, hgab⟩

theorem Hyp30.exists_adj (h : Hyp30 Γ G) (v : V) : ∃ w, Γ.Adj v w := by
  have hpos : 0 < Nat.card (Γ.neighborSet v) := by
    rw [(h.valency v).2]
    have : 0 < 2 ^ nOf Γ v := pow_pos (by norm_num) _
    omega
  obtain ⟨⟨w, hw⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  exact ⟨w, hw⟩

theorem Hyp30.three_le_card (h : Hyp30 Γ G) (v : V) :
    3 ≤ Nat.card (Γ.neighborSet v) := by
  obtain ⟨hn, hcard⟩ := h.valency v
  rw [hcard]
  have h2 : 2 ≤ 2 ^ nOf Γ v := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ nOf Γ v := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem Hyp30.exists_adj_ne (h : Hyp30 Γ G) (v w : V) : ∃ u, Γ.Adj v u ∧ u ≠ w := by
  by_contra hc
  push Not at hc
  obtain ⟨a, ha⟩ := h.exists_adj v
  have hsub : Γ.neighborSet v ⊆ ({w} : Set V) := fun u hu => by
    simpa using hc u hu
  have hcard : Nat.card (Γ.neighborSet v) ≤ 1 := by
    rw [Nat.card_coe_set_eq]
    calc (Γ.neighborSet v).ncard ≤ ({w} : Set V).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton w)
      _ = 1 := by simp
  have := h.three_le_card v
  omega

theorem Hyp30.finite_neighborSet (h : Hyp30 Γ G) (v : V) :
    (Γ.neighborSet v).Finite := by
  obtain ⟨a, ha⟩ := h.exists_adj v
  obtain ⟨N, hN⟩ := h.locL2 v
  haveI : Finite (MulAction.stabilizer G v) := h.finite_stab v
  haveI : Finite N :=
    Finite.of_injective (Subgroup.inclusion hN.le) (Subgroup.inclusion_injective hN.le)
  refine Finite.of_surjective (fun g : N => (⟨(g : G) • a, ?_⟩ : Γ.neighborSet v)) ?_
  · have hgv : (g : G) • v = v := MulAction.mem_stabilizer_iff.mp (hN.le g.2)
    simpa [hgv] using (h.adj_smul (g : G) v a).2 ha
  · rintro ⟨w, hw⟩
    obtain ⟨g, hg, hgaw⟩ := hN.trans a w ha hw
    exact ⟨⟨g, hg⟩, Subtype.ext hgaw⟩

theorem edgeTransitive_of_locTrans (hconn : Γ.Connected)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (H : Subgroup G) {α β : V} (hαβ : Γ.Adj α β)
    (hα : ∀ a b : V, Γ.Adj α a → Γ.Adj α b →
      ∃ h ∈ H ⊓ MulAction.stabilizer G α, h • a = b)
    (hβ : ∀ a b : V, Γ.Adj β a → Γ.Adj β b →
      ∃ h ∈ H ⊓ MulAction.stabilizer G β, h • a = b) :
    EdgeTransitive Γ H := by
  have hstep : ∀ {a b : V}, Γ.Adj a b →
      (∃ h ∈ H, h • a = α ∨ h • a = β) →
      ∃ h ∈ H, h • b = α ∨ h • b = β := by
    intro a b hab ⟨h, hh, hmap⟩
    have hadj' : Γ.Adj (h • a) (h • b) := (hadj h a b).2 hab
    rcases hmap with hmap | hmap
    · by_cases hb : h • b = β
      · exact ⟨h, hh, Or.inr hb⟩
      · have hadj'' : Γ.Adj α (h • b) := by simpa [hmap] using hadj'
        obtain ⟨k, hk, hkmap⟩ := hα (h • b) β hadj'' hαβ
        exact ⟨k * h, H.mul_mem hk.1 hh, Or.inr (by rw [mul_smul, hkmap])⟩
    · by_cases ha : h • b = α
      · exact ⟨h, hh, Or.inl ha⟩
      · have hadj'' : Γ.Adj β (h • b) := by simpa [hmap] using hadj'
        obtain ⟨k, hk, hkmap⟩ := hβ (h • b) α hadj'' hαβ.symm
        exact ⟨k * h, H.mul_mem hk.1 hh, Or.inl (by rw [mul_smul, hkmap])⟩
  have hvertex : ∀ {a b : V} (p : Γ.Walk a b),
      (∃ h ∈ H, h • a = α ∨ h • a = β) →
      ∃ h ∈ H, h • b = α ∨ h • b = β := by
    intro a b p
    induction p using SimpleGraph.Walk.rec with
    | nil => exact id
    | cons h p ih => exact fun ha => ih (hstep h ha)
  have hedge : ∀ {u v : V}, Γ.Adj u v →
      ∃ h ∈ H, (h • u = α ∧ h • v = β) ∨ (h • u = β ∧ h • v = α) := by
    intro u v huv
    obtain ⟨p⟩ := hconn α u
    obtain ⟨h, hh, hmap⟩ := hvertex p ⟨1, H.one_mem, Or.inl (one_smul _ _)⟩
    have hadj' : Γ.Adj (h • u) (h • v) := (hadj h u v).2 huv
    rcases hmap with hmap | hmap
    · by_cases hv : h • v = β
      · exact ⟨h, hh, Or.inl ⟨hmap, hv⟩⟩
      · have hadj'' : Γ.Adj α (h • v) := by simpa [hmap] using hadj'
        obtain ⟨k, hk, hkmap⟩ := hα (h • v) β hadj'' hαβ
        exact ⟨k * h, H.mul_mem hk.1 hh,
          Or.inl ⟨by rw [mul_smul, hmap, MulAction.mem_stabilizer_iff.mp hk.2],
            by rw [mul_smul, hkmap]⟩⟩
    · by_cases hv : h • v = α
      · exact ⟨h, hh, Or.inr ⟨hmap, hv⟩⟩
      · have hadj'' : Γ.Adj β (h • v) := by simpa [hmap] using hadj'
        obtain ⟨k, hk, hkmap⟩ := hβ (h • v) α hadj'' hαβ.symm
        exact ⟨k * h, H.mul_mem hk.1 hh,
          Or.inr ⟨by rw [mul_smul, hmap, MulAction.mem_stabilizer_iff.mp hk.2],
            by rw [mul_smul, hkmap]⟩⟩
  intro u v u' v' huv hu'v'
  obtain ⟨h₁, hh₁, hor₁⟩ := hedge huv
  obtain ⟨h₂, hh₂, hor₂⟩ := hedge hu'v'
  refine ⟨h₂⁻¹ * h₁, H.mul_mem (H.inv_mem hh₂) hh₁, ?_⟩
  rcases hor₁ with ⟨h₁u, h₁v⟩ | ⟨h₁u, h₁v⟩ <;>
    rcases hor₂ with ⟨h₂u, h₂v⟩ | ⟨h₂u, h₂v⟩
  · left
    refine ⟨?_, ?_⟩ <;> simp only [mul_smul]
    · rw [h₁u, ← h₂u, inv_smul_smul]
    · rw [h₁v, ← h₂v, inv_smul_smul]
  · right
    refine ⟨?_, ?_⟩ <;> simp only [mul_smul]
    · rw [h₁u, ← h₂v, inv_smul_smul]
    · rw [h₁v, ← h₂u, inv_smul_smul]
  · right
    refine ⟨?_, ?_⟩ <;> simp only [mul_smul]
    · rw [h₁u, ← h₂v, inv_smul_smul]
    · rw [h₁v, ← h₂u, inv_smul_smul]
  · left
    refine ⟨?_, ?_⟩ <;> simp only [mul_smul]
    · rw [h₁u, ← h₂u, inv_smul_smul]
    · rw [h₁v, ← h₂v, inv_smul_smul]

theorem eq_bot_of_normalizer_edgeTransitive_of_faithful
    (hfaith : ∀ g : G, (∀ v : V, g • v = v) → g = 1) (hnbr : ∀ v : V, ∃ w, Γ.Adj v w)
    {X : Subgroup G} {α β : V} (hαβ : Γ.Adj α β)
    (hX : X ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hN : EdgeTransitive Γ (Subgroup.normalizer (X : Set G))) : X = ⊥ := by
  have hfix : ∀ u ∈ X, u • α = α ∧ u • β = β := by
    intro u hu
    exact ⟨MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hX hu)).1,
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hX hu)).2⟩
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  apply hfaith
  intro w
  obtain ⟨w', hw'⟩ := hnbr w
  obtain ⟨n, hn, hor⟩ := hN α β w w' hαβ hw'
  have hconj : n⁻¹ * u * n ∈ X := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) u).1 hu
    simpa using this
  obtain ⟨h1, h2⟩ := hfix _ hconj
  have hun : u * n = n * (n⁻¹ * u * n) := by simp only [mul_assoc, mul_inv_cancel_left]
  have key : ∀ x y : V, n • α = x → n • β = y → u • x = x ∧ u • y = y := by
    rintro x y rfl rfl
    constructor
    · rw [← mul_smul, hun, mul_smul, h1]
    · rw [← mul_smul, hun, mul_smul, h2]
  rcases hor with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact (key _ _ ha hb).1
  · exact (key _ _ ha hb).2

theorem PreservesParts.not_adj_smul (hP : PreservesParts Γ G) (g : G) (v : V) :
    ¬ Γ.Adj v (g • v) := by
  intro hAdj
  have hdist : Γ.dist v (g • v) = 1 := dist_eq_one_iff_adj.mpr hAdj
  have hev := hP g v
  rw [hdist] at hev
  norm_num at hev

theorem eq_bot_of_normalizer_trans_of_faithful (hconn : Γ.Connected)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hfaith : ∀ g : G, (∀ v : V, g • v = v) → g = 1) (hnbr : ∀ v : V, ∃ w, Γ.Adj v w)
    {X : Subgroup G} {α β : V} (hαβ : Γ.Adj α β)
    (hX : X ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hα : ∀ a b : V, Γ.Adj α a → Γ.Adj α b →
      ∃ g ∈ Subgroup.normalizer (X : Set G) ⊓ MulAction.stabilizer G α, g • a = b)
    (hβ : ∀ a b : V, Γ.Adj β a → Γ.Adj β b →
      ∃ g ∈ Subgroup.normalizer (X : Set G) ⊓ MulAction.stabilizer G β, g • a = b) :
    X = ⊥ :=
  eq_bot_of_normalizer_edgeTransitive_of_faithful hfaith hnbr hαβ hX
    (edgeTransitive_of_locTrans hconn hadj (Subgroup.normalizer (X : Set G)) hαβ hα hβ)

theorem eq_bot_of_normalizer_trans (h : Hyp30 Γ G) {X : Subgroup G} {α β : V}
    (hαβ : Γ.Adj α β)
    (hX : X ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hα : ∀ a b : V, Γ.Adj α a → Γ.Adj α b →
      ∃ g ∈ Subgroup.normalizer (X : Set G) ⊓ MulAction.stabilizer G α, g • a = b)
    (hβ : ∀ a b : V, Γ.Adj β a → Γ.Adj β b →
      ∃ g ∈ Subgroup.normalizer (X : Set G) ⊓ MulAction.stabilizer G β, g • a = b) :
    X = ⊥ :=
  eq_bot_of_normalizer_trans_of_faithful h.isTree.connected h.adj_smul h.faithful h.exists_adj
    hαβ hX hα hβ

theorem exists_mul_of_edgeTransitive (hadj : ∀ (g : G) (u v : V),
    Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hP : PreservesParts Γ G) {α β : V} (hαβ : Γ.Adj α β) {N : Subgroup G}
    (hN : EdgeTransitive Γ N) (g : G) :
    ∃ n ∈ N, ∃ k ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β, g = n * k := by
  have hgαβ : Γ.Adj (g • α) (g • β) := (hadj g α β).2 hαβ
  obtain ⟨n, hn, hor⟩ := hN α β (g • α) (g • β) hαβ hgαβ
  rcases hor with ⟨hnα, hnβ⟩ | ⟨hnα, hnβ⟩
  · refine ⟨n, hn, n⁻¹ * g, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, by group⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hnα, inv_smul_smul]
    · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hnβ, inv_smul_smul]
  · exfalso
    have hswap : (n⁻¹ * g) • α = β := by rw [mul_smul, ← hnβ, inv_smul_smul]
    exact hP.not_adj_smul (n⁻¹ * g) α (by rw [hswap]; exact hαβ)

theorem sup_eq_top_of_edgeTransitive (hadj : ∀ (g : G) (u v : V),
    Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hP : PreservesParts Γ G) {α β : V} (hαβ : Γ.Adj α β) {N : Subgroup G}
    (hN : EdgeTransitive Γ N) :
    N ⊔ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨n, hn, k, hk, rfl⟩ := exists_mul_of_edgeTransitive hadj hP hαβ hN g
  exact Subgroup.mul_mem_sup hn hk

theorem IsTree.even_dist_add_dist_add_dist (hT : Γ.IsTree) (u v w : V) :
    Even (Γ.dist u v + Γ.dist v w + Γ.dist u w) := by
  have key : ∀ {a b : V} (p : Γ.Walk a b),
      Even (Γ.dist u b + (Γ.dist u a + p.length)) := by
    intro a b p
    induction p using SimpleGraph.Walk.rec with
    | nil => simp
    | cons h p ih =>
      rw [Walk.length_cons]
      rcases IsTree.dist_adj_cases hT (r := u) h with hcase | hcase
      · rcases ih with ⟨k, hk⟩
        exact ⟨k, by omega⟩
      · rcases ih with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
  obtain ⟨p, -, hp⟩ := (hT.connected v w).exists_path_of_dist
  have := key p
  rw [hp] at this
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem even_add_iff_left {a b : ℕ} (ha : Even a) : Even (a + b) ↔ Even b := by
  constructor
  · rintro ⟨k, hk⟩
    rcases ha with ⟨l, hl⟩
    exact ⟨k - l, by omega⟩
  · rintro ⟨k, hk⟩
    rcases ha with ⟨l, hl⟩
    exact ⟨l + k, by omega⟩

theorem even_add_iff_right {a b : ℕ} (hb : Even b) : Even (a + b) ↔ Even a := by
  rw [Nat.add_comm]
  exact even_add_iff_left hb

theorem IsTree.dist_smul (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (g : G) (u v : V) : Γ.dist (g • u) (g • v) = Γ.dist u v := by
  let hf : Γ →g Γ := ⟨fun x => g • x, fun {a b} h => (hadj g a b).2 h⟩
  let hf' : Γ →g Γ := ⟨fun x => g⁻¹ • x, fun {a b} h => by
    exact (hadj g (g⁻¹ • a) (g⁻¹ • b)).1 (by simpa using h)⟩
  refine le_antisymm ?_ ?_
  · obtain ⟨p, -, hp⟩ := (hT.connected u v).exists_path_of_dist
    have hlen : (p.map hf).length = p.length := Walk.length_map hf p
    have h1 : Γ.dist (hf u) (hf v) ≤ (p.map hf).length := dist_le (p.map hf)
    have h1' : Γ.dist (g • u) (g • v) ≤ (p.map hf).length := by
      convert h1 using 2 <;> rfl
    calc Γ.dist (g • u) (g • v) ≤ (p.map hf).length := h1'
      _ = p.length := hlen
      _ = Γ.dist u v := hp
  · obtain ⟨p, -, hp⟩ := (hT.connected (g • u) (g • v)).exists_path_of_dist
    have hlen : (p.map hf').length = p.length := Walk.length_map hf' p
    have h1 : Γ.dist (hf' (g • u)) (hf' (g • v)) ≤ (p.map hf').length := dist_le (p.map hf')
    rw [hlen, hp] at h1
    have h1' : Γ.dist u v ≤ Γ.dist (g • u) (g • v) := by
      convert h1 using 2 <;> dsimp only [hf'] <;> simp
    exact h1'

theorem IsTree.even_dist_smul_iff (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (g : G) (u v : V) :
    Even (Γ.dist u (g • u)) ↔ Even (Γ.dist v (g • v)) := by
  have h1 := IsTree.even_dist_add_dist_add_dist hT u (g • u) (g • v)
  have h2 := IsTree.even_dist_add_dist_add_dist hT u (g • v) v
  rw [IsTree.dist_smul hT hadj g u v] at h1
  rw [dist_comm (u := g • v) (v := v)] at h2
  have h1' : Even (Γ.dist u (g • u) + (Γ.dist u v + Γ.dist u (g • v))) := by
    simpa [Nat.add_assoc] using h1
  have h2' : Even ((Γ.dist u v + Γ.dist u (g • v)) + Γ.dist v (g • v)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2
  constructor
  · intro hgu
    have hBC : Even (Γ.dist u v + Γ.dist u (g • v)) := (even_add_iff_left hgu).mp h1'
    exact (even_add_iff_left hBC).mp h2'
  · intro hgv
    have hBC : Even (Γ.dist u v + Γ.dist u (g • v)) := (even_add_iff_right hgv).mp h2'
    exact (even_add_iff_right hBC).mp h1'

def evenSubgroup (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) (α : V) :
    Subgroup G where
  carrier := {g | Even (Γ.dist α (g • α))}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change Even (Γ.dist α ((g * h) • α))
    have h1 := IsTree.even_dist_add_dist_add_dist hT α (g • α) ((g * h) • α)
    have hdist : Γ.dist (g • α) ((g * h) • α) = Γ.dist α (h • α) := by
      simpa [mul_smul] using IsTree.dist_smul hT hadj g α (h • α)
    rw [hdist] at h1
    have h1' : Even ((Γ.dist α (g • α) + Γ.dist α (h • α)) +
        Γ.dist α ((g * h) • α)) := by
      simpa [Nat.add_assoc] using h1
    have hBC : Even (Γ.dist α (g • α) + Γ.dist α (h • α)) := by
      rcases hg with ⟨k, hk⟩
      rcases hh with ⟨l, hl⟩
      exact ⟨k + l, by omega⟩
    exact (even_add_iff_left hBC).mp h1'
  inv_mem' := by
    intro g hg
    change Even (Γ.dist α (g⁻¹ • α))
    have hdist : Γ.dist α (g⁻¹ • α) = Γ.dist α (g • α) := by
      have h := IsTree.dist_smul hT hadj g (g⁻¹ • α) α
      rw [smul_inv_smul] at h
      have h' : Γ.dist α (g • α) = Γ.dist α (g⁻¹ • α) := by simpa [dist_comm] using h
      exact h'.symm
    rw [hdist]
    exact hg

theorem evenSubgroup_normal (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) (α : V) :
    (evenSubgroup (G := G) hT hadj α).Normal := by
  refine ⟨fun g hg a => ?_⟩
  change Even (Γ.dist α ((a * g * a⁻¹) • α))
  have hv : (a * g * a⁻¹) • α = a • (g • (a⁻¹ • α)) := by simp [mul_smul]
  have hd := IsTree.dist_smul hT hadj a (a⁻¹ • α) (g • (a⁻¹ • α))
  rw [smul_inv_smul] at hd
  rw [hv, hd]
  exact (IsTree.even_dist_smul_iff hT hadj g α (a⁻¹ • α)).mp hg

theorem Hyp30.preservesParts (h : Hyp30 Γ G) : PreservesParts Γ G := by
  classical
  let α : V := h.isTree.connected.nonempty.some
  obtain ⟨β, hαβ⟩ := h.exists_adj α
  let H := evenSubgroup (G := G) h.isTree h.adj_smul α
  have hHnormal : H.Normal := evenSubgroup_normal h.isTree h.adj_smul α
  have hHα : H ⊓ MulAction.stabilizer G α = MulAction.stabilizer G α := by
    refine le_antisymm inf_le_right ?_
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨by
      change Even (Γ.dist α (x • α))
      rw [MulAction.mem_stabilizer_iff.mp hx, dist_self]
      exact ⟨0, rfl⟩, hx⟩
  have hHβ : H ⊓ MulAction.stabilizer G β = MulAction.stabilizer G β := by
    refine le_antisymm inf_le_right ?_
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨by
      change Even (Γ.dist α (x • α))
      exact (IsTree.even_dist_smul_iff h.isTree h.adj_smul x α β).mpr (by
        change Even (Γ.dist β (x • β))
        rw [MulAction.mem_stabilizer_iff.mp hx, dist_self]
        exact ⟨0, rfl⟩), hx⟩
  have htransα : ∀ a b : V, Γ.Adj α a → Γ.Adj α b →
      ∃ g ∈ H ⊓ MulAction.stabilizer G α, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hg, hgab⟩ := h.locTrans ha hb
    exact ⟨g, by rw [hHα]; exact hg, hgab⟩
  have htransβ : ∀ a b : V, Γ.Adj β a → Γ.Adj β b →
      ∃ g ∈ H ⊓ MulAction.stabilizer G β, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hg, hgab⟩ := h.locTrans ha hb
    exact ⟨g, by rw [hHβ]; exact hg, hgab⟩
  have hedge : EdgeTransitive Γ H :=
    edgeTransitive_of_locTrans h.isTree.connected h.adj_smul H hαβ htransα htransβ
  have htop : H = ⊤ := h.minimal H hHnormal hedge
  intro g v
  have hg : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
  exact (IsTree.even_dist_smul_iff h.isTree h.adj_smul g α v).mp hg

theorem stabilizer_smul_eq_conjSub (g : G) (v : V) :
    MulAction.stabilizer G (g • v) = conjSub g (MulAction.stabilizer G v) :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g v

theorem conjSub_fixSet (g : G) (S : Set V) :
    conjSub g (fixSet G S) = fixSet G (g • S) := by
  ext x
  rw [mem_conjSub, Fan86.mem_fixSet, Fan86.mem_fixSet]
  constructor
  · intro h v hv
    rw [Set.mem_smul_set] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    calc x • (g • w) = g • ((g⁻¹ * x * g) • w) := by simp [mul_smul]
      _ = g • w := by rw [h w hw]
  · intro h v hv
    calc (g⁻¹ * x * g) • v = g⁻¹ • (x • (g • v)) := by simp [mul_smul]
      _ = g⁻¹ • (g • v) := by rw [h (g • v) (Set.smul_mem_smul_set hv)]
      _ = v := by simp

theorem pCoreOf_le_of_isSylowTwoOf {G : Type*} [Group G] {H S : Subgroup G} [Finite H]
    (hS : IsSylowTwoOf S H) : pCoreOf 2 H ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 H := hS'.toSylow hS.2.2
  have : (CFSG.Open.pCore 2 H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : CFSG.Open.pCore 2 H ≤ (P : Subgroup H) :=
    IsPGroup.le_sylow_of_normal (CFSG.LieType.BorelTits.pCore_isPGroup 2) P
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  have h3 : (P : Subgroup H).map H.subtype = S := by
    change (S.subgroupOf H).map H.subtype = S
    rw [Subgroup.map_subgroupOf_eq_of_le hS.1]
  change Subgroup.map H.subtype (CFSG.Open.pCore 2 H) ≤ S
  rw [← h3]
  exact h2

theorem exists_isSylowTwoOf_ge_of_finite {G : Type*} [Group G] {J X : Subgroup G}
    [Finite J] (hX : IsPGroup 2 X) (hXJ : X ≤ J) :
    ∃ S : Subgroup G, IsSylowTwoOf S J ∧ X ≤ S := by
  have hX' : IsPGroup 2 (X.subgroupOf J) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXJ).symm
  obtain ⟨P, hP⟩ := hX'.exists_le_sylow
  refine ⟨P.map J.subtype, ⟨Subgroup.map_subtype_le _, P.isPGroup'.map J.subtype, ?_⟩, ?_⟩
  · have h : (P.map J.subtype : Subgroup G).subgroupOf J = (P : Subgroup ↥J) :=
      Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
    rw [h]
    exact Sylow.not_dvd_index P
  · intro x hx
    exact ⟨⟨x, hXJ hx⟩, hP (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩

theorem conjSub_eq_of_mem {G : Type*} [Group G] {g : G} {H : Subgroup G} (hg : g ∈ H) :
    conjSub g H = H := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro h
    have := H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
    simpa [mul_assoc] using this
  · intro hx
    have h' : g⁻¹ * x * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg
    simpa using h'

namespace Setup

variable (X : Setup Γ G)

theorem adj (i : ℤ) : Γ.Adj (X.vert i) (X.vert (i + 1)) := X.line.adj i

theorem vert_injective : Function.Injective X.vert :=
  Line.vert_injective X.hyp.isTree X.line

theorem pow_smul_vert (n : ℕ) (i : ℤ) :
    X.τ ^ n • X.vert i = X.vert (i + 2 * (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, X.trans]
    congr 1
    push_cast
    ring

theorem zpow_smul_vert (m i : ℤ) :
    X.τ ^ m • X.vert i = X.vert (i + 2 * m) := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · simpa using Setup.pow_smul_vert X n i
  · rw [zpow_neg]
    have h := Setup.pow_smul_vert X n (i - 2 * (n : ℤ))
    rw [show i - 2 * (n : ℤ) + 2 * (n : ℤ) = i by ring] at h
    simp only [zpow_natCast]
    rw [← h, inv_smul_smul]
    congr 1
    push_cast
    ring

theorem Gi_add (m i : ℤ) :
    X.Gi (i + 2 * m) = conjSub (X.τ ^ m) (X.Gi i) := by
  unfold Setup.Gi
  rw [← X.zpow_smul_vert m i, stabilizer_smul_eq_conjSub]

theorem Q_add (m i : ℤ) :
    X.Q (i + 2 * m) = conjSub (X.τ ^ m) (X.Q i) := by
  unfold Setup.Q
  rw [X.Gi_add, pCoreOf_conjSub]

theorem L_add (m i : ℤ) :
    X.L (i + 2 * m) = conjSub (X.τ ^ m) (X.L i) := by
  unfold Setup.L
  rw [X.Gi_add, ← conjSub_oTwoPrime]

theorem smul_Icc_vert (m a c : ℤ) :
    (X.τ ^ m) • (X.vert '' Set.Icc a c) =
      X.vert '' Set.Icc (a + 2 * m) (c + 2 * m) := by
  ext x
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    rw [Set.mem_Icc] at hi
    refine ⟨i + 2 * m, ?_, ?_⟩
    · rw [Set.mem_Icc]
      omega
    · exact (X.zpow_smul_vert m i).symm
  · rintro ⟨j, hj, rfl⟩
    rw [Set.mem_Icc] at hj
    refine ⟨X.vert (j - 2 * m), ?_, ?_⟩
    · rw [Set.mem_image]
      exact ⟨j - 2 * m, by rw [Set.mem_Icc]; omega, rfl⟩
    · change X.τ ^ m • X.vert (j - 2 * m) = X.vert j
      rw [X.zpow_smul_vert]
      congr 1
      ring

theorem arcStab_add (m a c : ℤ) :
    X.arcStab (a + 2 * m) (c + 2 * m) = conjSub (X.τ ^ m) (X.arcStab a c) := by
  unfold Setup.arcStab
  rw [← X.smul_Icc_vert m a c, conjSub_fixSet]

theorem neighborSet_add (m i : ℤ) :
    Γ.neighborSet (X.vert (i + 2 * m)) =
      (X.τ ^ m) • Γ.neighborSet (X.vert i) := by
  rw [← X.zpow_smul_vert m i]
  ext w
  rw [Set.mem_smul_set]
  constructor
  · intro hw
    refine ⟨(X.τ ^ m)⁻¹ • w, ?_, by simp⟩
    have := (X.hyp.adj_smul ((X.τ ^ m)⁻¹) ((X.τ ^ m) • X.vert i) w).2 hw
    simpa using this
  · rintro ⟨a, ha, rfl⟩
    exact (X.hyp.adj_smul (X.τ ^ m) (X.vert i) a).2 ha

theorem n_add (m i : ℤ) : X.n (i + 2 * m) = X.n i := by
  unfold Setup.n nOf
  have hcard : Nat.card (Γ.neighborSet (X.vert (i + 2 * m))) =
      Nat.card (Γ.neighborSet (X.vert i)) := by
    rw [X.neighborSet_add, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_smul_set]
  rw [hcard]

theorem iSup_sylow_center_conj {H : Type*} [Group H] (g : H) (K : Subgroup H) :
    (⨆ (P : Subgroup H) (_ : IsSylowTwoOf P (conjSub g K)),
      centerOf P ⊓ pCoreOf 2 (conjSub g K)) =
    conjSub g (⨆ (P : Subgroup H) (_ : IsSylowTwoOf P K),
      centerOf P ⊓ pCoreOf 2 K) := by
  have hcenter : ∀ P : Subgroup H,
      centerOf (conjSub g P) = conjSub g (centerOf P) := by
    intro P
    unfold centerOf
    rw [conjSub_inf, conjSub_centralizer]
  have hQ : pCoreOf 2 (conjSub g K) = conjSub g (pCoreOf 2 K) := pCoreOf_conjSub g K
  apply le_antisymm
  · apply iSup_le
    intro P
    apply iSup_le
    intro hP
    let P' : Subgroup H := conjSub g⁻¹ P
    have hP'₀ : IsSylowTwoOf P' K := by
      have := B6.isSylowTwoOf_conjSub hP (g := g⁻¹)
      change IsSylowTwoOf (conjSub g⁻¹ P) (conjSub g⁻¹ (conjSub g K)) at this
      dsimp only [P'] at this ⊢
      simpa [conjSub_conjSub_inv] using this
    have hPcong : conjSub g P' = P := by
      dsimp only [P']
      rw [conjSub_inv_conjSub]
    have hcen : centerOf P = conjSub g (centerOf P') := by
      rw [← hPcong, hcenter]
    rw [hcen, hQ, ← conjSub_inf]
    exact conjSub_mono g (le_iSup₂_of_le P' hP'₀ le_rfl)
  · have hstep : ∀ (P : Subgroup H) (hP : IsSylowTwoOf P K),
        conjSub g (centerOf P ⊓ pCoreOf 2 K) ≤
          (⨆ (P : Subgroup H) (_ : IsSylowTwoOf P (conjSub g K)),
            centerOf P ⊓ pCoreOf 2 (conjSub g K)) := by
      intro P hP
      have hSP : IsSylowTwoOf (conjSub g P) (conjSub g K) :=
        B6.isSylowTwoOf_conjSub hP g
      rw [conjSub_inf, ← hcenter P, ← hQ]
      exact le_iSup₂_of_le (conjSub g P) hSP le_rfl
    calc conjSub g (⨆ (P : Subgroup H) (_ : IsSylowTwoOf P K),
          centerOf P ⊓ pCoreOf 2 K)
        = conjSub g (⨆ P, ⨆ (_ : IsSylowTwoOf P K), centerOf P ⊓ pCoreOf 2 K) := rfl
      _ = ⨆ P, conjSub g (⨆ (_ : IsSylowTwoOf P K), centerOf P ⊓ pCoreOf 2 K) :=
          conjSub_iSup g _
      _ = ⨆ P, ⨆ (_ : IsSylowTwoOf P K),
          conjSub g (centerOf P ⊓ pCoreOf 2 K) := by
          simp only [conjSub_iSup]
      _ ≤ _ := iSup_le fun P => iSup_le fun hP => hstep P hP

theorem Z_add (m i : ℤ) :
    X.Z (i + 2 * m) = conjSub (X.τ ^ m) (X.Z i) := by
  change (⨆ (P : Subgroup G) (_ : IsSylowTwoOf P (X.Gi (i + 2 * m))),
      centerOf P ⊓ X.Q (i + 2 * m)) =
    conjSub (X.τ ^ m) (⨆ (P : Subgroup G) (_ : IsSylowTwoOf P (X.Gi i)),
      centerOf P ⊓ X.Q i)
  rw [X.Gi_add, X.Q_add]
  simp only [Setup.Q]
  rw [← pCoreOf_conjSub]
  exact iSup_sylow_center_conj (X.τ ^ m) (X.Gi i)

theorem K_le_GT : X.K ≤ X.GT := by
  intro k hk
  rw [Setup.GT, Fan86.mem_fixSet]
  rintro v ⟨i, rfl⟩
  exact X.K_fix k hk i

theorem K_le_Gi (i : ℤ) : X.K ≤ X.Gi i := by
  intro k hk
  exact MulAction.mem_stabilizer_iff.mpr (X.K_fix k hk i)

theorem K_le_inf : X.K ≤ X.Gi 0 ⊓ X.Gi 1 := le_inf (X.K_le_Gi 0) (X.K_le_Gi 1)

theorem Z_le_Q (i : ℤ) : X.Z i ≤ X.Q i := by
  unfold Setup.Z
  exact iSup_le fun _ => iSup_le fun _ => inf_le_right

theorem Q_le_Gi (i : ℤ) : X.Q i ≤ X.Gi i :=
  CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi i)

theorem Z_le_Gi (i : ℤ) : X.Z i ≤ X.Gi i := (X.Z_le_Q i).trans (X.Q_le_Gi i)

theorem L_le_Gi (i : ℤ) : X.L i ≤ X.Gi i := oTwoPrime_le (X.Gi i)

theorem Z_normal (i : ℤ) : ∀ g ∈ X.Gi i, conjSub g (X.Z i) = X.Z i := by
  intro g hg
  have h := iSup_sylow_center_conj g (X.Gi i)
  rw [conjSub_eq_of_mem hg] at h
  change X.Z i = conjSub g (X.Z i) at h
  exact h.symm

theorem Z_le_center (i : ℤ) : X.Z i ≤ centerOf (X.Q i) := by
  haveI hfin : Finite (X.Gi i) := X.hyp.finite_stab (X.vert i)
  unfold Setup.Z
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  intro x hx
  obtain ⟨hxP, hxQ⟩ := Subgroup.mem_inf.mp hx
  have hQP : X.Q i ≤ P := pCoreOf_le_of_isSylowTwoOf hP
  refine Subgroup.mem_inf.mpr ⟨hxQ, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp hxP.2) y (hQP hy)

theorem Z_commute (i : ℤ) : ∀ x ∈ X.Z i, ∀ y ∈ X.Z i, x * y = y * x := by
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.mp (X.Z_le_center i hx).2) y (X.Z_le_Q i hy)).symm

theorem Z_ne_bot_of (i : ℤ) (hQ : X.Q i ≠ ⊥) : X.Z i ≠ ⊥ := by
  haveI hfin : Finite (X.Gi i) := X.hyp.finite_stab (X.vert i)
  have hQp : IsPGroup 2 (X.Q i) := by
    unfold Setup.Q
    exact (CFSG.pCore_isPGroup (p := 2) (G := X.Gi i)).map (X.Gi i).subtype
  obtain ⟨P, hP, hQP⟩ :=
    exists_isSylowTwoOf_ge_of_finite (J := X.Gi i) hQp (X.Q_le_Gi i)
  have hQnorm : X.Gi i ≤ Subgroup.normalizer (X.Q i : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i)
  have hQnP : P ≤ Subgroup.normalizer (X.Q i : Set G) := hP.1.trans hQnorm
  have hNnormal : ((X.Q i).subgroupOf P).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQnP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hPfin : Finite P :=
    Finite.of_injective (Subgroup.inclusion hP.1) (Subgroup.inclusion_injective hP.1)
  haveI hPnil : Group.IsNilpotent P := hP.2.1.isNilpotent
  have hNne : (X.Q i).subgroupOf P ≠ ⊥ := by
    intro hbot
    apply hQ
    rw [eq_bot_iff]
    intro x hx
    have hxP : (⟨x, hQP hx⟩ : P) ∈ (X.Q i).subgroupOf P := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hbot, Subgroup.mem_bot] at hxP
    exact Subtype.ext_iff.mp hxP
  have hcenter := Group.IsNilpotent.inf_center_ne_bot_of_normal hNne
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter
  have hyQ : (y : G) ∈ X.Q i :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hy).1
  have hyZ : (y : G) ∈ centerOf P := by
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' := Subgroup.mem_center_iff.mp ((Subgroup.mem_inf.mp hy).2) ⟨z, hz⟩
    exact congrArg Subtype.val hz'
  intro hZbot
  have hle : centerOf P ⊓ X.Q i ≤ X.Z i := le_iSup₂_of_le P hP le_rfl
  have hterm : centerOf P ⊓ X.Q i = ⊥ := le_bot_iff.mp (hZbot ▸ hle)
  have hyterm : (y : G) ∈ centerOf P ⊓ X.Q i := Subgroup.mem_inf.mpr ⟨hyZ, hyQ⟩
  rw [hterm, Subgroup.mem_bot] at hyterm
  exact hy1 (Subtype.ext (Subtype.ext hyterm))

theorem arcStab_self (m : ℤ) : X.arcStab m m = X.Gi m := by
  unfold Setup.arcStab Setup.Gi
  have himage : X.vert '' Set.Icc m m = {X.vert m} := by
    ext x
    simp [Set.mem_Icc]
  rw [himage]
  ext g
  rw [Fan86.mem_fixSet, MulAction.mem_stabilizer_iff]
  simp

theorem arcStab_anti {m m' r r' : ℤ} (hm : m ≤ m') (hr : r' ≤ r) :
    X.arcStab m r ≤ X.arcStab m' r' := by
  unfold Setup.arcStab
  apply Fan86.fixSet_anti
  rintro _ ⟨k, hk, rfl⟩
  rw [Set.mem_Icc] at hk
  exact ⟨k, ⟨by omega, by omega⟩, rfl⟩

theorem arcStab_eq_inf {m r : ℤ} (hmr : m ≤ r) :
    X.arcStab m r = X.Gi m ⊓ X.Gi r := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · rw [← X.arcStab_self m]
      exact X.arcStab_anti le_rfl hmr
    · rw [← X.arcStab_self r]
      exact X.arcStab_anti hmr le_rfl
  · intro g hg
    obtain ⟨hgm, hgr⟩ := Subgroup.mem_inf.mp hg
    unfold Setup.arcStab
    rw [Fan86.mem_fixSet]
    rintro _ ⟨k, hk, rfl⟩
    rw [Set.mem_Icc] at hk
    exact Line.fixes_between X.hyp.isTree X.hyp.adj_smul X.line hk.1 hk.2
      (MulAction.mem_stabilizer_iff.mp hgm) (MulAction.mem_stabilizer_iff.mp hgr)

theorem mem_Gi_of_between {g : G} {m r k : ℤ} (hm : g ∈ X.Gi m) (hr : g ∈ X.Gi r)
    (h1 : m ≤ k) (h2 : k ≤ r) : g ∈ X.Gi k := by
  have hg : g ∈ X.arcStab m r := by
    rw [X.arcStab_eq_inf (le_trans h1 h2)]
    exact Subgroup.mem_inf.mpr ⟨hm, hr⟩
  unfold Setup.arcStab at hg
  rw [Fan86.mem_fixSet] at hg
  exact MulAction.mem_stabilizer_iff.mpr (hg (X.vert k) ⟨k, ⟨h1, h2⟩, rfl⟩)

theorem GT_le_arcStab (m r : ℤ) : X.GT ≤ X.arcStab m r := by
  unfold Setup.GT Setup.arcStab
  exact Fan86.fixSet_anti (Set.image_subset_range X.vert (Set.Icc m r))

theorem GT_le_Gi (i : ℤ) : X.GT ≤ X.Gi i := by
  rw [← X.arcStab_self i]
  exact X.GT_le_arcStab i i

theorem le_Gi_of_le_add {i : ℤ} {m : ℕ} (h : X.Z i ≤ X.Gi (i + (m : ℤ))) :
    ∀ k : ℤ, i ≤ k → k ≤ i + (m : ℤ) → X.Z i ≤ X.Gi k := by
  intro k h1 h2 z hz
  exact X.mem_Gi_of_between (X.Z_le_Gi i hz) (h hz) h1 h2

theorem le_Gi_of_sub_le {i : ℤ} {m : ℕ} (h : X.Z i ≤ X.Gi (i - (m : ℤ))) :
    ∀ k : ℤ, i - (m : ℤ) ≤ k → k ≤ i → X.Z i ≤ X.Gi k := by
  intro k h1 h2 z hz
  exact X.mem_Gi_of_between (h hz) (X.Z_le_Gi i hz) h1 h2

end Setup

end CFSG.Quasithin.St84
