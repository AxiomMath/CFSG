module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbTreeDist

public section

namespace CFSG.Combinatorics

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel T.Adj] in
private lemma exists_adj_dist_eq_of_connected {c v : V} {k : ℕ} (hT : T.Connected)
    (hv : T.dist c v = k + 1) : ∃ w, T.Adj w v ∧ T.dist c w = k := by
  obtain ⟨p, hp⟩ := hT.exists_walk_length_eq_dist c v
  have hlen : p.length = k + 1 := by rw [hp, hv]
  have hnil : ¬ p.reverse.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, SimpleGraph.Walk.length_reverse, hlen]
    omega
  obtain ⟨w, hw, q, hq⟩ := SimpleGraph.Walk.not_nil_iff.mp hnil
  have hqlen : q.length = k := by
    have h := congrArg SimpleGraph.Walk.length hq
    rw [SimpleGraph.Walk.length_reverse, hlen, SimpleGraph.Walk.length_cons] at h
    omega
  have h1 : T.dist c w ≤ k := by
    rw [SimpleGraph.dist_comm]
    calc T.dist w c ≤ q.length := SimpleGraph.dist_le q
      _ = k := hqlen
  have h2 : k ≤ T.dist c w := by
    have htri := (hT c w).dist_triangle_left v
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hw.symm, hv] at htri
    omega
  exact ⟨w, hw.symm, le_antisymm h1 h2⟩

private lemma eq_of_adj_dist_eq {c : V} (hT : T.Connected) (hdeg : ∀ v, v ≠ c → T.degree v ≤ 2)
    {k : ℕ} {v v' w : V} (hwv : T.Adj w v) (hwv' : T.Adj w v') (hw : T.dist c w = k + 1)
    (hv : T.dist c v = k + 2) (hv' : T.dist c v' = k + 2) : v = v' := by
  by_contra hne
  have hwc : w ≠ c := by
    intro h
    rw [h, SimpleGraph.dist_self] at hw
    omega
  obtain ⟨z, hzw, hzd⟩ := exists_adj_dist_eq_of_connected hT hw
  have hzv : z ≠ v := by
    intro h
    rw [h] at hzd
    omega
  have hzv' : z ≠ v' := by
    intro h
    rw [h] at hzd
    omega
  have hsub : ({v, v', z} : Finset V) ⊆ T.neighborFinset w := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [SimpleGraph.mem_neighborFinset]
    rcases hy with rfl | rfl | rfl
    · exact hwv
    · exact hwv'
    · exact hzw.symm
  have hcard3 : ({v, v', z} : Finset V).card = 3 := by
    have h1 : v ∉ ({v', z} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne, Ne.symm hzv⟩
    have h2 : v' ∉ ({z} : Finset V) := by
      simp only [Finset.mem_singleton]
      exact Ne.symm hzv'
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]
  have hge3 : 3 ≤ T.degree w := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    calc 3 = ({v, v', z} : Finset V).card := hcard3.symm
      _ ≤ (T.neighborFinset w).card := Finset.card_le_card hsub
  have := hdeg w hwc
  omega

theorem degree_smul_eq {G : Type*} [Group G] [MulAction G V]
    (hadj : ∀ (g : G) (u v : V), T.Adj (g • u) (g • v) ↔ T.Adj u v) (g : G) (v : V) :
    T.degree (g • v) = T.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have h : T.neighborFinset (g • v) = (T.neighborFinset v).image (fun w => g • w) := by
    ext w
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
    constructor
    · intro hw
      refine ⟨g⁻¹ • w, ?_, by simp⟩
      rw [SimpleGraph.mem_neighborFinset]
      have h1 : T.Adj (g • v) (g • (g⁻¹ • w)) := by simpa using hw
      exact (hadj g v (g⁻¹ • w)).mp h1
    · rintro ⟨u, hu, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hu
      exact (hadj g v u).mpr hu
  rw [h, Finset.card_image_of_injective _ (MulAction.injective g)]

theorem card_dist_eq_add_two_le (hT : T.Connected) {c : V} (hdeg : ∀ v, v ≠ c → T.degree v ≤ 2)
    (k : ℕ) : #{v | T.dist c v = k + 2} ≤ #{v | T.dist c v = k + 1} := by
  classical
  let f : V → V := fun v =>
    if hv : T.dist c v = k + 2 then
      (exists_adj_dist_eq_of_connected (k := k + 1) hT hv).choose else v
  have hf : ∀ v, T.dist c v = k + 2 → T.Adj (f v) v ∧ T.dist c (f v) = k + 1 := by
    intro v hv
    have hfv : f v = (exists_adj_dist_eq_of_connected (k := k + 1) hT hv).choose := by
      simp only [f]
      exact dif_pos hv
    rw [hfv]
    exact (exists_adj_dist_eq_of_connected (k := k + 1) hT hv).choose_spec
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_univ _, (hf v hv.2).2⟩
  · intro v hv v' hv' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hv hv'
    exact eq_of_adj_dist_eq hT hdeg (hf v hv.2).1 (by rw [heq]; exact (hf v' hv'.2).1)
      (hf v hv.2).2 hv.2 hv'.2

theorem card_dist_eq_succ_le (hT : T.Connected) {c : V} (hdeg : ∀ v, v ≠ c → T.degree v ≤ 2)
    (d : ℕ) : #{v | T.dist c v = d + 1} ≤ T.degree c := by
  induction d with
  | zero =>
    rw [show (univ.filter fun v => T.dist c v = 0 + 1) = T.neighborFinset c by
      ext v
      simp [SimpleGraph.dist_eq_one_iff_adj]]
    exact le_of_eq (SimpleGraph.card_neighborFinset_eq_degree T c)
  | succ d ih =>
    exact le_trans (card_dist_eq_add_two_le hT hdeg d) ih

omit [DecidableEq V] in
theorem card_degree_le_one_le_two (hT : T.IsTree) (hdeg : ∀ v, T.degree v ≤ 2) :
    #{v | T.degree v ≤ 1} ≤ 2 := by
  classical
  set L := #{v | T.degree v ≤ 1} with hL
  set M := #{v | ¬ T.degree v ≤ 1} with hM
  have hLM : L + M = Fintype.card V := by
    rw [hL, hM]
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun v => T.degree v ≤ 1)
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun v => T.degree v ≤ 1) (f := fun v => T.degree v)
  have h1 : ∑ v with T.degree v ≤ 1, T.degree v ≤ L := by
    rw [hL]
    calc ∑ v with T.degree v ≤ 1, T.degree v
        ≤ ∑ v with T.degree v ≤ 1, (1 : ℕ) :=
          Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = #{v | T.degree v ≤ 1} := by simp
  have h2 : ∑ v with ¬ T.degree v ≤ 1, T.degree v ≤ 2 * M := by
    rw [hM]
    calc ∑ v with ¬ T.degree v ≤ 1, T.degree v
        ≤ ∑ v with ¬ T.degree v ≤ 1, (2 : ℕ) :=
          Finset.sum_le_sum (fun v _ => hdeg v)
      _ = 2 * #{v | ¬ T.degree v ≤ 1} := by simp [Finset.sum_const, mul_comm]
  have hsum := T.sum_degrees_eq_twice_card_edges
  have hedge := hT.card_edgeFinset
  have hV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr hT.connected.nonempty
  omega

theorem card_orbit_le_two_of_smul_eq (hT : T.Connected) {c : V} (hc : T.degree c ≤ 3)
    (hdeg : ∀ v, v ≠ c → T.degree v ≤ 2) {G : Type*} [Group G] [Finite G] [MulAction G V]
    (hG : IsPGroup 2 G) (hadj : ∀ (g : G) (u v : V), T.Adj (g • u) (g • v) ↔ T.Adj u v)
    (hfix : ∀ g : G, g • c = c) (x : V) : Nat.card (MulAction.orbit G x) ≤ 2 := by
  classical
  rcases eq_or_ne x c with hx | hx
  · rw [hx]
    have horb : MulAction.orbit G c = {c} := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact hfix g
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        exact ⟨1, by simp [hy]⟩
    rw [horb, Nat.card_coe_set_eq, Set.ncard_singleton]
    norm_num
  · have hdne : T.dist c x ≠ 0 := fun h => hx (hT.dist_eq_zero_iff.mp h).symm
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hdne
    have hdist : ∀ y ∈ MulAction.orbit G x, T.dist c y = d + 1 := by
      rintro y ⟨g, rfl⟩
      have h := CFSG.AGLEmbeddingD2.Tits.GN516.Tree.dist_perm_eq (T := T)
        (σ := MulAction.toPerm g) (fun u v => by simpa using hadj g u v) c x
      rw [MulAction.toPerm_apply, MulAction.toPerm_apply, hfix g] at h
      rw [h, hd]
    have hinj : Function.Injective (fun y : MulAction.orbit G x =>
        (⟨y.1, hdist y.1 y.2⟩ : {v // T.dist c v = d + 1})) := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : {v // T.dist c v = d + 1} => (z : V)) hab)
    have hle3 : Nat.card (MulAction.orbit G x) ≤ 3 := by
      rw [Nat.card_eq_fintype_card]
      calc Fintype.card (MulAction.orbit G x)
          ≤ Fintype.card {v // T.dist c v = d + 1} := Fintype.card_le_of_injective _ hinj
        _ = #{v | T.dist c v = d + 1} := Fintype.card_subtype _
        _ ≤ T.degree c := card_dist_eq_succ_le hT hdeg d
        _ ≤ 3 := hc
    obtain ⟨n, hn⟩ := hG.card_orbit x
    rw [hn] at hle3 ⊢
    have hn2 : n ≤ 1 := by
      by_contra h
      push Not at h
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := pow_le_pow_right' (by norm_num) h
      omega
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> norm_num

theorem smul_eq_of_smul_eq_of_degree_le_one (hT : T.IsTree) (hdeg : ∀ v, T.degree v ≤ 2)
    {G : Type*} [Group G] [MulAction G V]
    (hadj : ∀ (g : G) (u v : V), T.Adj (g • u) (g • v) ↔ T.Adj u v) {ℓ : V}
    (hℓ : T.degree ℓ ≤ 1) {g : G} (hg : g • ℓ = ℓ) (x : V) : g • x = x := by
  classical
  rcases eq_or_ne x ℓ with hx | hx
  · rw [hx]
    exact hg
  · have hdne : T.dist ℓ x ≠ 0 := fun h => hx (hT.connected.dist_eq_zero_iff.mp h).symm
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hdne
    have hgx : T.dist ℓ (g • x) = d + 1 := by
      have h := CFSG.AGLEmbeddingD2.Tits.GN516.Tree.dist_perm_eq (T := T)
        (σ := MulAction.toPerm g) (fun u v => by simpa using hadj g u v) ℓ x
      rw [MulAction.toPerm_apply, MulAction.toPerm_apply, hg] at h
      rw [h, hd]
    have hle1 : #{v | T.dist ℓ v = d + 1} ≤ 1 :=
      le_trans (card_dist_eq_succ_le hT.connected (fun v _ => hdeg v) d) hℓ
    have hxmem : x ∈ (univ.filter fun v => T.dist ℓ v = d + 1) := by simp [hd]
    have hgxmem : g • x ∈ (univ.filter fun v => T.dist ℓ v = d + 1) := by simp [hgx]
    exact (Finset.card_le_one.mp hle1 x hxmem (g • x) hgxmem).symm

theorem card_orbit_le_two_of_degree_le_two (hT : T.IsTree) (hdeg : ∀ v, T.degree v ≤ 2)
    {G : Type*} [Group G] [Finite G] [MulAction G V]
    (hadj : ∀ (g : G) (u v : V), T.Adj (g • u) (g • v) ↔ T.Adj u v) (x : V) :
    Nat.card (MulAction.orbit G x) ≤ 2 := by
  classical
  have hexists : ∃ ℓ, T.degree ℓ ≤ 1 := by
    by_contra h
    push Not at h
    have hV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr hT.connected.nonempty
    have hsum2 : 2 * Fintype.card V ≤ ∑ v, T.degree v := by
      calc 2 * Fintype.card V = ∑ _v : V, 2 := by simp [Finset.sum_const, mul_comm]
        _ ≤ ∑ v, T.degree v := Finset.sum_le_sum (fun v _ => by have := h v; omega)
    have hsum := T.sum_degrees_eq_twice_card_edges
    have hedge := hT.card_edgeFinset
    omega
  obtain ⟨ℓ, hℓ⟩ := hexists
  have hstab : MulAction.stabilizer G ℓ ≤ MulAction.stabilizer G x := fun g hg =>
    smul_eq_of_smul_eq_of_degree_le_one hT hdeg hadj hℓ hg x
  have hdvd : (MulAction.stabilizer G x).index ∣ (MulAction.stabilizer G ℓ).index :=
    Subgroup.index_dvd_of_le hstab
  have hsub : MulAction.orbit G ℓ ⊆ {v | T.degree v ≤ 1} := by
    rintro y ⟨g, rfl⟩
    change T.degree (g • ℓ) ≤ 1
    rw [degree_smul_eq hadj g ℓ]
    exact hℓ
  have horb_le : Nat.card (MulAction.orbit G ℓ) ≤ 2 := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card (MulAction.orbit G ℓ)
        ≤ Fintype.card {v // T.degree v ≤ 1} :=
          Fintype.card_le_of_injective (fun y => (⟨y.1, hsub y.2⟩ : {v // T.degree v ≤ 1}))
            (fun a b hab => Subtype.ext
              (congrArg (fun z : {v // T.degree v ≤ 1} => (z : V)) hab))
      _ = #{v | T.degree v ≤ 1} := Fintype.card_subtype _
      _ ≤ 2 := card_degree_le_one_le_two hT hdeg
  have hpos : 0 < (MulAction.stabilizer G ℓ).index := by
    rw [MulAction.index_stabilizer G ℓ]
    rw [Set.ncard_pos]
    exact ⟨ℓ, MulAction.mem_orbit_self ℓ⟩
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer G x]
  calc (MulAction.stabilizer G x).index ≤ (MulAction.stabilizer G ℓ).index :=
        Nat.le_of_dvd hpos hdvd
    _ = Nat.card (MulAction.orbit G ℓ) := by
        rw [Nat.card_coe_set_eq, MulAction.index_stabilizer]
    _ ≤ 2 := horb_le

theorem card_orbit_le_two_of_isTree (hT : T.IsTree) (hdeg : ∀ v, T.degree v ≤ 3)
    (hbr : ∀ u v, T.degree u = 3 → T.degree v = 3 → u = v) {G : Type*} [Group G] [Finite G]
    [MulAction G V] (hG : IsPGroup 2 G)
    (hadj : ∀ (g : G) (u v : V), T.Adj (g • u) (g • v) ↔ T.Adj u v) (x : V) :
    Nat.card (MulAction.orbit G x) ≤ 2 := by
  classical
  by_cases hb : ∃ b, T.degree b = 3
  · obtain ⟨b, hb3⟩ := hb
    have hfix : ∀ g : G, g • b = b := fun g =>
      hbr (g • b) b (by rw [degree_smul_eq hadj g b, hb3]) hb3
    refine card_orbit_le_two_of_smul_eq (c := b) hT.connected (le_of_eq hb3) ?_ hG hadj hfix x
    intro v hv
    by_contra h3
    have hv3 : T.degree v = 3 := by have := hdeg v; omega
    exact hv (hbr v b hv3 hb3)
  · push Not at hb
    exact card_orbit_le_two_of_degree_le_two hT
      (fun v => by have h1 := hdeg v; have h2 := hb v; omega) hadj x

end CFSG.Combinatorics
