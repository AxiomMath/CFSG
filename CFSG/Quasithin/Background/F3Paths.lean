module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.Quasithin

universe u v

variable {V : Type u}

@[ext] structure GPath (Γ : SimpleGraph V) (n : ℕ) where
  toFun : ℕ → V
  adj : ∀ i, i < n → Γ.Adj (toFun i) (toFun (i + 1))
  tail : ∀ i, n ≤ i → toFun i = toFun n

class GraphAction (H : Type*) [Group H] [MulAction H V] (Γ : SimpleGraph V) : Prop where
  adj_smul : ∀ (g : H) (a b : V), Γ.Adj (g • a) (g • b) ↔ Γ.Adj a b

namespace GPath

variable {Γ : SimpleGraph V} {n : ℕ}

instance : CoeFun (GPath Γ n) (fun _ => ℕ → V) := ⟨GPath.toFun⟩

theorem ext' {p q : GPath Γ n} (h : ∀ i, i ≤ n → p i = q i) : p = q := by
  refine GPath.ext (funext fun i => ?_)
  by_cases hi : i ≤ n
  · exact h i hi
  · have h1 : p i = p n := p.tail i (by omega)
    have h2 : q i = q n := q.tail i (by omega)
    show p.toFun i = q.toFun i
    rw [show p.toFun i = p n from h1, show q.toFun i = q n from h2]
    exact h n le_rfl

@[expose] def NoBack (p : GPath Γ n) : Prop := ∀ i, i + 2 ≤ n → p i ≠ p (i + 2)

@[expose] def paths (Γ : SimpleGraph V) (u : V) (n : ℕ) : Set (GPath Γ n) := {p | p 0 = u}

@[expose] def nbPaths (Γ : SimpleGraph V) (u : V) (n : ℕ) : Set (GPath Γ n) :=
  {p | p 0 = u ∧ p.NoBack}

@[expose] def snoc (p : GPath Γ n) (w : V) (h : Γ.Adj (p n) w) : GPath Γ (n + 1) where
  toFun i := if i ≤ n then p i else w
  adj i hi := by
    by_cases h1 : i + 1 ≤ n
    · simpa [h1, show i ≤ n by omega] using p.adj i (by omega)
    · have hi' : i = n := by omega
      subst hi'
      simpa using h
  tail i hi := by
    simp [show ¬ i ≤ n by omega, show ¬ n + 1 ≤ n by omega]

@[simp] theorem snoc_of_le (p : GPath Γ n) (w : V) (h : Γ.Adj (p n) w) {i : ℕ} (hi : i ≤ n) :
    p.snoc w h i = p i := by
  show (if i ≤ n then p i else w) = p i
  simp [hi]

@[simp] theorem snoc_last (p : GPath Γ n) (w : V) (h : Γ.Adj (p n) w) : p.snoc w h (n + 1) = w := by
  show (if n + 1 ≤ n then p (n + 1) else w) = w
  simp

@[expose] def take (p : GPath Γ n) (k : ℕ) (hk : k ≤ n) : GPath Γ k where
  toFun i := p (min i k)
  adj i hi := by
    have h1 : min i k = i := min_eq_left hi.le
    have h2 : min (i + 1) k = i + 1 := min_eq_left hi
    simp only [h1, h2]
    exact p.adj i (by omega)
  tail i hi := by
    have h1 : min i k = k := min_eq_right hi
    simp [h1]

@[simp] theorem take_apply_of_le (p : GPath Γ n) (k : ℕ) (hk : k ≤ n) {i : ℕ} (hi : i ≤ k) :
    p.take k hk i = p i := by
  show p (min i k) = p i
  rw [min_eq_left hi]

@[expose] def map {W : Type v} {Δ : SimpleGraph W} (f : V → W)
    (hf : ∀ a b, Γ.Adj a b → Δ.Adj (f a) (f b)) (p : GPath Γ n) : GPath Δ n where
  toFun i := f (p i)
  adj i hi := hf _ _ (p.adj i hi)
  tail i hi := by simp [p.tail i hi]

@[simp] theorem map_apply {W : Type v} {Δ : SimpleGraph W} (f : V → W)
    (hf : ∀ a b, Γ.Adj a b → Δ.Adj (f a) (f b)) (p : GPath Γ n) (i : ℕ) :
    p.map f hf i = f (p i) := rfl

section Dist

variable (hΓ : Γ.Connected)

include hΓ in
theorem dist_le_length : ∀ {n : ℕ} (p : GPath Γ n), Γ.dist (p 0) (p n) ≤ n := by
  intro n
  induction n with
  | zero =>
    intro p
    simp
  | succ n ih =>
    intro p
    have h1 := ih (p.take n (by omega))
    simp only [take_apply_of_le _ _ _ (le_refl n), take_apply_of_le _ _ _ (Nat.zero_le n)] at h1
    have h2 : Γ.dist (p n) (p (n + 1)) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (p.adj n (by omega))
    have h3 := hΓ.dist_triangle (u := p 0) (v := p n) (w := p (n + 1))
    omega

include hΓ in
theorem dist_le_sub {n : ℕ} (p : GPath Γ n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    Γ.dist (p i) (p j) ≤ j - i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have h1 := ih (by omega)
    have h2 : Γ.dist (p j) (p (j + 1)) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (p.adj j (by omega))
    have h3 := hΓ.dist_triangle (u := p i) (v := p j) (w := p (j + 1))
    omega

include hΓ in
theorem dist_prefix {n : ℕ} (p : GPath Γ n) (h : Γ.dist (p 0) (p n) = n) {i : ℕ} (hi : i ≤ n) :
    Γ.dist (p 0) (p i) = i := by
  have h1 := dist_le_length hΓ (p.take i hi)
  simp only [take_apply_of_le _ _ _ (le_refl i), take_apply_of_le _ _ _ (Nat.zero_le i)] at h1
  have h2 := dist_le_sub hΓ p hi le_rfl
  have h3 := hΓ.dist_triangle (u := p 0) (v := p i) (w := p n)
  omega

include hΓ in
theorem noBack_of_dist_eq {n : ℕ} (p : GPath Γ n) (h : Γ.dist (p 0) (p n) = n) : p.NoBack := by
  intro i hi heq
  have h1 := dist_prefix hΓ p h (show i ≤ n by omega)
  have h2 := dist_le_sub hΓ p (show i + 2 ≤ n by omega) le_rfl
  have h3 := hΓ.dist_triangle (u := p 0) (v := p i) (w := p n)
  have h4 : Γ.dist (p i) (p n) ≤ Γ.dist (p i) (p (i + 2)) + Γ.dist (p (i + 2)) (p n) :=
    hΓ.dist_triangle
  have h5 : Γ.dist (p i) (p (i + 2)) = 0 := by
    rw [heq]; exact (SimpleGraph.Connected.dist_eq_zero_iff hΓ).mpr rfl
  omega

@[expose] def ofWalk {a b : V} (w : Γ.Walk a b) : GPath Γ w.length where
  toFun i := w.getVert i
  adj i hi := w.adj_getVert_succ hi
  tail i hi := by rw [w.getVert_of_length_le hi, w.getVert_length]

include hΓ in
theorem exists_geodesic (u y : V) :
    ∃ p : GPath Γ (Γ.dist u y), p 0 = u ∧ p (Γ.dist u y) = y ∧ p.NoBack := by
  obtain ⟨w, hw⟩ := hΓ.exists_walk_length_eq_dist u y
  set k := Γ.dist u y with hk
  let p : GPath Γ k :=
    ⟨fun i => w.getVert i, fun i hi => w.adj_getVert_succ (hw ▸ hi), fun i hi => by
      rw [w.getVert_of_length_le (hw ▸ hi), w.getVert_of_length_le (hw ▸ le_refl k)]⟩
  have h0 : p 0 = u := w.getVert_zero
  have hk' : p k = y := w.getVert_of_length_le (hw ▸ le_refl k)
  refine ⟨p, h0, hk', noBack_of_dist_eq hΓ p ?_⟩
  rw [h0, hk']

include hΓ in
theorem exists_geodesic' (u y : V) {n : ℕ} (h : Γ.dist u y = n) :
    ∃ p : GPath Γ n, p 0 = u ∧ p n = y ∧ p.NoBack := by
  subst h
  exact exists_geodesic hΓ u y

end Dist

@[expose] def IsGeodesic (p : GPath Γ n) : Prop := Γ.dist (p 0) (p n) = n

theorem NoBack.take {p : GPath Γ n} (h : p.NoBack) (k : ℕ) (hk : k ≤ n) : (p.take k hk).NoBack :=
  fun i hi heq => h i (by omega) (by
    simpa [take_apply_of_le _ _ _ (show i ≤ k by omega),
      take_apply_of_le _ _ _ (show i + 2 ≤ k by omega)] using heq)

@[expose] def seqPath (z : ℕ → V) (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (a n : ℕ) : GPath Γ n where
  toFun i := z (a + min i n)
  adj i hi := by
    have h1 : min i n = i := min_eq_left hi.le
    have h2 : min (i + 1) n = i + 1 := min_eq_left hi
    simp only [h1, h2, ← add_assoc]
    exact hz _
  tail i hi := by
    have h1 : min i n = n := min_eq_right hi
    simp [h1]

@[simp] theorem seqPath_apply (z : ℕ → V) (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (a n : ℕ) {i : ℕ}
    (hi : i ≤ n) : seqPath z hz a n i = z (a + i) := by
  show z (a + min i n) = z (a + i)
  rw [min_eq_left hi]

@[expose] def seqPathRev (z : ℕ → V) (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (b n : ℕ) (hn : n ≤ b) :
    GPath Γ n where
  toFun i := z (b - min i n)
  adj i hi := by
    have h1 : min i n = i := min_eq_left hi.le
    have h2 : min (i + 1) n = i + 1 := min_eq_left hi
    simp only [h1, h2]
    have h3 : b - i = (b - (i + 1)) + 1 := by omega
    rw [h3]
    exact (hz _).symm
  tail i hi := by
    have h1 : min i n = n := min_eq_right hi
    simp [h1]

@[simp] theorem seqPathRev_apply (z : ℕ → V) (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (b n : ℕ)
    (hn : n ≤ b) {i : ℕ} (hi : i ≤ n) : seqPathRev z hz b n hn i = z (b - i) := by
  show z (b - min i n) = z (b - i)
  rw [min_eq_left hi]

section Bipartite

variable {c : V → Bool} (hΓ : Γ.Connected)

theorem walk_even_iff (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {a b : V} (w : Γ.Walk a b) :
    c a = c b ↔ Even w.length := by
  induction w with
  | nil => simp
  | @cons a a' b h w ih =>
    have h1 := hc a a' h
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    cases ha : c a <;> cases ha' : c a' <;> cases hb : c b <;> simp_all

include hΓ in
theorem dist_even_iff (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) (a b : V) :
    c a = c b ↔ Even (Γ.dist a b) := by
  obtain ⟨w, hw⟩ := hΓ.exists_walk_length_eq_dist a b
  rw [← hw]
  exact walk_even_iff hc w

include hΓ in
theorem dist_adj_succ_or (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) (u : V) {a b : V} (h : Γ.Adj a b) :
    Γ.dist u b = Γ.dist u a + 1 ∨ Γ.dist u a = Γ.dist u b + 1 := by
  have h1 : Γ.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
  have h2 : Γ.dist b a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h.symm
  have h3 : Γ.dist u b ≤ Γ.dist u a + Γ.dist a b := hΓ.dist_triangle
  have h4 : Γ.dist u a ≤ Γ.dist u b + Γ.dist b a := hΓ.dist_triangle
  have hne : Γ.dist u a ≠ Γ.dist u b := by
    intro heq
    have e1 := dist_even_iff hΓ hc u a
    have e2 := dist_even_iff hΓ hc u b
    rw [heq] at e1
    have hab := hc a b h
    have e3 : c u = c a ↔ c u = c b := e1.trans e2.symm
    cases hu : c u <;> cases ha : c a <;> cases hb : c b <;> simp_all
  omega

end Bipartite

section Action

variable {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ]

@[expose] def smul (g : H) (p : GPath Γ n) : GPath Γ n :=
  p.map (g • ·) (fun a b h => (GraphAction.adj_smul g a b).mpr h)

instance : SMul H (GPath Γ n) := ⟨smul⟩

@[simp] theorem smul_apply (g : H) (p : GPath Γ n) (i : ℕ) : (g • p) i = g • p i := rfl

theorem smul_noBack {g : H} {p : GPath Γ n} (h : p.NoBack) : (g • p).NoBack :=
  fun i hi heq => h i hi (by
    have := congrArg (g⁻¹ • ·) heq
    simpa using this)

theorem one_smul' (p : GPath Γ n) : (1 : H) • p = p := ext' fun i _ => by simp

theorem mul_smul' (g h : H) (p : GPath Γ n) : (g * h) • p = g • h • p :=
  ext' fun i _ => by simp [mul_smul]

theorem noBack_smul_iff {g : H} {p : GPath Γ n} : (g • p).NoBack ↔ p.NoBack :=
  ⟨fun h => by
    have := smul_noBack (g := g⁻¹) h
    rwa [← mul_smul', inv_mul_cancel, one_smul'] at this, smul_noBack⟩

theorem smul_eq_iff {g : H} {p q : GPath Γ n} : g • p = q ↔ ∀ i, i ≤ n → g • p i = q i :=
  ⟨fun h i _ => by rw [← h]; rfl, fun h => ext' fun i hi => h i hi⟩

theorem dist_smul (hΓ : Γ.Connected) (g : H) (a b : V) : Γ.dist (g • a) (g • b) = Γ.dist a b := by
  have key : ∀ (g : H) (a b : V), Γ.dist (g • a) (g • b) ≤ Γ.dist a b := by
    intro g a b
    obtain ⟨w, hw⟩ := hΓ.exists_walk_length_eq_dist a b
    let f : Γ →g Γ := ⟨fun x => g • x, fun {x y} h => (GraphAction.adj_smul g x y).mpr h⟩
    have := SimpleGraph.dist_le (w.map f)
    rw [SimpleGraph.Walk.length_map, hw] at this
    exact this
  refine le_antisymm (key g a b) ?_
  have := key g⁻¹ (g • a) (g • b)
  simpa using this

end Action

end GPath

abbrev PathSet (Γ : SimpleGraph V) (u : V) : Type u := Σ n : ℕ, {p : GPath Γ n // p 0 = u}

namespace PathSet

variable {Γ : SimpleGraph V} {u : V}

@[expose] def NoBack (p : PathSet Γ u) : Prop := p.2.1.NoBack

@[ext] theorem ext {p q : PathSet Γ u} (h1 : p.1 = q.1) (h2 : ∀ i, p.2.1 i = q.2.1 i) : p = q := by
  obtain ⟨n, p, hp⟩ := p
  obtain ⟨n', q, hq⟩ := q
  dsimp only at h1
  subst h1
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  exact GPath.ext (funext h2)

variable {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ]

instance : MulAction (MulAction.stabilizer H u) (PathSet Γ u) where
  smul g p := ⟨p.1, (g : H) • p.2.1, by
    show ((g : H) • p.2.1) 0 = u
    rw [GPath.smul_apply, p.2.2]
    exact MulAction.mem_stabilizer_iff.mp g.2⟩
  one_smul p := PathSet.ext rfl fun i => by
    show ((1 : H) • p.2.1) i = p.2.1 i
    rw [GPath.smul_apply, one_smul]
  mul_smul a b p := PathSet.ext rfl fun i => by
    show (((a * b : MulAction.stabilizer H u) : H) • p.2.1) i =
      ((a : H) • (b : H) • p.2.1) i
    rw [show ((a * b : MulAction.stabilizer H u) : H) = (a : H) * (b : H) from rfl, GPath.mul_smul']

theorem smul_def (g : MulAction.stabilizer H u) (p : PathSet Γ u) (i : ℕ) :
    (g • p).2.1 i = (g : H) • p.2.1 i := rfl

end PathSet

end CFSG.Quasithin
