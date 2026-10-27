module

public import CFSG.Milestones.ASVolI.F4K.Iface
public import CFSG.Milestones.ASVolI.F4K.Base

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF
open scoped Pointwise

section PolyGraph

universe u

variable {V : Type u} {Γ : SimpleGraph V}

def burnsideF4k_pa_zf (z : ℕ → V) (m : ℕ) (a : ZMod (2 * m)) : V := z a.val

theorem burnsideF4k_pa_two_m (m : ℕ) : 2 * (m : ZMod (2 * m)) = 0 := by
  exact_mod_cast ZMod.natCast_self (2 * m)

theorem burnsideF4k_pa_zf_natCast {z : ℕ → V} {m : ℕ} (hper : ∀ i, z (i + 2 * m) = z i) (k : ℕ) :
    burnsideF4k_pa_zf z m (k : ZMod (2 * m)) = z k := by
  unfold burnsideF4k_pa_zf
  rw [ZMod.val_natCast]
  exact (Function.Periodic.map_mod_nat (f := z) (fun x => hper x)) k

theorem burnsideF4k_pa_zf_inj {col : V → Bool} (hΓ : Γ.Connected)
    (hc : ∀ a b, Γ.Adj a b → col a ≠ col b) {m : ℕ} (hm : 2 ≤ m) (hU : UniqueGeod Γ m)
    {z : ℕ → V} (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (hnb : ∀ i, z i ≠ z (i + 2))
    (hper : ∀ i, z (i + 2 * m) = z i) : Function.Injective (burnsideF4k_pa_zf z m) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  intro a b h
  have h1 : z a.val = z b.val := h
  rw [GPath.periodic_eq_iff hΓ hc (by omega) hU z hz hnb hper] at h1
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, ZMod.natCast_eq_natCast_iff']
  exact h1

theorem burnsideF4k_pa_col_add {col : V → Bool} (hc : ∀ a b, Γ.Adj a b → col a ≠ col b)
    {z : ℕ → V} (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (k j : ℕ) :
    col (z (k + j)) = col (z k) ↔ Even j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := hc _ _ (hz (k + j))
    rw [← add_assoc, Nat.even_add_one, ← ih]
    cases ha : col (z (k + j)) <;> cases hb : col (z (k + j + 1)) <;> cases hk : col (z k) <;>
      simp_all

theorem burnsideF4k_pa_even_val {m : ℕ} (hm : 2 ≤ m) (x : ZMod (2 * m)) :
    Even x.val ↔ Even x := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(r : ZMod (2 * m)), ?_⟩
    rw [← ZMod.natCast_zmod_val x, hr, Nat.cast_add]
  · rintro ⟨y, rfl⟩
    rw [ZMod.val_add, Nat.even_iff, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 m), ← Nat.even_iff]
    exact ⟨y.val, rfl⟩

theorem burnsideF4k_pa_zf_col_iff {col : V → Bool} (hc : ∀ a b, Γ.Adj a b → col a ≠ col b)
    {m : ℕ} (hm : 2 ≤ m) {z : ℕ → V} (hz : ∀ i, Γ.Adj (z i) (z (i + 1)))
    (hper : ∀ i, z (i + 2 * m) = z i) (s t : ZMod (2 * m)) :
    col (burnsideF4k_pa_zf z m t) = col (burnsideF4k_pa_zf z m s) ↔ Even (t - s) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  rw [← burnsideF4k_pa_even_val hm (t - s)]
  have e : burnsideF4k_pa_zf z m t = z (s.val + (t - s).val) := by
    rw [← burnsideF4k_pa_zf_natCast hper]
    congr 1
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  rw [e]
  exact burnsideF4k_pa_col_add hc hz s.val (t - s).val

theorem burnsideF4k_pa_two_mul_eq_zero {m : ℕ} (hm : 2 ≤ m) (x : ZMod (2 * m)) :
    2 * x = 0 ↔ x = 0 ∨ x = (m : ZMod (2 * m)) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  constructor
  · intro h
    have h1 : ((2 * x.val : ℕ) : ZMod (2 * m)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_ofNat]
      exact h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have h2 : m ∣ x.val := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h1
    obtain ⟨k, hk⟩ := h2
    have hlt : x.val < 2 * m := ZMod.val_lt x
    have hk2 : k < 2 := by
      by_contra hk2
      push Not at hk2
      have : m * 2 ≤ m * k := Nat.mul_le_mul (le_refl m) hk2
      omega
    interval_cases k
    · left
      rw [← ZMod.natCast_zmod_val x, hk, mul_zero, Nat.cast_zero]
    · right
      rw [← ZMod.natCast_zmod_val x, hk, mul_one]
  · rintro (rfl | rfl)
    · exact mul_zero 2
    · exact burnsideF4k_pa_two_m m

theorem burnsideF4k_pa_dist_ge {col : V → Bool} (hΓ : Γ.Connected)
    (hc : ∀ a b, Γ.Adj a b → col a ≠ col b) {m : ℕ} (hU : UniqueGeod Γ m) {z : ℕ → V}
    (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (hnb : ∀ i, z i ≠ z (i + 2))
    (hper : ∀ i, z (i + 2 * m) = z i) (i : ℕ) {d : ℕ} (hd1 : m ≤ d) (hd2 : d ≤ 2 * m) :
    Γ.dist (z i) (z (i + d)) = 2 * m - d := by
  have h := GPath.window_dist hΓ hc hU z hz hnb (i + d) (d := 2 * m - d) (by omega)
  rw [show i + d + (2 * m - d) = i + 2 * m by omega, hper] at h
  rw [SimpleGraph.dist_comm]
  exact h

theorem burnsideF4k_pa_exists_d {z : ℕ → V} {m : ℕ} (hm : 2 ≤ m)
    (hper : ∀ i, z (i + 2 * m) = z i) (i j : ℕ) : ∃ d, d < 2 * m ∧ z j = z (i + d) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  refine ⟨((j : ZMod (2 * m)) - i).val, ZMod.val_lt _, ?_⟩
  rw [← burnsideF4k_pa_zf_natCast hper j, ← burnsideF4k_pa_zf_natCast hper (i + _)]
  congr 1
  rw [Nat.cast_add, ZMod.natCast_zmod_val]
  ring

theorem burnsideF4k_pa_opp {col : V → Bool} (hΓ : Γ.Connected)
    (hc : ∀ a b, Γ.Adj a b → col a ≠ col b) {m : ℕ} (hm : 2 ≤ m) (hU : UniqueGeod Γ m)
    {z : ℕ → V} (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (hnb : ∀ i, z i ≠ z (i + 2))
    (hper : ∀ i, z (i + 2 * m) = z i) (i j : ℕ) (hij : Γ.dist (z i) (z j) = m) :
    z j = z (i + m) := by
  obtain ⟨d, hd, hj⟩ := burnsideF4k_pa_exists_d hm hper i j
  rw [hj] at hij ⊢
  by_cases hdm : d ≤ m
  · rw [GPath.window_dist hΓ hc hU z hz hnb i hdm] at hij
    rw [hij]
  · rw [burnsideF4k_pa_dist_ge hΓ hc hU hz hnb hper i (by omega) (by omega)] at hij
    omega

theorem burnsideF4k_pa_nbr {col : V → Bool} (hΓ : Γ.Connected)
    (hc : ∀ a b, Γ.Adj a b → col a ≠ col b) {m : ℕ} (hm : 2 ≤ m) (hU : UniqueGeod Γ m)
    {z : ℕ → V} (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (hnb : ∀ i, z i ≠ z (i + 2))
    (hper : ∀ i, z (i + 2 * m) = z i) (i : ℕ) {w : V} (hw : w ∈ Set.range z)
    (hadj : Γ.Adj (z i) w) : w = z (i + 1) ∨ w = z (i + 2 * m - 1) := by
  obtain ⟨j, rfl⟩ := hw
  obtain ⟨d, hd, hj⟩ := burnsideF4k_pa_exists_d hm hper i j
  rw [hj] at hadj ⊢
  have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  by_cases hdm : d ≤ m
  · rw [GPath.window_dist hΓ hc hU z hz hnb i hdm] at h1
    left
    rw [h1]
  · rw [burnsideF4k_pa_dist_ge hΓ hc hU hz hnb hper i (by omega) (by omega)] at h1
    right
    congr 1
    omega

theorem burnsideF4k_pa_zf_nbr {col : V → Bool} (hΓ : Γ.Connected)
    (hc : ∀ a b, Γ.Adj a b → col a ≠ col b) {m : ℕ} (hm : 2 ≤ m) (hU : UniqueGeod Γ m)
    {z : ℕ → V} (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) (hnb : ∀ i, z i ≠ z (i + 2))
    (hper : ∀ i, z (i + 2 * m) = z i) (a : ZMod (2 * m)) {w : V} (hw : w ∈ Set.range z)
    (hadj : Γ.Adj (burnsideF4k_pa_zf z m a) w) :
    w = burnsideF4k_pa_zf z m (a + 1) ∨ w = burnsideF4k_pa_zf z m (a - 1) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  rcases burnsideF4k_pa_nbr hΓ hc hm hU hz hnb hper a.val hw hadj with h | h
  · left
    rw [h, ← burnsideF4k_pa_zf_natCast hper]
    congr 1
    rw [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
  · right
    rw [h, ← burnsideF4k_pa_zf_natCast hper]
    congr 1
    rw [Nat.cast_sub (show 1 ≤ a.val + 2 * m by omega), Nat.cast_add, ZMod.natCast_zmod_val,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    linear_combination burnsideF4k_pa_two_m m

theorem burnsideF4k_pa_arc₁_apply (z : ℕ → V) (hz : ∀ i, Γ.Adj (z i) (z (i + 1)))
    {m i j : ℕ} (hj : j ≤ m) : GPath.arc₁ z hz m i j = z (i + j) := by
  rw [GPath.arc₁, GPath.seqPath_apply _ _ _ _ hj]

theorem burnsideF4k_pa_arc₂_apply (z : ℕ → V) (hz : ∀ i, Γ.Adj (z i) (z (i + 1)))
    {m i j : ℕ} (hj : j ≤ m) : GPath.arc₂ z hz m i j = z (i + 2 * m - j) := by
  rw [GPath.arc₂, GPath.seqPathRev_apply _ _ _ _ _ hj]

section Action

variable {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ]

theorem burnsideF4k_pa_swap_act {z : ℕ → V} (hz : ∀ i, Γ.Adj (z i) (z (i + 1))) {m : ℕ}
    (hm : 2 ≤ m) (hper : ∀ i, z (i + 2 * m) = z i) (i : ℕ) {g : H}
    (h1 : g • GPath.arc₁ z hz m i = GPath.arc₂ z hz m i)
    (h2 : g • GPath.arc₂ z hz m i = GPath.arc₁ z hz m i) (t : ZMod (2 * m)) :
    g • burnsideF4k_pa_zf z m t = burnsideF4k_pa_zf z m (2 * (i : ZMod (2 * m)) - t) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have e1 : ∀ j, j ≤ m → g • z (i + j) = z (i + 2 * m - j) := by
    intro j hj
    have := (GPath.smul_eq_iff.mp h1) j hj
    rwa [burnsideF4k_pa_arc₁_apply z hz hj, burnsideF4k_pa_arc₂_apply z hz hj] at this
  have e2 : ∀ j, j ≤ m → g • z (i + 2 * m - j) = z (i + j) := by
    intro j hj
    have := (GPath.smul_eq_iff.mp h2) j hj
    rwa [burnsideF4k_pa_arc₁_apply z hz hj, burnsideF4k_pa_arc₂_apply z hz hj] at this
  have h2m := burnsideF4k_pa_two_m m
  obtain ⟨d, hd⟩ : ∃ d, d = (t - (i : ZMod (2 * m))).val := ⟨_, rfl⟩
  have hdlt : d < 2 * m := by
    rw [hd]
    exact ZMod.val_lt _
  have ht : t = ((i + d : ℕ) : ZMod (2 * m)) := by
    rw [Nat.cast_add, hd, ZMod.natCast_zmod_val]
    ring
  rw [ht, burnsideF4k_pa_zf_natCast hper]
  by_cases hdm : d ≤ m
  · rw [e1 d hdm, ← burnsideF4k_pa_zf_natCast hper]
    congr 1
    rw [Nat.cast_sub (show d ≤ i + 2 * m by omega)]
    push_cast
    linear_combination h2m
  · have key : g • z (i + d) = z (i + (2 * m - d)) := by
      have := e2 (2 * m - d) (by omega)
      rwa [show i + 2 * m - (2 * m - d) = i + d by omega] at this
    rw [key, ← burnsideF4k_pa_zf_natCast hper]
    congr 1
    push_cast [Nat.cast_sub (show d ≤ 2 * m by omega)]
    linear_combination h2m

end Action

end PolyGraph

section Dihedral

variable {V : Type*} {H : Type*} [Group H] [MulAction H V] {n : ℕ} (f : ZMod n → V)

theorem burnsideF4k_pa_closure_act {sx sl : H} (hsx : ∀ t, sx • f t = f (-t))
    (hsl : ∀ t, sl • f t = f (2 - t)) {w : H} (hw : w ∈ Subgroup.closure {sx, sl}) :
    ∃ a e : ZMod n, Even a ∧ (e = 1 ∨ e = -1) ∧ ∀ t, w • f t = f (a + e * t) := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨0, -1, Even.zero, Or.inr rfl, fun t => by rw [hsx]; congr 1; ring⟩
    · exact ⟨2, -1, even_two, Or.inr rfl, fun t => by rw [hsl]; congr 1; ring⟩
  | one => exact ⟨0, 1, Even.zero, Or.inl rfl, fun t => by rw [one_smul]; congr 1; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, e, ha, he, hxa⟩ := hx
    obtain ⟨b, d, hb, hd, hyb⟩ := hy
    refine ⟨a + e * b, e * d, ha.add (hb.mul_left e), ?_, fun t => ?_⟩
    · rcases he with rfl | rfl <;> rcases hd with rfl | rfl <;> simp
    · rw [mul_smul, hyb, hxa]
      congr 1
      ring
  | inv x _ hx =>
    obtain ⟨a, e, ha, he, hxa⟩ := hx
    have hee : e * e = 1 := by rcases he with rfl | rfl <;> ring
    refine ⟨-(e * a), e, (ha.mul_left e).neg, he, fun t => ?_⟩
    have h1 : x • f (-(e * a) + e * t) = f t := by
      rw [hxa]
      congr 1
      linear_combination (t - a) * hee
    rw [← h1, inv_smul_smul]

theorem burnsideF4k_pa_pow_act {sx sl : H} (hsx : ∀ t, sx • f t = f (-t))
    (hsl : ∀ t, sl • f t = f (2 - t)) (k : ℕ) (t : ZMod n) :
    (sl * sx) ^ k • f t = f (2 * (k : ZMod n) + t) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_smul, mul_smul, hsx, hsl, ih]
    congr 1
    push_cast
    ring

theorem burnsideF4k_pa_pow_mul_act {sx sl : H} (hsx : ∀ t, sx • f t = f (-t))
    (hsl : ∀ t, sl • f t = f (2 - t)) (k : ℕ) (t : ZMod n) :
    ((sl * sx) ^ k * sx) • f t = f (2 * (k : ZMod n) - t) := by
  rw [mul_smul, hsx, burnsideF4k_pa_pow_act f hsx hsl]
  congr 1
  ring

end Dihedral

section Flags

variable {V : Type*}

def burnsideF4k_pa_flag {m : ℕ} (f : ZMod (2 * m) → V) (p : Fin m × Bool) : V × V :=
  (f (2 * ((p.1 : ℕ) : ZMod (2 * m))), f (2 * ((p.1 : ℕ) : ZMod (2 * m)) + if p.2 then 1 else -1))

theorem burnsideF4k_pa_flag_inj {m : ℕ} (hm : 2 ≤ m) {f : ZMod (2 * m) → V}
    (hf : Function.Injective f) : Function.Injective (burnsideF4k_pa_flag f) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  rintro ⟨k, b⟩ ⟨k', b'⟩ h
  simp only [burnsideF4k_pa_flag, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := hf h1
  have hk1 := k.isLt
  have hk2 := k'.isLt
  have hk : k = k' := by
    have h3 : ((2 * (k : ℕ) : ℕ) : ZMod (2 * m)) = ((2 * (k' : ℕ) : ℕ) : ZMod (2 * m)) := by
      exact_mod_cast h1'
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      at h3
    exact Fin.ext (by omega)
  subst hk
  have h3 : (if b then (1 : ZMod (2 * m)) else -1) = if b' then 1 else -1 := add_left_cancel (hf h2)
  have h2ne : (2 : ZMod (2 * m)) ≠ 0 := by
    intro h
    have h4 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  have hb : b = b' := by
    rcases b with _ | _ <;> rcases b' with _ | _
    · rfl
    · have h4 : (-1 : ZMod (2 * m)) = 1 := h3
      exact absurd (show (2 : ZMod (2 * m)) = 0 by linear_combination -h4) h2ne
    · have h4 : (1 : ZMod (2 * m)) = -1 := h3
      exact absurd (show (2 : ZMod (2 * m)) = 0 by linear_combination h4) h2ne
    · rfl
  rw [hb]

theorem burnsideF4k_pa_flag_mem {m : ℕ} (hm : 2 ≤ m) (f : ZMod (2 * m) → V) {a e : ZMod (2 * m)}
    (ha : Even a) (he : e = 1 ∨ e = -1) :
    (f a, f (a + e)) ∈ Set.range (burnsideF4k_pa_flag f) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨j, hj⟩ := (burnsideF4k_pa_even_val hm a).mpr ha
  have hlt : a.val < 2 * m := ZMod.val_lt a
  have ha' : 2 * ((j : ℕ) : ZMod (2 * m)) = a := by
    rw [← ZMod.natCast_zmod_val a, hj, Nat.cast_add]
    ring
  rcases he with rfl | rfl
  · refine ⟨(⟨j, by omega⟩, true), ?_⟩
    show (f (2 * ((j : ℕ) : ZMod (2 * m))), f (2 * ((j : ℕ) : ZMod (2 * m)) + 1)) = _
    rw [ha']
  · refine ⟨(⟨j, by omega⟩, false), ?_⟩
    show (f (2 * ((j : ℕ) : ZMod (2 * m))), f (2 * ((j : ℕ) : ZMod (2 * m)) + -1)) = _
    rw [ha']

end Flags

section Completion

variable {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z]

theorem burnsideF4k_pa_stab_eq (c : α.Completion Z) {m : ℕ} (hm : 2 ≤ m)
    (hU : UniqueGeod c.graph m) {z : ℕ → c.Γ} (hz : ∀ i, c.graph.Adj (z i) (z (i + 1)))
    (hnb : ∀ i, z i ≠ z (i + 2)) (hper : ∀ i, z (i + 2 * m) = z i) {H : Subgroup c.G0}
    (hH : H ≤ setStab c (Set.range z)) :
    MulAction.stabilizer (↥H) (z 0, z 1) = (pointwiseStab c (Set.range z)).subgroupOf H := by
  have hconn := connected_graph c
  have hbip : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  obtain ⟨φ⟩ := GPath.isPolygon_of_periodic hconn hbip hm hU z hz hnb hper
  ext h
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, burnsideF4k_mem_pointwiseStab c]
  constructor
  · intro hh
    have h0 : (h : c.G0) • z 0 = z 0 := congrArg Prod.fst hh
    have h1 : (h : c.G0) • z 1 = z 1 := congrArg Prod.snd hh
    exact burnsideF4k_polygon_fix_adj (by omega) φ (h : c.G0)
      (fun v hv => burnsideF4k_setStab_mem c (hH h.2) hv) ⟨0, rfl⟩ ⟨1, rfl⟩ (hz 0) h0 h1
  · intro hh
    exact Prod.ext (hh (z 0) ⟨0, rfl⟩) (hh (z 1) ⟨1, rfl⟩)

end Completion

theorem burnsideF4k_polyArcs : burnsideF4k_PolyArcs := by
  intro α Z _ c m hm hU z hz hnb hper i
  have hconn := connected_graph c
  have hbip : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  have hdist : c.graph.dist (z i) (z (i + m)) = m :=
    GPath.window_dist hconn hbip hU z hz hnb i le_rfl
  refine ⟨⟨GPath.arc₁_zero z hz m i, GPath.arc₁_last z hz m i, ?_⟩,
    ⟨GPath.arc₂_zero z hz m hper i, GPath.arc₂_last z hz m i, ?_⟩,
    GPath.arc_ne z hz hnb m hper (by omega) i, ?_⟩
  · show c.graph.dist _ _ = m
    rw [GPath.arc₁_zero, GPath.arc₁_last]
    exact hdist
  · show c.graph.dist _ _ = m
    rw [GPath.arc₂_zero z hz m hper, GPath.arc₂_last]
    exact hdist
  · ext v
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨d, hd, hk⟩ := burnsideF4k_pa_exists_d hm hper i k
      rw [hk]
      by_cases hdm : d ≤ m
      · exact Or.inl ⟨d, hdm, burnsideF4k_pa_arc₁_apply z hz hdm⟩
      · refine Or.inr ⟨2 * m - d, by omega, ?_⟩
        rw [burnsideF4k_pa_arc₂_apply z hz (by omega)]
        congr 1
        omega
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨_, (burnsideF4k_pa_arc₁_apply z hz hj).symm⟩
      · exact ⟨_, (burnsideF4k_pa_arc₂_apply z hz hj).symm⟩

theorem burnsideF4k_polyOpp : burnsideF4k_PolyOpp := by
  intro α Z _ c m hm hU z hz hnb hper i j hij
  have hbip : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  exact burnsideF4k_pa_opp (connected_graph c) hbip hm hU hz hnb hper i j hij

theorem burnsideF4k_polyNbr : burnsideF4k_PolyNbr := by
  intro α Z _ c m hm hU z hz hnb hper i w hw hadj
  have hbip : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  exact burnsideF4k_pa_nbr (connected_graph c) hbip hm hU hz hnb hper i hw hadj

theorem burnsideF4k_polyRefl : burnsideF4k_PolyRefl := by
  intro α Z _ c m hm hU z hz hnb hper i g h1 h2
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hconn := connected_graph c
  have hbip : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  have hinj := burnsideF4k_pa_zf_inj hconn hbip hm hU hz hnb hper
  have hact := burnsideF4k_pa_swap_act hz hm hper i h1 h2
  have hcast : ∀ k : ℕ, burnsideF4k_pa_zf z m (k : ZMod (2 * m)) = z k :=
    burnsideF4k_pa_zf_natCast hper
  have h2m := burnsideF4k_pa_two_m m
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro w ⟨k, rfl⟩
    rw [← hcast k, mul_smul, hact, hact]
    congr 1
    ring
  · rw [setStab, MulAction.mem_stabilizer_iff]
    apply Set.Subset.antisymm
    · rintro v ⟨w, ⟨k, rfl⟩, rfl⟩
      show g • z k ∈ Set.range z
      rw [← hcast k, hact]
      exact ⟨_, rfl⟩
    · rintro v ⟨k, rfl⟩
      refine ⟨burnsideF4k_pa_zf z m (2 * (i : ZMod (2 * m)) - k), ⟨_, rfl⟩, ?_⟩
      show g • burnsideF4k_pa_zf z m (2 * (i : ZMod (2 * m)) - k) = z k
      rw [hact, ← hcast k]
      congr 1
      ring
  · rw [← hcast i, hact]
    congr 1
    ring
  · have hne : z i ≠ z (i + m) := by
      intro h
      have := GPath.window_dist hconn hbip hU z hz hnb i (le_refl m)
      rw [← h, SimpleGraph.dist_self] at this
      omega
    have hfix : {w : c.Γ | w ∈ Set.range z ∧ g • w = w} = {z i, z (i + m)} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨k, rfl⟩, hk⟩
        rw [← hcast k, hact] at hk
        have hk' := hinj hk
        rcases (burnsideF4k_pa_two_mul_eq_zero hm ((k : ZMod (2 * m)) - i)).mp
          (by linear_combination -hk') with h | h
        · left
          rw [← hcast k, ← hcast i]
          congr 1
          linear_combination h
        · right
          rw [← hcast k, ← hcast (i + m)]
          congr 1
          push_cast
          linear_combination h
      · rintro (rfl | rfl)
        · refine ⟨⟨i, rfl⟩, ?_⟩
          rw [← hcast i, hact]
          congr 1
          ring
        · refine ⟨⟨i + m, rfl⟩, ?_⟩
          rw [← hcast (i + m), hact]
          congr 1
          push_cast
          linear_combination -h2m
    rw [hfix, Set.ncard_pair hne]

theorem burnsideF4k_polyW : burnsideF4k_PolyW := by
  intro α Z _ c m hm hU z hz hnb hper hz0 hz1 sx sl hx1 hx2 hl1 hl2
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hconn := connected_graph c
  have hbip : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  have hinj := burnsideF4k_pa_zf_inj hconn hbip hm hU hz hnb hper
  have hcast : ∀ k : ℕ, burnsideF4k_pa_zf z m (k : ZMod (2 * m)) = z k :=
    burnsideF4k_pa_zf_natCast hper
  have hz0' : z 0 = burnsideF4k_pa_zf z m 0 := by rw [← hcast 0, Nat.cast_zero]
  have hz1' : z 1 = burnsideF4k_pa_zf z m 1 := by rw [← hcast 1, Nat.cast_one]
  have hsx : ∀ t, sx • burnsideF4k_pa_zf z m t = burnsideF4k_pa_zf z m (-t) := by
    intro t
    rw [burnsideF4k_pa_swap_act hz hm hper 0 hx1 hx2]
    congr 1
    simp
  have hsl : ∀ t, sl • burnsideF4k_pa_zf z m t = burnsideF4k_pa_zf z m (2 - t) := by
    intro t
    rw [burnsideF4k_pa_swap_act hz hm hper 1 hl1 hl2]
    congr 1
    simp
  have hrx : IsReflectionOn c sx (Set.range z) c.xv := by
    have := burnsideF4k_polyRefl c m hm hU z hz hnb hper 0 sx hx1 hx2
    rwa [hz0] at this
  have hrl : IsReflectionOn c sl (Set.range z) c.lv := by
    have := burnsideF4k_polyRefl c m hm hU z hz hnb hper 1 sl hl1 hl2
    rwa [hz1] at this
  have hWle : Subgroup.closure {sx, sl} ≤ setStab c (Set.range z) := by
    rw [Subgroup.closure_le]
    rintro s (rfl | rfl)
    · exact hrx.2.1
    · exact hrl.2.1
  have hmx : sx ∈ Subgroup.closure {sx, sl} := Subgroup.subset_closure (by simp)
  have hml : sl ∈ Subgroup.closure {sx, sl} := Subgroup.subset_closure (by simp)
  have hpow : ∀ k : ℕ, (sl * sx) ^ k ∈ Subgroup.closure {sx, sl} :=
    fun k => Subgroup.pow_mem _ (Subgroup.mul_mem _ hml hmx) k
  have hflag : ∀ g : c.G0, (∃ a e : ZMod (2 * m), Even a ∧ (e = 1 ∨ e = -1) ∧
      g • z 0 = burnsideF4k_pa_zf z m a ∧ g • z 1 = burnsideF4k_pa_zf z m (a + e)) →
      (g • z 0, g • z 1) ∈ Set.range (burnsideF4k_pa_flag (burnsideF4k_pa_zf z m)) := by
    rintro g ⟨a, e, ha, he, h0, h1⟩
    rw [h0, h1]
    exact burnsideF4k_pa_flag_mem hm _ ha he
  have horbW : MulAction.orbit (↥(Subgroup.closure {sx, sl})) (z 0, z 1) =
      Set.range (burnsideF4k_pa_flag (burnsideF4k_pa_zf z m)) := by
    ext p
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨a, e, ha, he, hw⟩ := burnsideF4k_pa_closure_act _ hsx hsl w.2
      refine hflag (w : c.G0) ⟨a, e, ha, he, ?_, ?_⟩
      · rw [hz0', hw, mul_zero, add_zero]
      · rw [hz1', hw, mul_one]
    · rintro ⟨⟨k, b⟩, rfl⟩
      cases b
      · refine ⟨⟨(sl * sx) ^ (k : ℕ) * sx, Subgroup.mul_mem _ (hpow k) hmx⟩, ?_⟩
        show (((sl * sx) ^ (k : ℕ) * sx) • z 0, ((sl * sx) ^ (k : ℕ) * sx) • z 1) =
          (burnsideF4k_pa_zf z m (2 * ((k : ℕ) : ZMod (2 * m))),
            burnsideF4k_pa_zf z m (2 * ((k : ℕ) : ZMod (2 * m)) + -1))
        rw [hz0', hz1', burnsideF4k_pa_pow_mul_act _ hsx hsl,
          burnsideF4k_pa_pow_mul_act _ hsx hsl, sub_zero, sub_eq_add_neg]
      · refine ⟨⟨(sl * sx) ^ (k : ℕ), hpow k⟩, ?_⟩
        show ((sl * sx) ^ (k : ℕ) • z 0, (sl * sx) ^ (k : ℕ) • z 1) =
          (burnsideF4k_pa_zf z m (2 * ((k : ℕ) : ZMod (2 * m))),
            burnsideF4k_pa_zf z m (2 * ((k : ℕ) : ZMod (2 * m)) + 1))
        rw [hz0', hz1', burnsideF4k_pa_pow_act _ hsx hsl,
          burnsideF4k_pa_pow_act _ hsx hsl, add_zero]
  have horbS : MulAction.orbit (↥(setStab c (Set.range z))) (z 0, z 1) =
      Set.range (burnsideF4k_pa_flag (burnsideF4k_pa_zf z m)) := by
    apply Set.Subset.antisymm
    · intro p hp
      rw [MulAction.mem_orbit_iff] at hp
      obtain ⟨g, rfl⟩ := hp
      have hg : (g : c.G0) ∈ setStab c (Set.range z) := g.2
      obtain ⟨k, hk⟩ := burnsideF4k_setStab_mem c hg ⟨0, rfl⟩
      have hga : (g : c.G0) • z 0 = burnsideF4k_pa_zf z m (k : ZMod (2 * m)) := by
        rw [hcast k, hk]
      refine hflag (g : c.G0) ?_
      have heven : Even (k : ZMod (2 * m)) := by
        have h := (burnsideF4k_pa_zf_col_iff hbip hm hz hper 0 (k : ZMod (2 * m))).mp
          (by rw [← hga, CosetGeom.vtype_smul, hz0'])
        rwa [sub_zero] at h
      have hadj : c.graph.Adj (burnsideF4k_pa_zf z m (k : ZMod (2 * m))) ((g : c.G0) • z 1) := by
        rw [← hga]
        exact (CosetGeom.smul_adj (g : c.G0)).mpr (hz 0)
      rcases burnsideF4k_pa_zf_nbr hconn hbip hm hU hz hnb hper _
          (burnsideF4k_setStab_mem c hg ⟨1, rfl⟩) hadj with h | h
      · exact ⟨_, 1, heven, Or.inl rfl, hga, h⟩
      · exact ⟨_, -1, heven, Or.inr rfl, hga, by rw [h, sub_eq_add_neg]⟩
    · rw [← horbW]
      intro p hp
      rw [MulAction.mem_orbit_iff] at hp ⊢
      obtain ⟨w, rfl⟩ := hp
      exact ⟨⟨(w : c.G0), hWle w.2⟩, rfl⟩
  have htrans : ∀ u ∈ Set.range z, ∀ v ∈ Set.range z,
      CosetGeom.vtype u = CosetGeom.vtype v → ∃ w ∈ Subgroup.closure {sx, sl}, w • u = v := by
    rintro u ⟨i, rfl⟩ v ⟨j, rfl⟩ huv
    rw [← hcast i] at huv
    rw [← hcast j] at huv
    obtain ⟨r, hr⟩ :=
      (burnsideF4k_pa_zf_col_iff hbip hm hz hper (i : ZMod (2 * m)) j).mp huv.symm
    refine ⟨(sl * sx) ^ r.val, hpow r.val, ?_⟩
    rw [← hcast i, ← hcast j, burnsideF4k_pa_pow_act _ hsx hsl, ZMod.natCast_zmod_val]
    congr 1
    linear_combination -hr
  have hcard : (Set.range (burnsideF4k_pa_flag (burnsideF4k_pa_zf z m))).ncard = 2 * m := by
    rw [Set.ncard_range_of_injective (burnsideF4k_pa_flag_inj hm hinj), Nat.card_prod,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool,
      mul_comm]
  refine ⟨⟨MulAction.mem_stabilizer_iff.mpr hrx.2.2.1, MulAction.mem_stabilizer_iff.mpr hrl.2.2.1,
    hrx, hrl, ?_, htrans⟩, ?_⟩
  · show ((pointwiseStab c (Set.range z)).subgroupOf (Subgroup.closure {sx, sl})).index = 2 * m
    rw [← burnsideF4k_pa_stab_eq c hm hU hz hnb hper hWle, MulAction.index_stabilizer, horbW,
      hcard]
  · rw [← burnsideF4k_pa_stab_eq c hm hU hz hnb hper le_rfl, MulAction.index_stabilizer,
      horbS, hcard]

end CFSG.ASVolI
