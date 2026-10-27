module

public import CFSG.Quasithin.Recognition.St84.Basic
public import CFSG.Quasithin.Recognition.St84.Singularity
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Arc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3SixLoc
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T
open scoped Pointwise

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

@[expose] def G1 (x : V) : Subgroup G :=
  MulAction.stabilizer G x ⊓ fixSet G (Γ.neighborSet x)

@[expose] def G1Set (W : Set V) : Subgroup G :=
  ⨅ x ∈ W, G1 (Γ := Γ) (G := G) x

@[expose] def Gm (m : ℕ) (x : V) : Subgroup G :=
  fixSet G {y | Γ.dist x y ≤ m}

@[expose] def GmPair (m : ℕ) (x y : V) : Subgroup G :=
  Gm (Γ := Γ) (G := G) m x ⊓ Gm (Γ := Γ) (G := G) m y

theorem mem_G1 {x : V} {g : G} :
    g ∈ G1 (Γ := Γ) (G := G) x ↔ g • x = x ∧ ∀ y, Γ.Adj x y → g • y = y := by
  constructor
  · intro hg
    rw [G1, Subgroup.mem_inf, mem_fixSet] at hg
    exact ⟨MulAction.mem_stabilizer_iff.mp hg.1, fun y hy => hg.2 y hy⟩
  · intro hg
    rw [G1, Subgroup.mem_inf, mem_fixSet]
    exact ⟨MulAction.mem_stabilizer_iff.mpr hg.1, fun y hy => hg.2 y hy⟩

theorem G1_le_stabilizer (x : V) : G1 (Γ := Γ) (G := G) x ≤ MulAction.stabilizer G x :=
  inf_le_left

theorem G1_le_fixSet (x : V) :
    G1 (Γ := Γ) (G := G) x ≤ fixSet G (Γ.neighborSet x) := inf_le_right

theorem G1_fixes (x : V) : ∀ g ∈ G1 (Γ := Γ) (G := G) x, g • x = x :=
  fun g hg => MulAction.mem_stabilizer_iff.mp (G1_le_stabilizer x hg)

theorem G1_fixes_adj {x y : V} (hxy : Γ.Adj x y) :
    ∀ g ∈ G1 (Γ := Γ) (G := G) x, g • y = y :=
  fun g hg => (mem_G1.mp hg).2 y hxy

theorem mem_G1Set {W : Set V} {g : G} :
    g ∈ G1Set (Γ := Γ) (G := G) W ↔ ∀ x ∈ W, g ∈ G1 (Γ := Γ) (G := G) x := by
  simp [G1Set]

theorem G1Set_fixes {W : Set V} {x : V} (hx : x ∈ W) {g : G}
    (hg : g ∈ G1Set (Γ := Γ) (G := G) W) : g • x = x :=
  G1_fixes x g ((mem_G1Set.mp hg) x hx)

theorem G1Set_mono {W W' : Set V} (h : W' ⊆ W) :
    G1Set (Γ := Γ) (G := G) W ≤ G1Set (Γ := Γ) (G := G) W' := by
  intro g hg
  rw [mem_G1Set] at hg ⊢
  exact fun x hx => hg x (h hx)

theorem mem_Gm {m : ℕ} {x : V} {g : G} :
    g ∈ Gm (Γ := Γ) (G := G) m x ↔ ∀ y, Γ.dist x y ≤ m → g • y = y := by
  simp [Gm, mem_fixSet]

theorem Gm_le_stabilizer (m : ℕ) (x : V) :
    Gm (Γ := Γ) (G := G) m x ≤ MulAction.stabilizer G x := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  exact (mem_Gm.mp hg) x (by simp)

theorem Gm_mono {m n : ℕ} (hmn : m ≤ n) (x : V) :
    Gm (Γ := Γ) (G := G) n x ≤ Gm (Γ := Γ) (G := G) m x := by
  intro g hg
  simp only [Gm, mem_fixSet, Set.mem_setOf_eq] at hg ⊢
  intro y hy
  exact hg y (hy.trans hmn)

theorem GmPair_le_left (m : ℕ) (x y : V) :
    GmPair (Γ := Γ) (G := G) m x y ≤ Gm (Γ := Γ) (G := G) m x := inf_le_left

theorem GmPair_le_right (m : ℕ) (x y : V) :
    GmPair (Γ := Γ) (G := G) m x y ≤ Gm (Γ := Γ) (G := G) m y := inf_le_right

theorem conjSub_G1 (h : Hyp30 Γ G) (g : G) (x : V) :
    conjSub g (G1 (Γ := Γ) (G := G) x) = G1 (Γ := Γ) (G := G) (g • x) := by
  rw [G1, G1, conjSub_inf, stabilizer_smul_eq_conjSub]
  congr 1
  have hnb : Γ.neighborSet (g • x) = g • Γ.neighborSet x := by
    ext y
    rw [Set.mem_smul_set]
    constructor
    · intro hy
      exact ⟨g⁻¹ • y, (h.adj_smul g x (g⁻¹ • y)).1 (by simpa using hy), by simp⟩
    · rintro ⟨z, hz, rfl⟩
      exact (h.adj_smul g x z).2 hz
  rw [hnb, ← conjSub_fixSet]

theorem finite_G1 (h : Hyp30 Γ G) (x : V) : Finite (G1 (Γ := Γ) (G := G) x) := by
  haveI : Finite (MulAction.stabilizer G x) := h.finite_stab x
  exact Finite.of_injective (Subgroup.inclusion (G1_le_stabilizer x))
    (Subgroup.inclusion_injective _)

theorem finite_G1Set_of_mem (h : Hyp30 Γ G) {W : Set V} {x : V} (hx : x ∈ W) :
    Finite (G1Set (Γ := Γ) (G := G) W) := by
  have hle : G1Set (Γ := Γ) (G := G) W ≤ G1 (Γ := Γ) (G := G) x := by
    intro g hg
    exact (mem_G1Set.mp hg) x hx
  haveI := finite_G1 h x
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)

@[expose] def snocArc {m : ℕ} (P : Arc Γ m) (x : V) (hx : Γ.Adj (P.vert m) x)
    (hx' : 1 ≤ m → x ≠ P.vert (m - 1)) : Arc Γ (m + 1) where
  vert i := if i ≤ m then P.vert i else x
  adj i hi := by
    by_cases h : i + 1 ≤ m
    · simp only [show i ≤ m by omega, h, ↓reduceIte]
      exact P.adj i (by omega)
    · have h' : i = m := by omega
      subst h'
      simp only [le_refl, h, ↓reduceIte]
      exact hx
  nb i hi := by
    by_cases h : i + 2 ≤ m
    · simp only [show i ≤ m by omega, h, ↓reduceIte]
      exact P.nb i h
    · have h' : i = m - 1 := by omega
      have hm : 1 ≤ m := by omega
      have h'' : i + 2 = m + 1 := by omega
      simp only [show i ≤ m by omega, h, ↓reduceIte]
      rw [h']
      exact (hx' hm).symm

@[simp] theorem snocArc_vert_last {m : ℕ} (P : Arc Γ m) (x : V) (hx : Γ.Adj (P.vert m) x)
    (hx' : 1 ≤ m → x ≠ P.vert (m - 1)) :
    (snocArc P x hx hx').vert (m + 1) = x := by
  simp [snocArc]

theorem snocArc_vert_le {m : ℕ} (P : Arc Γ m) (x : V) (hx : Γ.Adj (P.vert m) x)
    (hx' : 1 ≤ m → x ≠ P.vert (m - 1)) {i : ℕ} (hi : i ≤ m) :
    (snocArc P x hx hx').vert i = P.vert i := by
  simp [snocArc, hi]

theorem snocArc_vert {m : ℕ} (P : Arc Γ m) (x : V) (hx : Γ.Adj (P.vert m) x)
    (hx' : 1 ≤ m → x ≠ P.vert (m - 1)) (i : ℕ) :
    (snocArc P x hx hx').vert i = if i ≤ m then P.vert i else x := rfl

@[expose] def consArc {m : ℕ} (P : Arc Γ m) (x : V) (hx : Γ.Adj x (P.vert 0))
    (hx' : 1 ≤ m → x ≠ P.vert 1) : Arc Γ (m + 1) where
  vert i := if i = 0 then x else P.vert (i - 1)
  adj i hi := by
    by_cases h0 : i = 0
    · subst h0
      simpa using hx
    · have hi1 : 1 ≤ i := by omega
      have hi' : i - 1 < m := by omega
      simp only [h0, if_false, ↓reduceIte, if_true]
      rw [show i + 1 - 1 = i by omega, show i = (i - 1) + 1 by omega]
      exact P.adj (i - 1) hi'
  nb i hi := by
    by_cases h0 : i = 0
    · subst h0
      have hm : 1 ≤ m := by omega
      simpa [hx'] using hx' hm
    · by_cases h1 : i = 1
      · subst h1
        have hm : 2 ≤ m := by omega
        simpa using P.nb 0 (by omega)
      · have hi2 : 2 ≤ i := by omega
        have hi' : i - 1 + 2 ≤ m := by omega
        simp only [h0, h1, if_false, ↓reduceIte]
        rw [show i + 2 - 1 = i - 1 + 2 by omega]
        exact P.nb (i - 1) hi'

@[simp] theorem consArc_vert_zero {m : ℕ} (P : Arc Γ m) (x : V) (hx : Γ.Adj x (P.vert 0))
    (hx' : 1 ≤ m → x ≠ P.vert 1) : (consArc P x hx hx').vert 0 = x := by
  simp [consArc]

theorem consArc_vert_succ {m : ℕ} (P : Arc Γ m) (x : V) (hx : Γ.Adj x (P.vert 0))
    (hx' : 1 ≤ m → x ≠ P.vert 1) (i : ℕ) :
    (consArc P x hx hx').vert (i + 1) = P.vert i := by
  simp [consArc]

@[expose] def arcCast {m n : ℕ} (h : m = n) (P : Arc Γ m) : Arc Γ n := h ▸ P

@[simp] theorem arcCast_vert {m n : ℕ} (h : m = n) (P : Arc Γ m) (i : ℕ) :
    (arcCast h P).vert i = P.vert i := by cases h; rfl

theorem suffixArc_vert_apply {m k : ℕ} (P : Arc Γ m) (hk : k ≤ m) (i : ℕ) :
    (suffixArc P k hk).vert i = P.vert (i + (m - k)) := rfl

theorem line_arc_vert (T : KTrack (Γ := Γ) (G := G)) (a : ℤ) (n : ℕ) (i : ℕ) :
    (T.line.arc a n).vert i = T.line.vert (a + (i : ℤ)) := by
  simp [Line.arc]

theorem line_arc_rev_vert (T : KTrack (Γ := Γ) (G := G)) (a : ℤ) (n : ℕ) (i : ℕ) :
    (T.line.arc a n).rev.vert i = T.line.vert (a + ((n - i : ℕ) : ℤ)) := by
  rw [Arc.rev_vert, line_arc_vert]

@[expose] def arcStab {m : ℕ} (P : Arc Γ m) : Subgroup G :=
  stabRange G P.vert 0 m

theorem mem_arcStab {m : ℕ} (P : Arc Γ m) {g : G} :
    g ∈ arcStab (G := G) P ↔ ∀ i, i ≤ m → g • P.vert i = P.vert i := by
  rw [arcStab, mem_stabRange]
  constructor
  · intro h i hi
    exact h i (Nat.zero_le _) hi
  · intro h i hi0 hi
    exact h i hi

theorem arcStab_le_stabilizer_last {m : ℕ} (P : Arc Γ m) :
    arcStab (G := G) P ≤ MulAction.stabilizer G (P.vert m) := by
  intro g hg
  exact MulAction.mem_stabilizer_iff.mpr ((mem_arcStab P).mp hg m le_rfl)

theorem mem_arcStab_of_forall {m : ℕ} (P : Arc Γ m) {g : G}
    (h : ∀ i, i ≤ m → g • P.vert i = P.vert i) : g ∈ arcStab (G := G) P :=
  (mem_arcStab P).mpr h

theorem arcStab_le_stabilizer {m : ℕ} (P : Arc Γ m) {i : ℕ} (hi : i ≤ m) :
    arcStab (G := G) P ≤ MulAction.stabilizer G (P.vert i) := by
  intro g hg
  exact MulAction.mem_stabilizer_iff.mpr ((mem_arcStab P).mp hg i hi)

theorem even_nontransitive (h : Hyp30 Γ G) (hs : IsSingularity Γ G s) (hev : Even s) :
    ∀ m, s ≤ m → ∀ P : Arc Γ m,
      ¬ LeftTransitive Γ G P.vert 0 m ∧ ¬ RightTransitive Γ G P.vert 0 m := by
  have hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b :=
    fun v a b ha hb => h.locTrans ha hb
  have hd := singularity_dichotomy h.isTree h.adj_smul hloc
    h.edgeTrans h.preservesParts hs
  rcases hd with ⟨heven, hnt⟩ | ⟨hodd, -⟩
  · exact hnt
  · exact absurd hev (Nat.not_even_iff_odd.mpr hodd)

private theorem closure_reaches_of_K_b
    (hadj : ∀ (g : G) (x y : V), Γ.Adj (g • x) (g • y) ↔ Γ.Adj x y)
    {K : Subgroup G} {b : G} {v u w : V}
    (hvw : Γ.Adj v w) (hwu : w ≠ u)
    (hbv : b • v = v) (hbu : b • u = u) (hbw : b • w ≠ w)
    (hKv : ∀ k ∈ K, k • v = v) (hKw : ∀ k ∈ K, k • w = w)
    (hKtrans : ∀ x y, Γ.Adj v x → x ≠ u → x ≠ w → Γ.Adj v y → y ≠ u → y ≠ w →
      ∃ k ∈ K, k • x = y) :
    ∀ x, Γ.Adj v x → x ≠ u → ∃ h ∈ Subgroup.closure ((K : Set G) ∪ {b}), h • x = w := by
  intro x hvx hxu
  by_cases hxw : x = w
  · subst hxw
    exact ⟨1, Subgroup.one_mem _, one_smul _ _⟩
  · have hbx_adj : Γ.Adj v (b • x) := by
      have := (hadj b v x).2 hvx
      rwa [hbv] at this
    have hbx_u : b • x ≠ u := by
      intro h
      apply hxu
      have : b • x = b • u := by rw [hbu]; exact h
      exact MulAction.injective b this
    by_cases hbxw : b • x = w
    · exact ⟨b, Subgroup.subset_closure (Or.inr (by simp)), hbxw⟩
    · have hbw_adj : Γ.Adj v (b • w) := by
        have := (hadj b v w).2 hvw
        rwa [hbv] at this
      have hbw_u : b • w ≠ u := by
        intro h
        apply hwu
        have : b • w = b • u := by rw [hbu]; exact h
        exact MulAction.injective b this
      obtain ⟨k, hkK, hk⟩ :=
        hKtrans (b • x) (b • w) hbx_adj hbx_u hbxw hbw_adj hbw_u hbw
      refine ⟨b⁻¹ * k * b, ?_, ?_⟩
      · exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr (by simp))))
            (Subgroup.subset_closure (Or.inl hkK)))
          (Subgroup.subset_closure (Or.inr (by simp)))
      · calc (b⁻¹ * k * b) • x = b⁻¹ • (k • (b • x)) := by simp [mul_smul]
          _ = b⁻¹ • (b • w) := by rw [hk]
          _ = w := by simp

@[expose] def KTrack.rev (T : KTrack (Γ := Γ) (G := G)) : KTrack Γ G where
  line := T.line.rev
  τ := T.τ⁻¹
  trans i := by
    rw [Line.rev_vert, Line.rev_vert, inv_smul_eq_iff]
    have h := T.trans (-i - 2)
    rw [show -i - 2 + 2 = -i by omega] at h
    rw [show -(i + 2) = -i - 2 by omega]
    exact h.symm
  K := T.K
  K_fix k hk i := by
    rw [Line.rev_vert]
    exact T.K_fix k hk (-i)
  τ_norm := inv_mem T.τ_norm

@[expose] def lineStab (T : KTrack (Γ := Γ) (G := G)) : Subgroup G :=
  fixSet G (Set.range T.line.vert)

theorem mem_lineStab (T : KTrack (Γ := Γ) (G := G)) {g : G} :
    g ∈ lineStab T ↔ ∀ i : ℤ, g • T.line.vert i = T.line.vert i := by
  simp [lineStab, mem_fixSet]

theorem lineStab_le_arcStab (T : KTrack (Γ := Γ) (G := G)) (i : ℤ) (m : ℕ) :
    lineStab T ≤ arcStab (G := G) (T.line.arc i m) := by
  intro g hg
  rw [mem_arcStab]
  intro k hk
  change g • T.line.vert (i + k) = T.line.vert (i + k)
  exact (mem_lineStab T).mp hg (i + k)

theorem K_trans_off (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (i : ℤ) {a b : V} (ha : Γ.Adj (T.line.vert i) a) (ha1 : a ≠ T.line.vert (i - 1))
    (ha2 : a ≠ T.line.vert (i + 1)) (hb : Γ.Adj (T.line.vert i) b)
    (hb1 : b ≠ T.line.vert (i - 1)) (hb2 : b ≠ T.line.vert (i + 1)) :
    ∃ k ∈ T.K, k • a = b := hK i a b ha hb ha1 ha2 hb1 hb2

theorem not_rightSingular_of_move_right (h : Hyp30 Γ G) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (j : ℤ) {b : G}
    (hbarc : b ∈ arcStab (G := G) (T.line.arc (j - (s : ℤ)) s))
    (hbmove : b • T.line.vert (j + 1) ≠ T.line.vert (j + 1)) :
    False := by
  let P : Arc Γ s := T.line.arc (j - (s : ℤ)) s
  have hPs : P.vert s = T.line.vert j := by
    simp only [P, Line.arc]
    congr 1
    push_cast
    ring
  have hPsm : P.vert (s - 1) = T.line.vert (j - 1) := by
    simp only [P, Line.arc]
    congr 1
    push_cast
    omega
  have hbv : b • T.line.vert j = T.line.vert j := by
    have := (mem_arcStab P).mp hbarc s le_rfl
    rwa [hPs] at this
  have hbu : b • T.line.vert (j - 1) = T.line.vert (j - 1) := by
    have := (mem_arcStab P).mp hbarc (s - 1) (by omega)
    rwa [hPsm] at this
  have hvw : Γ.Adj (T.line.vert j) (T.line.vert (j + 1)) := T.line.adj j
  have hwu : T.line.vert (j + 1) ≠ T.line.vert (j - 1) := by
    have h := T.line.nb (j - 1)
    rw [show j - 1 + 2 = j + 1 by omega] at h
    exact h.symm
  have hKfix : ∀ k ∈ T.K, ∀ i : ℤ, k • T.line.vert i = T.line.vert i :=
    fun k hk i => T.K_fix k hk i
  have hreach := closure_reaches_of_K_b (Γ := Γ) (G := G) h.adj_smul
    (K := T.K) (b := b) (v := T.line.vert j) (u := T.line.vert (j - 1))
    (w := T.line.vert (j + 1)) hvw hwu hbv hbu hbmove
    (fun k hk => hKfix k hk j) (fun k hk => hKfix k hk (j + 1))
    (fun x y hx hxu hxw hy hyu hyw => hK j x y hx hy hxu hxw hyu hyw)
  let H : Subgroup G := Subgroup.closure ((T.K : Set G) ∪ {b})
  have hHle : H ≤ arcStab (G := G) P := by
    apply (Subgroup.closure_le _).mpr
    rintro g (hgK | hgb)
    · exact (lineStab_le_arcStab T (j - (s : ℤ)) s)
        ((mem_lineStab T).mpr (fun i => hKfix g hgK i))
    · have hgb' : g = b := by simpa using hgb
      simpa [hgb'] using hbarc
  have htrans : RightTransitive Γ G P.vert 0 s := by
    intro a c ha hau hc hcu
    have ha' : Γ.Adj (T.line.vert j) a := by simpa [hPs] using ha
    have hau' : a ≠ T.line.vert (j - 1) := by simpa [hPsm] using hau
    have hc' : Γ.Adj (T.line.vert j) c := by simpa [hPs] using hc
    have hcu' : c ≠ T.line.vert (j - 1) := by simpa [hPsm] using hcu
    obtain ⟨haH, haHmem, hha⟩ := hreach a ha' hau'
    obtain ⟨hcH, hcHmem, hhc⟩ := hreach c hc' hcu'
    refine ⟨hcH⁻¹ * haH, ?_, ?_⟩
    · exact hHle (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcHmem) haHmem)
    · calc (hcH⁻¹ * haH) • a = hcH⁻¹ • (haH • a) := by rw [mul_smul]
        _ = hcH⁻¹ • T.line.vert (j + 1) := by rw [hha]
        _ = c := by
          have := congrArg (fun z => hcH⁻¹ • z) hhc
          simpa using this.symm
  exact (even_nontransitive h hs hev s le_rfl P).2 htrans

theorem not_leftSingular_of_move_left (h : Hyp30 Γ G) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (j : ℤ) {b : G}
    (hbarc : b ∈ arcStab (G := G) (T.line.arc j s))
    (hbmove : b • T.line.vert (j - 1) ≠ T.line.vert (j - 1)) :
    False := by
  let P : Arc Γ s := T.line.arc j s
  have hP0 : P.vert 0 = T.line.vert j := by
    simp [P, Line.arc]
  have hP1 : P.vert 1 = T.line.vert (j + 1) := by
    simp [P, Line.arc]
  have hbv : b • T.line.vert j = T.line.vert j := by
    have := (mem_arcStab P).mp hbarc 0 (by omega)
    rwa [hP0] at this
  have hbu : b • T.line.vert (j + 1) = T.line.vert (j + 1) := by
    have := (mem_arcStab P).mp hbarc 1 (by omega)
    rwa [hP1] at this
  have hvw : Γ.Adj (T.line.vert j) (T.line.vert (j - 1)) := by
    have h := (T.line.adj (j - 1)).symm
    rwa [show j - 1 + 1 = j by omega] at h
  have hwu : T.line.vert (j - 1) ≠ T.line.vert (j + 1) := by
    have h := T.line.nb (j - 1)
    rw [show j - 1 + 2 = j + 1 by omega] at h
    exact h
  have hKfix : ∀ k ∈ T.K, ∀ i : ℤ, k • T.line.vert i = T.line.vert i :=
    fun k hk i => T.K_fix k hk i
  have hreach := closure_reaches_of_K_b (Γ := Γ) (G := G) h.adj_smul
    (K := T.K) (b := b) (v := T.line.vert j) (u := T.line.vert (j + 1))
    (w := T.line.vert (j - 1)) hvw hwu hbv hbu hbmove
    (fun k hk => hKfix k hk j) (fun k hk => hKfix k hk (j - 1))
    (fun x y hx hxu hxw hy hyu hyw => hK j x y hx hy hxw hxu hyw hyu)
  let H : Subgroup G := Subgroup.closure ((T.K : Set G) ∪ {b})
  have hHle : H ≤ arcStab (G := G) P := by
    apply (Subgroup.closure_le _).mpr
    rintro g (hgK | hgb)
    · exact (lineStab_le_arcStab T j s)
        ((mem_lineStab T).mpr (fun i => hKfix g hgK i))
    · have hgb' : g = b := by simpa using hgb
      simpa [hgb'] using hbarc
  have htrans : LeftTransitive Γ G P.vert 0 s := by
    intro a c ha hau hc hcu
    have ha' : Γ.Adj (T.line.vert j) a := by simpa [hP0] using ha
    have hau' : a ≠ T.line.vert (j + 1) := by simpa [hP1] using hau
    have hc' : Γ.Adj (T.line.vert j) c := by simpa [hP0] using hc
    have hcu' : c ≠ T.line.vert (j + 1) := by simpa [hP1] using hcu
    obtain ⟨haH, haHmem, hha⟩ := hreach a ha' hau'
    obtain ⟨hcH, hcHmem, hhc⟩ := hreach c hc' hcu'
    refine ⟨hcH⁻¹ * haH, ?_, ?_⟩
    · exact hHle (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcHmem) haHmem)
    · calc (hcH⁻¹ * haH) • a = hcH⁻¹ • (haH • a) := by rw [mul_smul]
        _ = hcH⁻¹ • T.line.vert (j - 1) := by rw [hha]
        _ = c := by
          have := congrArg (fun z => hcH⁻¹ • z) hhc
          simpa using this.symm
  exact (even_nontransitive h hs hev s le_rfl P).1 htrans

private theorem fix_succ_of_arc_right (h : Hyp30 Γ G) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) {i j : ℤ} {b : G}
    (hj : i + (s : ℤ) ≤ j)
    (hseg : ∀ k : ℤ, i ≤ k → k ≤ j → b • T.line.vert k = T.line.vert k) :
    b • T.line.vert (j + 1) = T.line.vert (j + 1) := by
  by_contra hne
  have hbarc : b ∈ arcStab (G := G) (T.line.arc (j - (s : ℤ)) s) := by
    rw [mem_arcStab]
    intro l hl
    exact hseg ((j - (s : ℤ)) + (l : ℤ)) (by omega) (by omega)
  exact not_rightSingular_of_move_right h T hK hs hev hs6 j hbarc hne

private theorem fix_pred_of_arc_left (h : Hyp30 Γ G) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) {i j : ℤ} {b : G}
    (hj : j ≤ i)
    (hseg : ∀ k : ℤ, j ≤ k → k ≤ i + (s : ℤ) → b • T.line.vert k = T.line.vert k) :
    b • T.line.vert (j - 1) = T.line.vert (j - 1) := by
  by_contra hne
  have hbarc : b ∈ arcStab (G := G) (T.line.arc j s) := by
    rw [mem_arcStab]
    intro l hl
    exact hseg (j + (l : ℤ)) (by omega) (by omega)
  exact not_leftSingular_of_move_left h T hK hs hev hs6 j hbarc hne

theorem arcStab_s_le_lineStab (h : Hyp30 Γ G) (hs : IsSingularity Γ G s) (hev : Even s)
    (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (i : ℤ) :
    arcStab (G := G) (T.line.arc i s) ≤ lineStab T := by
  intro b hb
  rw [mem_lineStab]
  have hbase : ∀ k : ℤ, i ≤ k → k ≤ i + (s : ℤ) → b • T.line.vert k = T.line.vert k := by
    intro k hik hk
    have hb' := (mem_arcStab (T.line.arc i s)).mp hb
    set l : ℕ := (k - i).toNat with hl
    have hlk : (l : ℤ) = k - i := Int.toNat_of_nonneg (by omega)
    have hls : l ≤ s := by omega
    have h := hb' l hls
    simpa [Line.arc, hlk] using h
  have hfwd : ∀ j : ℤ, i + (s : ℤ) ≤ j → ∀ k : ℤ, i ≤ k → k ≤ j →
      b • T.line.vert k = T.line.vert k := by
    intro j hj
    refine Int.leInduction (m := i + (s : ℤ))
      (motive := fun j _ => ∀ k : ℤ, i ≤ k → k ≤ j → b • T.line.vert k = T.line.vert k)
      hbase ?_ j hj
    intro j hj ih k hik hkj
    by_cases hk : k ≤ j
    · exact ih k hik hk
    · have hk' : k = j + 1 := by omega
      subst hk'
      exact fix_succ_of_arc_right h T hK hs hev hs6 hj ih
  have hbwd : ∀ j : ℤ, j ≤ i → ∀ k : ℤ, j ≤ k → k ≤ i + (s : ℤ) →
      b • T.line.vert k = T.line.vert k := by
    intro j hj
    refine Int.leInductionDown (m := i)
      (motive := fun j _ => ∀ k : ℤ, j ≤ k → k ≤ i + (s : ℤ) →
        b • T.line.vert k = T.line.vert k)
      hbase ?_ j hj
    intro j hj ih k hjk hk
    by_cases hjk' : j ≤ k
    · exact ih k hjk' hk
    · have hk' : k = j - 1 := by omega
      subst hk'
      exact fix_pred_of_arc_left h T hK hs hev hs6 hj ih
  intro k
  by_cases hk : i + (s : ℤ) ≤ k
  · exact hfwd k hk k (by omega) le_rfl
  · by_cases hki : i ≤ k
    · exact hbase k hki (by omega)
    · exact hbwd k (by omega) k le_rfl (by omega)

theorem stabilizer_le_normalizer_G1 (h : Hyp30 Γ G) (x : V) :
    MulAction.stabilizer G x ≤ Subgroup.normalizer (G1 (Γ := Γ) (G := G) x : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hconj : conjSub g (G1 (Γ := Γ) (G := G) x) = G1 (Γ := Γ) (G := G) x := by
      rw [conjSub_G1 h, MulAction.mem_stabilizer_iff.mp hg]
    have : g * y * g⁻¹ ∈ conjSub g (G1 (Γ := Γ) (G := G) x) :=
      mul_mem_conjSub (g := g) hy
    rwa [hconj] at this
  · intro hy
    have hconj : conjSub g⁻¹ (G1 (Γ := Γ) (G := G) x) = G1 (Γ := Γ) (G := G) x := by
      rw [conjSub_G1 h, MulAction.mem_stabilizer_iff.mp (inv_mem hg)]
    have hmem : g⁻¹ * (g * y * g⁻¹) * g ∈ conjSub g⁻¹ (G1 (Γ := Γ) (G := G) x) := by
      simpa using mul_mem_conjSub (g := g⁻¹) hy
    rw [hconj] at hmem
    simpa [mul_assoc] using hmem

private theorem normal_fixes_of_twoTransitive_set
    {Ω : Set V} {H N : Subgroup G} (hNleH : N ≤ H)
    (hNnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hHΩ : ∀ g ∈ H, ∀ x ∈ Ω, g • x ∈ Ω)
    (hH2 : ∀ a ∈ Ω, ∀ b ∈ Ω, a ≠ b → ∀ c ∈ Ω, ∀ d ∈ Ω, c ≠ d →
      ∃ h ∈ H, h • a = c ∧ h • b = d)
    (hNnot : ¬ ∀ a ∈ Ω, ∀ b ∈ Ω, ∃ n ∈ N, n • a = b) :
    ∀ n ∈ N, ∀ a ∈ Ω, n • a = a := by
  intro n hn a ha
  by_contra hne
  apply hNnot
  intro x hx y hy
  by_cases hxy : x = y
  · exact ⟨1, N.one_mem, by rw [hxy, one_smul]⟩
  · have hna_ne_a : a ≠ n • a := Ne.symm hne
    have hnaΩ : n • a ∈ Ω := hHΩ n (hNleH hn) a ha
    obtain ⟨h, hh, hx', hy'⟩ := hH2 a ha (n • a) hnaΩ hna_ne_a x hx y hy hxy
    refine ⟨h * n * h⁻¹, hNnorm h hh n hn, ?_⟩
    calc (h * n * h⁻¹) • x = h • (n • (h⁻¹ • x)) := by simp [mul_smul]
      _ = h • (n • a) := by rw [show h⁻¹ • x = a by rw [← hx', inv_smul_smul]]
      _ = y := hy'

theorem exists_smul_to_line (h : Hyp30 Γ G) (T : KTrack (Γ := Γ) (G := G)) (v : V) :
    (∃ g : G, g • v = T.line.vert 0) ∨ (∃ g : G, g • v = T.line.vert 1) := by
  have horb := orbit_eq_even_of_adj h.isTree h.adj_smul h.edgeTrans h.preservesParts
    (T.line.adj 0) (fun u => h.exists_adj u)
  rcases Nat.even_or_odd (Γ.dist (T.line.vert 0) v) with he | ho
  · left
    have hv : v ∈ MulAction.orbit G (T.line.vert 0) := (horb.1 v).2 he
    obtain ⟨g, hg⟩ := hv
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  · right
    have hv : v ∈ MulAction.orbit G (T.line.vert 1) := (horb.2 v).2 ho
    obtain ⟨g, hg⟩ := hv
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

private theorem normal_fixes_of_twoTransitive {α : Type*} [MulAction G α]
    {H N : Subgroup G} (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hH2 : ∀ a b c d : α, a ≠ b → c ≠ d → ∃ h ∈ H, h • a = c ∧ h • b = d)
    (hNnot : ¬ ∀ a b : α, ∃ n ∈ N, n • a = b) :
    ∀ n ∈ N, ∀ a : α, n • a = a := by
  intro n hn a
  by_contra hne
  apply hNnot
  intro x y
  by_cases hxy : x = y
  · exact ⟨1, N.one_mem, by rw [hxy, one_smul]⟩
  · obtain ⟨h, hh, hx, hy⟩ := hH2 a (n • a) x y (Ne.symm hne) hxy
    refine ⟨h * n * h⁻¹, hN h hh n hn, ?_⟩
    calc (h * n * h⁻¹) • x = h • (n • (h⁻¹ • x)) := by simp [mul_smul]
      _ = h • (n • a) := by
        rw [show h⁻¹ • x = a by rw [← hx, inv_smul_smul]]
      _ = y := hy

theorem G1_inf_arcStab_le_G1_end (h : Hyp30 Γ G) (hs : IsSingularity Γ G s) (hev : Even s)
    (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (P : Arc Γ (s - 1)) :
    G1 (Γ := Γ) (G := G) (P.vert 0) ⊓ arcStab (G := G) P ≤
      G1 (Γ := Γ) (G := G) (P.vert (s - 1)) := by
  let H : Subgroup G := arcStab (G := G) P
  let N : Subgroup G := G1 (Γ := Γ) (G := G) (P.vert 0) ⊓ H
  let z : V := P.vert (s - 1)
  let u : V := P.vert (s - 2)
  let Ω : Set V := {x | Γ.Adj z x ∧ x ≠ u}
  have hreg : Regular Γ G P := hs.2.1 (s - 1) (by omega) (by omega) P
  have hHtrans : ∀ a ∈ Ω, ∀ b ∈ Ω, ∃ g ∈ H, g • a = b := by
    intro a ha b hb
    exact hreg.2 a b ha.1 ha.2 hb.1 hb.2
  have hpoint : ∀ p ∈ Ω, ∀ x ∈ Ω, x ≠ p → ∀ y ∈ Ω, y ≠ p →
      ∃ g ∈ H, g • p = p ∧ g • x = y := by
    intro p hp x hx hxp y hy hyp
    let m : ℕ := s - 1 + 1
    have hm : m = s := by omega
    have hmle : m ≤ s := by omega
    let Q : Arc Γ m := snocArc P p hp.1 (fun _ => hp.2)
    have hQ0 : Q.vert 0 = P.vert 0 := by
      change (snocArc P p hp.1 (fun _ => hp.2)).vert 0 = P.vert 0
      rw [snocArc_vert_le P p hp.1 (fun _ => hp.2) (by omega)]
    have hQlast : Q.vert m = p := by
      change (snocArc P p hp.1 (fun _ => hp.2)).vert (s - 1 + 1) = p
      exact snocArc_vert_last P p hp.1 (fun _ => hp.2)
    obtain ⟨j, g, hg⟩ : ∃ (j : ℤ) (g : G), g • P.vert 0 = T.line.vert j := by
      rcases exists_smul_to_line h T (P.vert 0) with ⟨g, hg⟩ | ⟨g, hg⟩
      · exact ⟨0, g, hg⟩
      · exact ⟨1, g, hg⟩
    obtain ⟨hmap, hhmap⟩ := arc_conj_of_le h.adj_smul (fun v a b ha hb => h.locTrans ha hb) hs hmle
      Q (T.line.arc j m) g (by rw [hQ0]; simpa [Line.arc] using hg)
    have hPmap : ∀ i : ℕ, i ≤ s - 1 → hmap • P.vert i = T.line.vert (j + (i : ℤ)) := by
      intro i hi
      have h1 : Q.vert i = P.vert i := by
        change (snocArc P p hp.1 (fun _ => hp.2)).vert i = P.vert i
        exact snocArc_vert_le P p hp.1 (fun _ => hp.2) hi
      have h2 := hhmap i (by omega : i ≤ m)
      rw [h1] at h2
      rw [h2]
      simp [Line.arc]
    have hpmap : hmap • p = T.line.vert (j + (m : ℤ)) := by
      have h2 := hhmap m le_rfl
      rw [hQlast] at h2
      rw [h2]
      simp [Line.arc]
    have hzmap : hmap • z = T.line.vert (j + (m : ℤ) - 1) := by
      have h := hPmap (s - 1) le_rfl
      rw [show j + ((s - 1 : ℕ) : ℤ) = j + (m : ℤ) - 1 by omega] at h
      exact h
    have humap : hmap • u = T.line.vert (j + (m : ℤ) - 1 - 1) := by
      have h := hPmap (s - 2) (by omega)
      rw [show j + ((s - 2 : ℕ) : ℤ) = j + (m : ℤ) - 1 - 1 by omega] at h
      exact h
    have hxmap_u : hmap • x ≠ T.line.vert (j + (m : ℤ) - 1 - 1) := by
      intro hh
      exact hx.2 (MulAction.injective hmap (hh.trans humap.symm))
    have hxmap_p : hmap • x ≠ T.line.vert (j + (m : ℤ)) := by
      intro hh
      exact hxp (MulAction.injective hmap (hh.trans hpmap.symm))
    have hymap_u : hmap • y ≠ T.line.vert (j + (m : ℤ) - 1 - 1) := by
      intro hh
      exact hy.2 (MulAction.injective hmap (hh.trans humap.symm))
    have hymap_p : hmap • y ≠ T.line.vert (j + (m : ℤ)) := by
      intro hh
      exact hyp (MulAction.injective hmap (hh.trans hpmap.symm))
    have hxadj : Γ.Adj (T.line.vert (j + (m : ℤ) - 1)) (hmap • x) := by
      have hadj := (h.adj_smul hmap z x).2 hx.1
      rwa [hzmap] at hadj
    have hyadj : Γ.Adj (T.line.vert (j + (m : ℤ) - 1)) (hmap • y) := by
      have hadj := (h.adj_smul hmap z y).2 hy.1
      rwa [hzmap] at hadj
    have hxmap_p' : hmap • x ≠ T.line.vert (j + (m : ℤ) - 1 + 1) := by
      rwa [show j + (m : ℤ) - 1 + 1 = j + (m : ℤ) by omega]
    have hymap_p' : hmap • y ≠ T.line.vert (j + (m : ℤ) - 1 + 1) := by
      rwa [show j + (m : ℤ) - 1 + 1 = j + (m : ℤ) by omega]
    obtain ⟨k0, hk0K, hk0⟩ := hK (j + (m : ℤ) - 1) (hmap • x) (hmap • y)
      hxadj hyadj hxmap_u hxmap_p' hymap_u hymap_p' 
    refine ⟨hmap⁻¹ * k0 * hmap, ?_, ?_, ?_⟩
    · rw [mem_arcStab]
      intro i hi
      calc (hmap⁻¹ * k0 * hmap) • P.vert i
          = hmap⁻¹ • (k0 • (hmap • P.vert i)) := by simp [mul_smul]
        _ = hmap⁻¹ • (T.line.vert (j + (i : ℤ))) := by
          rw [hPmap i hi, T.K_fix k0 hk0K (j + (i : ℤ))]
        _ = P.vert i := by
          rw [← hPmap i hi]
          simp
    · calc (hmap⁻¹ * k0 * hmap) • p
          = hmap⁻¹ • (k0 • (hmap • p)) := by simp [mul_smul]
        _ = hmap⁻¹ • (T.line.vert (j + (m : ℤ))) := by
          rw [hpmap, T.K_fix k0 hk0K (j + (m : ℤ))]
        _ = p := by
          rw [← hpmap]
          simp
    · calc (hmap⁻¹ * k0 * hmap) • x
          = hmap⁻¹ • (k0 • (hmap • x)) := by simp [mul_smul]
        _ = hmap⁻¹ • (hmap • y) := by rw [hk0]
        _ = y := by simp
  have hH2 : ∀ a ∈ Ω, ∀ b ∈ Ω, a ≠ b → ∀ c ∈ Ω, ∀ d ∈ Ω, c ≠ d →
      ∃ g ∈ H, g • a = c ∧ g • b = d := by
    intro a ha b hb hab c hc d hd hcd
    obtain ⟨h1, h1H, h1a⟩ := hHtrans a ha c hc
    have h1bΩ : h1 • b ∈ Ω := by
      refine ⟨?_, ?_⟩
      · have hz : h1 • z = z := (mem_arcStab P).mp h1H (s - 1) le_rfl
        have hadj := (h.adj_smul h1 z b).2 hb.1
        rwa [hz] at hadj
      · have hu : h1 • u = u := (mem_arcStab P).mp h1H (s - 2) (by omega)
        exact fun h => hb.2 (MulAction.injective h1 (h.trans hu.symm))
    have h1bc : h1 • b ≠ c := by
      intro hh
      exact hab (MulAction.injective h1 (h1a.trans hh.symm))
    obtain ⟨h2, h2H, h2c, h2d⟩ := hpoint c hc (h1 • b) h1bΩ h1bc d hd (Ne.symm hcd)
    refine ⟨h2 * h1, H.mul_mem h2H h1H, ?_, ?_⟩
    · rw [mul_smul, h1a, h2c]
    · rw [mul_smul, h2d]
  have hHΩ : ∀ g ∈ H, ∀ x ∈ Ω, g • x ∈ Ω := by
    intro g hg x hx
    refine ⟨?_, ?_⟩
    · have hz : g • z = z := (mem_arcStab P).mp hg (s - 1) le_rfl
      have hadj := (h.adj_smul g z x).2 hx.1
      rwa [hz] at hadj
    · have hu : g • u = u := (mem_arcStab P).mp hg (s - 2) (by omega)
      exact fun h => hx.2 (MulAction.injective g (h.trans hu.symm))
  have hNnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    rw [Subgroup.mem_inf] at hn ⊢
    constructor
    · have hgG : g ∈ MulAction.stabilizer G (P.vert 0) :=
        arcStab_le_stabilizer P (by omega) hg
      exact (Subgroup.mem_normalizer_iff.mp
        (stabilizer_le_normalizer_G1 h (P.vert 0) hgG) n).mp hn.1
    · exact H.mul_mem (H.mul_mem hg hn.2) (H.inv_mem hg)
  have hNnot : ¬ ∀ a ∈ Ω, ∀ b ∈ Ω, ∃ n ∈ N, n • a = b := by
    intro htrans
    let m : ℕ := s - 1 + 1
    have hm : m = s := by omega
    have hmle : m ≤ s := by omega
    obtain ⟨u0, hu0adj, hu0ne⟩ := h.exists_adj_ne (P.vert 0) (P.vert 1)
    let P' : Arc Γ (s - 1) := P.rev
    have hP'last : P'.vert (s - 1) = P.vert 0 := by
      simp [P', Arc.rev_vert]
    have hP'pen : P'.vert (s - 2) = P.vert 1 := by
      simp [P', Arc.rev_vert, show s - 1 - (s - 2) = 1 by omega]
    let R0 : Arc Γ m := snocArc P' u0 (by rwa [hP'last]) (fun _ => by
        rw [show s - 1 - 1 = s - 2 by omega, hP'pen]
        exact hu0ne)
    let R : Arc Γ m := R0.rev
    have hRlast : R.vert m = z := by
      simp only [R, R0, Arc.rev_vert, Nat.sub_self]
      rw [snocArc_vert_le P' u0 (by rwa [hP'last]) (fun _ => by
        rw [show s - 1 - 1 = s - 2 by omega, hP'pen]
        exact hu0ne) (by omega)]
      simp [P', Arc.rev_vert, z]
    have hRpen : R.vert (m - 1) = u := by
      simp only [R, R0, Arc.rev_vert]
      rw [show m - (m - 1) = 1 by omega]
      rw [snocArc_vert_le P' u0 (by rwa [hP'last]) (fun _ => by
        rw [show s - 1 - 1 = s - 2 by omega, hP'pen]
        exact hu0ne) (by omega)]
      simp [P', Arc.rev_vert, show s - 1 - 1 = s - 2 by omega, u]
    have hRle : N ≤ arcStab (G := G) R := by
      intro n hn
      rw [Subgroup.mem_inf] at hn
      rw [mem_arcStab]
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        have hR0 : R.vert 0 = u0 := by
          simp only [R, Arc.rev_vert]
          exact snocArc_vert_last P' u0 (by rwa [hP'last]) (fun _ => by
        rw [show s - 1 - 1 = s - 2 by omega, hP'pen]
        exact hu0ne)
        rw [hR0]
        exact (mem_G1.mp hn.1).2 u0 hu0adj
      · have hi1 : 1 ≤ i := by omega
        have hRi : R.vert i = P.vert (i - 1) := by
          simp only [R, R0, Arc.rev_vert]
          rw [snocArc_vert_le P' u0 (by rwa [hP'last]) (fun _ => by
        rw [show s - 1 - 1 = s - 2 by omega, hP'pen]
        exact hu0ne)
            (by omega)]
          simp [P', Arc.rev_vert]
          congr 1
          omega
        rw [hRi]
        exact (mem_arcStab P).mp hn.2 (i - 1) (by omega)
    have hRtrans : RightTransitive Γ G R.vert 0 m := by
      intro a b ha hb hab hbb
      have haΩ : a ∈ Ω := by
        refine ⟨?_, ?_⟩
        · rwa [hRlast] at ha
        · rwa [hRpen] at hb
      have hbΩ : b ∈ Ω := by
        refine ⟨?_, ?_⟩
        · rwa [hRlast] at hab
        · rwa [hRpen] at hbb
      obtain ⟨n, hnN, hnab⟩ := htrans a haΩ b hbΩ
      exact ⟨n, hRle hnN, hnab⟩
    exact (even_nontransitive h hs hev m (by omega) R).2 hRtrans
  have hNfixΩ : ∀ n ∈ N, ∀ a ∈ Ω, n • a = a :=
    normal_fixes_of_twoTransitive_set (Ω := Ω) (H := H) (N := N) inf_le_right hNnorm hHΩ hH2 hNnot
  intro n hn
  rw [mem_G1]
  constructor
  · exact (mem_arcStab P).mp (Subgroup.mem_inf.mp hn).2 (s - 1) le_rfl
  · intro y hy
    by_cases hyu : y = u
    · subst hyu
      exact (mem_arcStab P).mp (Subgroup.mem_inf.mp hn).2 (s - 2) (by omega)
    · exact hNfixΩ n hn y ⟨hy, hyu⟩

private theorem F1_step_up (h : Hyp30 Γ G) (hs6 : 6 ≤ s)
    (T : KTrack (Γ := Γ) (G := G)) {A : Subgroup G} {F F1 : Set V}
    (hTF : ∀ i : ℤ, T.line.vert i ∈ F)
    (hneighbor_F : ∀ {x y : V}, x ∈ F1 → Γ.Adj x y → y ∈ F)
    (hTool : ∀ Q : Arc Γ (s - 1), (∀ k, k ≤ s - 1 → Q.vert k ∈ F) →
      Q.vert 0 ∈ F1 → Q.vert (s - 1) ∈ F1)
    (hstep : ∀ i : ℤ, T.line.vert i ∈ F1 → T.line.vert (i + (s - 1 : ℕ)) ∈ F1)
    {i : ℤ} (hi : T.line.vert i ∈ F1) (hi1 : T.line.vert (i + 1) ∈ F1) :
    T.line.vert (i + 2) ∈ F1 := by
  obtain ⟨x, hxadj, hx1, hx2⟩ := exists_adj_ne_ne (Γ := Γ)
    (v := T.line.vert (i + 1)) (a := T.line.vert i) (b := T.line.vert (i + 2))
    (h.three_le_card (T.line.vert (i + 1)))
  have hxF : x ∈ F := hneighbor_F hi1 hxadj
  let m : ℕ := s - 2
  have hm : m + 1 = s - 1 := by omega
  let A1 : Arc Γ m := (T.line.arc (i + 1) m).rev
  let B1 : Arc Γ 1 := Arc.step (T.line.vert (i + 1)) x hxadj
  have hA1_last : A1.vert m = T.line.vert (i + 1) := by
    rw [line_arc_rev_vert]
    simp [A1]
  have hB1_zero : B1.vert 0 = T.line.vert (i + 1) := by simp [B1, Arc.step]
  have hB1_one : B1.vert 1 = x := by simp [B1, Arc.step]
  have hjoin : A1.vert m = B1.vert 0 := by rw [hA1_last, hB1_zero]
  have hnb : 1 ≤ m → 1 ≤ 1 → A1.vert (m - 1) ≠ B1.vert 1 := by
    intro hm1 _
    rw [hB1_one]
    have : A1.vert (m - 1) = T.line.vert (i + 2) := by
      rw [line_arc_rev_vert]
      simp [A1, m]
      congr 1
      omega
    rw [this]
    exact Ne.symm hx2
  let Q1 : Arc Γ (s - 1) := arcCast (by omega : m + 1 = s - 1)
    (Arc.append A1 B1 hjoin hnb)
  have hQ1_0 : Q1.vert 0 = T.line.vert (i + ((s - 1 : ℕ) : ℤ)) := by
    rw [show Q1.vert 0 = (Arc.append A1 B1 hjoin hnb).vert 0 by simp [Q1]]
    rw [Arc.append_vert_le _ _ _ _ (Nat.zero_le m)]
    rw [line_arc_rev_vert]
    simp [A1, m]
    congr 1
    omega
  have hQ1_last : Q1.vert (s - 1) = x := by
    rw [show Q1.vert (s - 1) = (Arc.append A1 B1 hjoin hnb).vert (m + 1) by
      simp [Q1, hm]]
    rw [Arc.append_vert_ge _ _ _ _ (Nat.le_add_right m 1)]
    rw [show m + 1 - m = 1 by omega, hB1_one]
  have hQ1F : ∀ k, k ≤ s - 1 → Q1.vert k ∈ F := by
    intro k hk
    rw [show Q1.vert k = (Arc.append A1 B1 hjoin hnb).vert k by simp [Q1]]
    by_cases hkm : k ≤ m
    · rw [Arc.append_vert_le _ _ _ _ hkm]
      rw [line_arc_rev_vert]
      exact hTF _
    · have hk1 : k = m + 1 := by omega
      subst hk1
      rw [Arc.append_vert_ge _ _ _ _ (Nat.le_add_right m 1)]
      rw [show m + 1 - m = 1 by omega, hB1_one]
      exact hxF
  have hx_F1 : x ∈ F1 := by
    have := hTool Q1 hQ1F (by rw [hQ1_0]; exact hstep i hi)
    rwa [hQ1_last] at this
  let B2 : Arc Γ 1 := Arc.step x (T.line.vert (i + 1)) hxadj.symm
  let A2 : Arc Γ m := (T.line.arc (i - (s - 3 : ℕ)) m).rev
  have hB2_zero : B2.vert 0 = x := by simp [B2, Arc.step]
  have hB2_one : B2.vert 1 = T.line.vert (i + 1) := by simp [B2, Arc.step]
  have hA2_zero : A2.vert 0 = T.line.vert (i + 1) := by
    rw [line_arc_rev_vert]
    simp [A2, m]
    congr 1
    omega
  have hA2_last : A2.vert m = T.line.vert (i - (s - 3 : ℕ)) := by
    rw [line_arc_rev_vert]
    simp [A2, m]
  have hjoin2 : B2.vert 1 = A2.vert 0 := by rw [hB2_one, hA2_zero]
  have hnb2 : 1 ≤ 1 → 1 ≤ m → B2.vert 0 ≠ A2.vert 1 := by
    intro _ hm1
    rw [hB2_zero]
    have : A2.vert 1 = T.line.vert i := by
      rw [line_arc_rev_vert]
      simp [A2, m]
      congr 1
      omega
    rw [this]
    exact hx1
  let Q2 : Arc Γ (s - 1) := arcCast (by omega : 1 + m = s - 1)
    (Arc.append B2 A2 hjoin2 hnb2)
  have hQ2_0 : Q2.vert 0 = x := by
    rw [show Q2.vert 0 = (Arc.append B2 A2 hjoin2 hnb2).vert 0 by simp [Q2]]
    rw [Arc.append_vert_le _ _ _ _ (Nat.zero_le 1), hB2_zero]
  have hQ2_last : Q2.vert (s - 1) = T.line.vert (i - (s - 3 : ℕ)) := by
    rw [show Q2.vert (s - 1) = (Arc.append B2 A2 hjoin2 hnb2).vert (1 + m) by
      simp [Q2, show 1 + m = s - 1 by omega]]
    have h := Arc.append_vert_ge B2 A2 hjoin2 hnb2 (i := 1 + m) (by omega)
    rw [show 1 + m - 1 = m by omega] at h
    rw [h, hA2_last]
  have hQ2F : ∀ k, k ≤ s - 1 → Q2.vert k ∈ F := by
    intro k hk
    rw [show Q2.vert k = (Arc.append B2 A2 hjoin2 hnb2).vert k by simp [Q2]]
    by_cases hk0 : k = 0
    · subst hk0
      rw [Arc.append_vert_le _ _ _ _ (by omega), hB2_zero]
      exact hxF
    · have hk1 : 1 ≤ k := by omega
      rw [Arc.append_vert_ge _ _ _ _ hk1]
      have : A2.vert (k - 1) = T.line.vert (i + 1 - ((k - 1 : ℕ) : ℤ)) := by
        rw [line_arc_rev_vert]
        simp [A2, m]
        congr 1
        omega
      rw [this]
      exact hTF _
  have hend : T.line.vert (i - (s - 3 : ℕ)) ∈ F1 := by
    have := hTool Q2 hQ2F (by rw [hQ2_0]; exact hx_F1)
    rwa [hQ2_last] at this
  have hfin := hstep (i - (s - 3 : ℕ)) hend
  convert hfin using 2
  omega

private theorem distToT_exists (T : KTrack (Γ := Γ) (G := G)) (y : V) :
    ∃ n : ℕ, ∃ z : ℤ, Γ.dist (T.line.vert z) y = n :=
  ⟨Γ.dist (T.line.vert 0) y, 0, rfl⟩

private noncomputable def distToT (T : KTrack (Γ := Γ) (G := G)) (y : V) : ℕ := by
  classical
  exact Nat.find (distToT_exists T y)

private theorem distToT_le (T : KTrack (Γ := Γ) (G := G)) (y : V) (z : ℤ) :
    distToT T y ≤ Γ.dist (T.line.vert z) y := by
  classical
  exact Nat.find_min' (distToT_exists T y) ⟨z, rfl⟩

private theorem exists_distToT (T : KTrack (Γ := Γ) (G := G)) (y : V) :
    ∃ z : ℤ, Γ.dist (T.line.vert z) y = distToT T y := by
  classical
  exact Nat.find_spec (distToT_exists T y)

private theorem distToT_eq_zero_iff (h : Hyp30 Γ G) (T : KTrack (Γ := Γ) (G := G)) (y : V) :
    distToT T y = 0 ↔ y ∈ Set.range T.line.vert := by
  constructor
  · intro hd
    obtain ⟨z, hz⟩ := exists_distToT T y
    have hz0 : Γ.dist (T.line.vert z) y = 0 := by omega
    have hzy : T.line.vert z = y := by
      by_contra hne
      exact absurd hz0 (h.isTree.connected.pos_dist_of_ne hne).ne'
    exact ⟨z, hzy⟩
  · rintro ⟨z, rfl⟩
    apply Nat.eq_zero_of_le_zero
    calc distToT T (T.line.vert z) ≤ Γ.dist (T.line.vert z) (T.line.vert z) :=
          distToT_le T _ z
      _ = 0 := dist_self

private theorem F1_step_down (h : Hyp30 Γ G) (hs6 : 6 ≤ s)
    (T : KTrack (Γ := Γ) (G := G)) {A : Subgroup G} {F F1 : Set V}
    (hTF : ∀ i : ℤ, T.line.vert i ∈ F)
    (hneighbor_F : ∀ {x y : V}, x ∈ F1 → Γ.Adj x y → y ∈ F)
    (hTool : ∀ Q : Arc Γ (s - 1), (∀ k, k ≤ s - 1 → Q.vert k ∈ F) →
      Q.vert 0 ∈ F1 → Q.vert (s - 1) ∈ F1)
    (hstep : ∀ i : ℤ, T.line.vert i ∈ F1 → T.line.vert (i - (s - 1 : ℕ)) ∈ F1)
    {i : ℤ} (hi : T.line.vert i ∈ F1) (hi1 : T.line.vert (i - 1) ∈ F1) :
    T.line.vert (i - 2) ∈ F1 := by
  have hrev := F1_step_up h hs6 (T.rev) (A := A) (F := F) (F1 := F1)
    (fun k : ℤ => by
      simpa [KTrack.rev, Line.rev_vert] using hTF (-k))
    hneighbor_F hTool
    (fun k hk => by
      have hk' : T.line.vert (-k) ∈ F1 := by
        simpa [KTrack.rev, Line.rev_vert] using hk
      have := hstep (-k) hk'
      simpa [KTrack.rev, Line.rev_vert,
        show -k - ((s - 1 : ℕ) : ℤ) = -((s - 1 : ℕ) : ℤ) + -k by omega] using this)
    (i := -i)
    (by simpa [KTrack.rev, Line.rev_vert] using hi)
    (by
      have : T.rev.line.vert (-i + 1) = T.line.vert (i - 1) := by
        simp [KTrack.rev, Line.rev_vert]
        congr 1
        omega
      rw [this]
      exact hi1)
  have : T.rev.line.vert (-i + 2) = T.line.vert (i - 2) := by
    simp [KTrack.rev, Line.rev_vert]
    congr 1
    omega
  rwa [this] at hrev

theorem track_G1_pair_inf_arcStab_eq_bot_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (j : ℤ) :
    G1 (Γ := Γ) (G := G) (T.line.vert (j + 1)) ⊓
      G1 (Γ := Γ) (G := G) (T.line.vert (j + 2)) ⊓
      arcStab (G := G) (T.line.arc j s) = ⊥ := by
  classical
  let A : Subgroup G := G1 (Γ := Γ) (G := G) (T.line.vert (j + 1)) ⊓
    G1 (Γ := Γ) (G := G) (T.line.vert (j + 2)) ⊓ arcStab (G := G) (T.line.arc j s)
  let F : Set V := {x | ∀ a ∈ A, a • x = x}
  let F1 : Set V := {x | A ≤ G1 (Γ := Γ) (G := G) x}
  have hAleLine : A ≤ lineStab T := by
    intro a ha
    exact arcStab_s_le_lineStab h hs hev hs6 T hK j (Subgroup.mem_inf.mp ha).2
  have hTF : ∀ i : ℤ, T.line.vert i ∈ F := by
    intro i a ha
    exact (mem_lineStab T).mp (hAleLine ha) i
  have hF1_12 : T.line.vert (j + 1) ∈ F1 ∧ T.line.vert (j + 2) ∈ F1 := by
    constructor
    · exact (inf_le_left : A ≤ G1 (Γ := Γ) (G := G) (T.line.vert (j + 1)) ⊓
        G1 (Γ := Γ) (G := G) (T.line.vert (j + 2))).trans inf_le_left
    · exact (inf_le_left : A ≤ G1 (Γ := Γ) (G := G) (T.line.vert (j + 1)) ⊓
        G1 (Γ := Γ) (G := G) (T.line.vert (j + 2))).trans inf_le_right
  have hF1_sub_F : F1 ⊆ F := by
    intro x hx a ha
    exact (mem_G1.mp (hx ha)).1
  have hneighbor_F : ∀ {x y : V}, x ∈ F1 → Γ.Adj x y → y ∈ F := by
    intro x y hx hxy a ha
    exact (mem_G1.mp (hx ha)).2 y hxy
  have hTool : ∀ Q : Arc Γ (s - 1), (∀ k, k ≤ s - 1 → Q.vert k ∈ F) →
      Q.vert 0 ∈ F1 → Q.vert (s - 1) ∈ F1 := by
    intro Q hQF hQ0
    have hA0 : A ≤ G1 (Γ := Γ) (G := G) (Q.vert 0) := hQ0
    have hAarc : A ≤ arcStab (G := G) Q := by
      intro a ha
      rw [mem_arcStab]
      intro i hi
      exact hQF i hi a ha
    intro a ha
    exact G1_inf_arcStab_le_G1_end h hs hev hs6 T hK Q (Subgroup.mem_inf.mpr
      ⟨hA0 ha, hAarc ha⟩)
  have hstep1_fwd : ∀ i : ℤ, T.line.vert i ∈ F1 → T.line.vert (i + (s - 1 : ℕ)) ∈ F1 := by
    intro i hi
    have hQ : ∀ k, k ≤ s - 1 → (T.line.arc i (s - 1)).vert k ∈ F := by
      intro k hk
      rw [line_arc_vert]
      exact hTF _
    have h := hTool (T.line.arc i (s - 1)) hQ (by simpa [line_arc_vert] using hi)
    simpa [line_arc_vert] using h
  have hstep1_bwd : ∀ i : ℤ, T.line.vert i ∈ F1 → T.line.vert (i - (s - 1 : ℕ)) ∈ F1 := by
    intro i hi
    let Q : Arc Γ (s - 1) := (T.line.arc (i - (s - 1 : ℕ)) (s - 1)).rev
    have hQ : ∀ k, k ≤ s - 1 → Q.vert k ∈ F := by
      intro k hk
      rw [line_arc_rev_vert]
      exact hTF _
    have hQ0 : Q.vert 0 = T.line.vert i := by
      rw [line_arc_rev_vert]
      simp [Q]
    have h := hTool Q hQ (by rw [hQ0]; exact hi)
    have hQlast : Q.vert (s - 1) = T.line.vert (i - (s - 1 : ℕ)) := by
      rw [line_arc_rev_vert]
      simp [Q]
    rwa [hQlast] at h
  have hstep2_up : ∀ i : ℤ, T.line.vert i ∈ F1 → T.line.vert (i + 1) ∈ F1 →
      T.line.vert (i + 2) ∈ F1 :=
    fun i => F1_step_up h hs6 T (A := A) (F := F) (F1 := F1)
      hTF hneighbor_F hTool hstep1_fwd
  have hstep2_down : ∀ i : ℤ, T.line.vert i ∈ F1 → T.line.vert (i - 1) ∈ F1 →
      T.line.vert (i - 2) ∈ F1 :=
    fun i => F1_step_down h hs6 T (A := A) (F := F) (F1 := F1)
      hTF hneighbor_F hTool hstep1_bwd
  have hT_F1 : ∀ i : ℤ, T.line.vert i ∈ F1 := by
    have hup_nat : ∀ m : ℕ, T.line.vert (j + 1 + (m : ℤ)) ∈ F1 ∧
        T.line.vert (j + 2 + (m : ℤ)) ∈ F1 := by
      intro m
      induction m with
      | zero => simpa using hF1_12
      | succ m ih =>
        have h2 : T.line.vert ((j + 1 + (m : ℤ)) + 1) ∈ F1 := by
          simpa [show j + 2 + (m : ℤ) = j + 1 + (m : ℤ) + 1 by omega] using ih.2
        have hs := hstep2_up (j + 1 + (m : ℤ)) ih.1 h2
        constructor
        · have e : j + 2 + (m : ℤ) = j + 1 + (((m + 1 : ℕ) : ℤ)) := by push_cast; ring
          rw [← e]
          exact ih.2
        · have e : j + 2 + (((m + 1 : ℕ) : ℤ)) = j + 1 + (m : ℤ) + 2 := by push_cast; ring
          rw [e]
          exact hs
    have hdown_nat : ∀ m : ℕ, T.line.vert (j + 1 - (m : ℤ)) ∈ F1 ∧
        T.line.vert (j + 2 - (m : ℤ)) ∈ F1 := by
      intro m
      induction m with
      | zero => simpa using hF1_12
      | succ m ih =>
        have h1 : T.line.vert ((j + 2 - (m : ℤ)) - 1) ∈ F1 := by
          simpa [show (j + 2 - (m : ℤ)) - 1 = j + 1 - (m : ℤ) by omega] using ih.1
        have hs := hstep2_down (j + 2 - (m : ℤ)) ih.2 h1
        constructor
        · have e : j + 1 - (((m + 1 : ℕ) : ℤ)) = (j + 2 - (m : ℤ)) - 2 := by push_cast; ring
          rw [e]
          exact hs
        · have e : j + 2 - (((m + 1 : ℕ) : ℤ)) = j + 1 - (m : ℤ) := by push_cast; ring
          rw [e]
          exact ih.1
    intro i
    by_cases hi : j + 1 ≤ i
    · have h := (hup_nat (i - (j + 1)).toNat).1
      convert h using 2
      have := Int.toNat_of_nonneg (show 0 ≤ i - (j + 1) by omega)
      omega
    · have hi' : i ≤ j + 2 := by omega
      have h := (hdown_nat (j + 2 - i).toNat).2
      convert h using 2
      have := Int.toNat_of_nonneg (show 0 ≤ j + 2 - i by omega)
      omega
  have hAll_F1 : ∀ y : V, y ∈ F1 := by
    have key : ∀ n : ℕ, ∀ y : V, distToT T y = n → y ∈ F1 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro y hy
        by_cases hn0 : n = 0
        · have hyT : y ∈ Set.range T.line.vert := by
            exact (distToT_eq_zero_iff h T y).mp (by omega)
          rcases hyT with ⟨k, rfl⟩
          exact hT_F1 k
        · have hnpos : 0 < n := by omega
          obtain ⟨z, hz⟩ := exists_distToT T y
          have hz_eq : Γ.dist (T.line.vert z) y = n := by rw [hz, hy]
          have hzy : T.line.vert z ≠ y := by
            intro hzy
            rw [hzy, SimpleGraph.dist_self] at hz_eq
            omega
          obtain ⟨P, hP0, hPn⟩ := IsTree.exists_arc h.isTree n (T.line.vert z) y hz_eq
          have hn1 : 1 ≤ n := hnpos
          let x : V := P.vert (n - 1)
          have hxdist : Γ.dist (T.line.vert z) x = n - 1 := by
            rw [← hP0]
            exact Arc.dist_eq h.isTree P (n - 1) (by omega)
          have hxdT : distToT T x ≤ n - 1 :=
            (distToT_le T x z).trans_eq hxdist
          have hxF1 : x ∈ F1 := ih (distToT T x) (by omega) x rfl
          have hxy : Γ.Adj x y := by
            have h := P.adj (n - 1) (by omega)
            simpa [x, hPn, show n - 1 + 1 = n by omega] using h
          have hyF : y ∈ F := hneighbor_F hxF1 hxy
          let L : ℕ := s - 1
          have hLpos : 1 ≤ L := by omega
          by_cases hLn : L ≤ n
          ·
            let Q : Arc Γ L := suffixArc P L hLn
            have hQ0 : Q.vert 0 ∈ F1 := by
              have hdist : Γ.dist (T.line.vert z) (Q.vert 0) = n - L := by
                rw [suffixArc_vert_apply, show 0 + (n - L) = n - L by omega, ← hP0]
                exact Arc.dist_eq h.isTree P (n - L) (by omega)
              have : distToT T (Q.vert 0) ≤ n - L := (distToT_le T _ z).trans_eq hdist
              exact ih (distToT T (Q.vert 0)) (by omega) (Q.vert 0) rfl
            have hQF : ∀ k, k ≤ L → Q.vert k ∈ F := by
              intro k hk
              rw [suffixArc_vert_apply]
              by_cases hkn : k + (n - L) = n
              · rw [hkn, hPn]
                exact hyF
              · apply hF1_sub_F
                have hdist : Γ.dist (T.line.vert z) (P.vert (k + (n - L))) = k + (n - L) := by
                  rw [← hP0]
                  exact Arc.dist_eq h.isTree P (k + (n - L)) (by omega)
                have : distToT T (P.vert (k + (n - L))) ≤ k + (n - L) :=
                  (distToT_le T _ z).trans_eq hdist
                exact ih (distToT T _) (by omega) _ rfl
            have h := hTool Q hQF hQ0
            have hQlast : Q.vert (s - 1) = y := by
              rw [show s - 1 = L by rfl, suffixArc_vert_last, hPn]
            rwa [hQlast] at h
          ·
            have hLn' : n < L := by omega
            let k : ℕ := L - n
            have hkpos : 0 < k := by omega
            let Aarc : Arc Γ k := T.line.arc (z - (k : ℤ)) k
            have hA0 : Aarc.vert 0 = T.line.vert (z - (k : ℤ)) := by rw [line_arc_vert]; simp
            have hAlast : Aarc.vert k = T.line.vert z := by
              rw [line_arc_vert]
              congr 1
              omega
            have hP1_notT : P.vert 1 ∉ Set.range T.line.vert := by
              rintro ⟨u, hu⟩
              have hdist : Γ.dist (T.line.vert u) y = n - 1 := by
                rw [hu, ← hPn]
                exact Arc.dist_vert h.isTree P (by omega) le_rfl
              have : distToT T y ≤ n - 1 := (distToT_le T y u).trans_eq hdist
              omega
            have hnb : 1 ≤ k → 1 ≤ n → Aarc.vert (k - 1) ≠ P.vert 1 := by
              intro hk1 hn1
              have hApen : Aarc.vert (k - 1) = T.line.vert (z - 1) := by
                rw [line_arc_vert]
                congr 1
                omega
              rw [hApen]
              intro h
              exact hP1_notT ⟨z - 1, h⟩
            let Q : Arc Γ L := arcCast (by omega : k + n = L)
              (Arc.append Aarc P (by rw [hAlast, hP0]) hnb)
            have hQ0 : Q.vert 0 ∈ F1 := by
              rw [show Q.vert 0 = (Arc.append Aarc P (by rw [hAlast, hP0]) hnb).vert 0 by
                simp [Q]]
              rw [Arc.append_vert_le _ _ _ _ (Nat.zero_le k), hA0]
              exact hT_F1 _
            have hQF : ∀ i, i ≤ L → Q.vert i ∈ F := by
              intro i hi
              rw [show Q.vert i = (Arc.append Aarc P (by rw [hAlast, hP0]) hnb).vert i by
                simp [Q]]
              by_cases hik : i ≤ k
              · rw [Arc.append_vert_le _ _ _ _ hik, line_arc_vert]
                exact hTF _
              · have hik' : k ≤ i := by omega
                rw [Arc.append_vert_ge _ _ _ _ hik']
                by_cases hin : i - k = n
                · rw [hin, hPn]
                  exact hyF
                · apply hF1_sub_F
                  have hdist : Γ.dist (T.line.vert z) (P.vert (i - k)) = i - k := by
                    rw [← hP0]
                    exact Arc.dist_eq h.isTree P (i - k) (by omega)
                  have : distToT T (P.vert (i - k)) ≤ i - k :=
                    (distToT_le T _ z).trans_eq hdist
                  exact ih (distToT T _) (by omega) _ rfl
            have h := hTool Q hQF hQ0
            have hQlast : Q.vert (s - 1) = y := by
              rw [show s - 1 = L by rfl]
              rw [show Q.vert L = (Arc.append Aarc P (by rw [hAlast, hP0]) hnb).vert L by
                simp [Q]]
              rw [show L = k + n by omega]
              have h := Arc.append_vert_ge Aarc P (by rw [hAlast, hP0]) hnb
                (i := k + n) (by omega)
              rw [show k + n - k = n by omega] at h
              rw [h, hPn]
            rwa [hQlast] at h
    intro y
    exact key (distToT T y) y rfl
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply h.faithful
  intro y
  exact (mem_G1.mp (hAll_F1 y ha)).1

theorem track_G1_pair_inf_arcStab_eq_bot (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (j : ℤ) :
    G1 (Γ := Γ) (G := G) (T.line.vert (j + 1)) ⊓
      G1 (Γ := Γ) (G := G) (T.line.vert (j + 2)) ⊓
      arcStab (G := G) (T.line.arc j s) = ⊥ :=
  track_G1_pair_inf_arcStab_eq_bot_gen h hs hev hs6 T hK j

theorem conjSub_arcStab
    (hadj : ∀ (g : G) (x y : V), Γ.Adj (g • x) (g • y) ↔ Γ.Adj x y)
    {m : ℕ} (g : G) (P Q : Arc Γ m)
    (hg : ∀ i, i ≤ m → g • P.vert i = Q.vert i) :
    conjSub g (arcStab (G := G) P) = arcStab (G := G) Q := by
  rw [arcStab, arcStab, stabRange, stabRange, conjSub_fixSet]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (hg i hi.2).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨P.vert i, ⟨i, hi, rfl⟩, hg i hi.2⟩

theorem G1_pair_inf_arcStab_eq_bot_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (P : Arc Γ s) :
    G1 (Γ := Γ) (G := G) (P.vert 1) ⊓ G1 (Γ := Γ) (G := G) (P.vert 2) ⊓
      arcStab (G := G) P = ⊥ := by
  obtain ⟨j, g, hg⟩ : ∃ (j : ℤ) (g : G), g • P.vert 0 = T.line.vert j := by
    rcases exists_smul_to_line h T (P.vert 0) with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact ⟨0, g, hg⟩
    · exact ⟨1, g, hg⟩
  obtain ⟨hmap, hhmap⟩ := arc_conj_of_le h.adj_smul
    (fun v a b ha hb => h.locTrans ha hb) hs (le_refl s) P (T.line.arc j s) g
    (by simpa [line_arc_vert] using hg)
  have hmap1 : hmap • P.vert 1 = T.line.vert (j + 1) := by
    have := hhmap 1 (by omega)
    simpa [line_arc_vert] using this
  have hmap2 : hmap • P.vert 2 = T.line.vert (j + 2) := by
    have := hhmap 2 (by omega)
    simpa [line_arc_vert] using this
  have hmapArc : conjSub hmap (arcStab (G := G) P) = arcStab (G := G) (T.line.arc j s) :=
    conjSub_arcStab h.adj_smul hmap P (T.line.arc j s) (fun i hi => by
      have := hhmap i hi
      simpa [line_arc_vert] using this)
  have hconj : conjSub hmap
      (G1 (Γ := Γ) (G := G) (P.vert 1) ⊓ G1 (Γ := Γ) (G := G) (P.vert 2) ⊓
        arcStab (G := G) P) =
      G1 (Γ := Γ) (G := G) (T.line.vert (j + 1)) ⊓
        G1 (Γ := Γ) (G := G) (T.line.vert (j + 2)) ⊓
        arcStab (G := G) (T.line.arc j s) := by
    rw [conjSub_inf, conjSub_inf, conjSub_G1 h hmap (P.vert 1),
      conjSub_G1 h hmap (P.vert 2), hmapArc, hmap1, hmap2]
  have hbot := track_G1_pair_inf_arcStab_eq_bot_gen h hs hev hs6 T hK j
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have h1 : hmap * a * hmap⁻¹ = 1 := by
    have hmem : hmap * a * hmap⁻¹ ∈
        conjSub hmap (G1 (Γ := Γ) (G := G) (P.vert 1) ⊓
          G1 (Γ := Γ) (G := G) (P.vert 2) ⊓ arcStab (G := G) P) :=
      mul_mem_conjSub ha
    rw [hconj, hbot] at hmem
    simpa using hmem
  have : a = 1 := by
    have := congrArg (fun x => hmap⁻¹ * x * hmap) h1
    simpa [mul_assoc] using this
  simpa [this]

theorem G1_pair_inf_arcStab_eq_bot (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    (P : Arc Γ s) :
    G1 (Γ := Γ) (G := G) (P.vert 1) ⊓ G1 (Γ := Γ) (G := G) (P.vert 2) ⊓
      arcStab (G := G) P = ⊥ :=
  G1_pair_inf_arcStab_eq_bot_gen h hs hev hs6 T hK P

private theorem exists_fixed_neighbor_of_odd_prime (h : Hyp30 Γ G)
    {g : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hord : orderOf g = p)
    {u v : V} (huv : Γ.Adj u v) (hgu : g • u = u) (hgv : g • v = v) :
    ∃ w : V, Γ.Adj u w ∧ w ≠ v ∧ g • w = w := by
  classical
  let Z : Subgroup G := Subgroup.zpowers g
  have hZleu : Z ≤ MulAction.stabilizer G u :=
    Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hgu)
  have hZlev : Z ≤ MulAction.stabilizer G v :=
    Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hgv)
  have hZu : ∀ z ∈ Z, z • u = u := fun z hz => MulAction.mem_stabilizer_iff.mp (hZleu hz)
  have hZv : ∀ z ∈ Z, z • v = v := fun z hz => MulAction.mem_stabilizer_iff.mp (hZlev hz)
  let Ω : Set V := {w | Γ.Adj u w ∧ w ≠ v}
  let Ωsub : SubMulAction Z V :=
    { carrier := Ω
      smul_mem' := by
        intro z w hw
        refine ⟨?_, ?_⟩
        · have h1 := (h.adj_smul (z : G) u w).2 hw.1
          rwa [hZu z z.2] at h1
        · intro hzv
          apply hw.2
          exact MulAction.injective (z : G) (hzv.trans (hZv z z.2).symm) }
  have hcardΩ : Nat.card Ωsub = 2 ^ nOf Γ u := by
    change Nat.card {w // w ∈ (Ωsub : Set V)} = 2 ^ nOf Γ u
    rw [Nat.card_coe_set_eq]
    have hΩ : (Ωsub : Set V) = Γ.neighborSet u \ {v} := by
      ext w
      change (Γ.Adj u w ∧ w ≠ v) ↔ (Γ.Adj u w ∧ w ≠ v)
      tauto
    rw [hΩ]
    have hcardΔ : (Γ.neighborSet u).ncard = 2 ^ nOf Γ u + 1 := by
      rw [← Nat.card_coe_set_eq, (h.valency u).2]
    have h := Set.ncard_sdiff_singleton_add_one (s := Γ.neighborSet u) huv
      (h.finite_neighborSet u)
    omega
  have hZpg : IsPGroup p Z := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro z
    refine ⟨1, ?_⟩
    rw [pow_one, ← Subgroup.orderOf_coe z]
    simpa [hord] using orderOf_dvd_of_mem_zpowers z.2
  have hpn : ¬ p ∣ 2 ^ nOf Γ u := by
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := hZpg.nonempty_fixed_point_of_prime_not_dvd_card Ωsub
    (by rw [hcardΩ]; exact hpn)
  refine ⟨(x : V), x.2.1, x.2.2, ?_⟩
  have hxg := hx ⟨g, Subgroup.mem_zpowers g⟩
  have hxg' : ((⟨g, Subgroup.mem_zpowers g⟩ : Z) • x : Ωsub).1 = x.1 :=
    congrArg (Subtype.val : Ωsub → V) hxg
  simpa [SubMulAction.val_smul] using hxg'

private theorem exists_fixed_extension (h : Hyp30 Γ G)
    {g : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hord : orderOf g = p) (hs6 : 6 ≤ s)
    {P3 : Arc Γ 3} (hfix3 : ∀ i, i ≤ 3 → g • P3.vert i = P3.vert i) :
    ∃ P : Arc Γ s, (∀ i, i ≤ 3 → P.vert i = P3.vert i) ∧
      (∀ i, i ≤ s → g • P.vert i = P.vert i) := by
  have hmain : ∀ k : ℕ, ∃ P : Arc Γ (3 + k),
      (∀ i, i ≤ 3 → P.vert i = P3.vert i) ∧
      (∀ i, i ≤ 3 + k → g • P.vert i = P.vert i) := by
    intro k
    induction k with
    | zero =>
      refine ⟨P3, ?_, ?_⟩
      · intro i hi; rfl
      · intro i hi; exact hfix3 i (by omega)
    | succ k ih =>
      obtain ⟨P, hP3, hPfix⟩ := ih
      have huv : Γ.Adj (P.vert (3 + k)) (P.vert (3 + k - 1)) := by
        have h := (P.adj (3 + k - 1) (by omega)).symm
        rwa [show 3 + k - 1 + 1 = 3 + k by omega] at h
      have hgu : g • P.vert (3 + k) = P.vert (3 + k) := hPfix (3 + k) le_rfl
      have hgv : g • P.vert (3 + k - 1) = P.vert (3 + k - 1) :=
        hPfix (3 + k - 1) (by omega)
      obtain ⟨w, hwu, hwv, hgw⟩ :=
        exists_fixed_neighbor_of_odd_prime h hp hp2 hord huv hgu hgv
      let Q : Arc Γ ((3 + k) + 1) :=
        snocArc P w hwu (fun _ => hwv)
      refine ⟨arcCast (by omega : (3 + k) + 1 = 3 + (k + 1)) Q, ?_, ?_⟩
      · intro i hi
        rw [arcCast_vert]
        rw [snocArc_vert_le P w hwu (fun _ => hwv) (by omega)]
        exact hP3 i hi
      · intro i hi
        rw [arcCast_vert]
        by_cases hik : i ≤ 3 + k
        · rw [snocArc_vert_le P w hwu (fun _ => hwv) hik]
          exact hPfix i hik
        · have hi' : i = (3 + k) + 1 := by omega
          subst hi'
          have hQw : Q.vert ((3 + k) + 1) = w := snocArc_vert_last P w hwu (fun _ => hwv)
          rw [hQw]
          exact hgw
  obtain ⟨P, hP3, hPfix⟩ := hmain (s - 3)
  refine ⟨arcCast (by omega : 3 + (s - 3) = s) P, ?_, ?_⟩
  · intro i hi; rw [arcCast_vert]; exact hP3 i hi
  · intro i hi; rw [arcCast_vert]; exact hPfix i (by omega)

private theorem eq_one_of_odd_prime_mem_G1_pair (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    {x y : V} (hxy : Γ.Adj x y) {g : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : orderOf g = p) (hgx : g ∈ G1 (Γ := Γ) (G := G) x)
    (hgy : g ∈ G1 (Γ := Γ) (G := G) y) : g = 1 := by
  obtain ⟨w, hwx, hwy⟩ := h.exists_adj_ne x y
  obtain ⟨z, hyz, hzx⟩ := h.exists_adj_ne y x
  let P3 : Arc Γ 3 := Arc.three hwx.symm hxy hyz hwy hzx.symm
  have hfix3 : ∀ i, i ≤ 3 → g • P3.vert i = P3.vert i := by
    intro i hi
    interval_cases i <;> simp [P3, Arc.three, G1_fixes x g hgx, G1_fixes y g hgy,
      G1_fixes_adj hwx g hgx, G1_fixes_adj hyz g hgy]
  obtain ⟨P, hP3, hPfix⟩ := exists_fixed_extension h hp hp2 hord hs6 hfix3
  have hP1 : P.vert 1 = x := by rw [hP3 1 (by omega)]; simp [P3, Arc.three]
  have hP2 : P.vert 2 = y := by rw [hP3 2 (by omega)]; simp [P3, Arc.three]
  have hmem : g ∈ G1 (Γ := Γ) (G := G) (P.vert 1) ⊓
      G1 (Γ := Γ) (G := G) (P.vert 2) ⊓ arcStab (G := G) P := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rwa [hP1]
    · rwa [hP2]
    · rw [mem_arcStab]
      intro i hi
      exact hPfix i hi
  have hB := G1_pair_inf_arcStab_eq_bot_gen h hs hev hs6 T hK P
  rw [hB] at hmem
  simpa using hmem

theorem G1_pair_isPGroup_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    {x y : V} (hxy : Γ.Adj x y) :
    IsPGroup 2 ↥((G1 (Γ := Γ) (G := G) x) ⊓ (G1 (Γ := Γ) (G := G) y)) := by
  let H : Subgroup G := (G1 (Γ := Γ) (G := G) x) ⊓ (G1 (Γ := Γ) (G := G) y)
  haveI : Finite H := by
    haveI := finite_G1 h x
    exact Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  rw [IsPGroup.iff_card]
  by_contra hnot
  push Not at hnot
  have hcard0 : Nat.card H ≠ 0 := by
    haveI : Nonempty H := ⟨⟨1, H.one_mem⟩⟩
    exact ne_of_gt Nat.card_pos
  obtain ⟨a, b, hbodd, hcard⟩ := Nat.exists_eq_two_pow_mul_odd hcard0
  have hb1 : b ≠ 1 := by
    intro hb
    exact hnot a (by rw [hcard, hb, mul_one])
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hb1
  have hp2 : p ≠ 2 := by
    intro hp2
    exact (Nat.not_even_iff_odd.mpr hbodd) (even_iff_two_dvd.mpr (hp2 ▸ hpdvd))
  have hpdvdH : p ∣ Nat.card H := by
    rw [hcard]
    exact dvd_mul_of_dvd_right hpdvd _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' p hpdvdH
  have hggx : (g : G) ∈ G1 (Γ := Γ) (G := G) x :=
    (inf_le_left : H ≤ G1 (Γ := Γ) (G := G) x) g.2
  have hggy : (g : G) ∈ G1 (Γ := Γ) (G := G) y :=
    (inf_le_right : H ≤ G1 (Γ := Γ) (G := G) y) g.2
  have hgord' : orderOf (g : G) = p := by
    rw [Subgroup.orderOf_coe, hgord]
  have hgone := eq_one_of_odd_prime_mem_G1_pair h hs hev hs6 T hK hxy hp hp2 hgord'
    hggx hggy
  have h1 : orderOf (g : G) = 1 := by rw [hgone, orderOf_one]
  exact hp.ne_one (hgord'.symm.trans h1)

theorem G1_pair_isPGroup (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    {x y : V} (hxy : Γ.Adj x y) :
    IsPGroup 2 ↥((G1 (Γ := Γ) (G := G) x) ⊓ (G1 (Γ := Γ) (G := G) y)) :=
  G1_pair_isPGroup_gen h hs hev hs6 T hK hxy

private theorem pCoreOf_isPGroup_ambient (H : Subgroup G) : IsPGroup 2 (pCoreOf 2 H) :=
  (CFSG.pCore_isPGroup (p := 2) (G := H)).map H.subtype

theorem le_pCoreOf_of_two_normal {X A B : Subgroup G} [Finite A]
    (hX2 : IsPGroup 2 X) (hXA : X ≤ A) (hAn : A ≤ Subgroup.normalizer (X : Set G))
    (hAB : A ≤ B) (hBn : B ≤ Subgroup.normalizer (A : Set G)) :
    X ≤ pCoreOf 2 B := by
  have hXA' : X ≤ pCoreOf 2 A :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXA hAn hX2
  have hA2B : pCoreOf 2 A ≤ B := (CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hAB
  have hBnorm : B ≤ Subgroup.normalizer (pCoreOf 2 A : Set G) :=
    hBn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)
  have hO2 : pCoreOf 2 A ≤ pCoreOf 2 B :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hA2B hBnorm
      (pCoreOf_isPGroup_ambient A)
  exact hXA'.trans hO2

theorem G1Set_arc_eq_bot_gen (h : Hyp30 Γ G)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    {m : ℕ} (hm : s - 2 ≤ m) (P : Arc Γ m) :
    G1Set (Γ := Γ) (G := G) (P.vert '' Set.Icc 0 m) = ⊥ := by
  let W : Set V := P.vert '' Set.Icc 0 m
  let X : Subgroup G := G1Set (Γ := Γ) (G := G) W
  have hWmem : ∀ i, i ≤ m → P.vert i ∈ W := fun i hi => ⟨i, ⟨Nat.zero_le _, hi⟩, rfl⟩
  have hXG1 : ∀ i, i ≤ m → X ≤ G1 (Γ := Γ) (G := G) (P.vert i) :=
    fun i hi a ha => (mem_G1Set.mp ha) _ (hWmem i hi)
  have hXfix : ∀ i, i ≤ m → ∀ a ∈ X, a • P.vert i = P.vert i :=
    fun i hi a ha => (mem_G1.mp (hXG1 i hi ha)).1
  have finish : ∀ Q : Arc Γ s, (∀ i, i ≤ s → ∀ a ∈ X, a • Q.vert i = Q.vert i) →
      X ≤ G1 (Γ := Γ) (G := G) (Q.vert 1) →
      X ≤ G1 (Γ := Γ) (G := G) (Q.vert 2) → X = ⊥ := by
    intro Q hfixQ hQ1 hQ2
    have harc : X ≤ arcStab (G := G) Q := by
      intro a ha
      rw [mem_arcStab]
      exact fun i hi => hfixQ i hi a ha
    have hpair : X ≤ G1 (Γ := Γ) (G := G) (Q.vert 1) ⊓
        G1 (Γ := Γ) (G := G) (Q.vert 2) := le_inf hQ1 hQ2
    have hB := G1_pair_inf_arcStab_eq_bot_gen h hs hev hs6 T hK Q
    rw [eq_bot_iff]
    intro a ha
    have hmem : a ∈ G1 (Γ := Γ) (G := G) (Q.vert 1) ⊓
        G1 (Γ := Γ) (G := G) (Q.vert 2) ⊓ arcStab (G := G) Q :=
      Subgroup.mem_inf.mpr ⟨hpair ha, harc ha⟩
    rw [hB] at hmem
    simpa using hmem
  rcases lt_or_ge m s with hms | hsm
  · have hm2 : m = s - 2 ∨ m = s - 1 := by omega
    rcases hm2 with rfl | rfl
    ·
      obtain ⟨z', hz'adj, hz'ne⟩ := h.exists_adj_ne (P.vert (s - 2)) (P.vert (s - 2 - 1))
      obtain ⟨z, hzadj, hzne⟩ := h.exists_adj_ne (P.vert 0) (P.vert 1)
      let P' : Arc Γ (s - 1) := arcCast (by omega : (s - 2) + 1 = s - 1)
        (snocArc P z' hz'adj (fun _ => hz'ne))
      have hP'0 : P'.vert 0 = P.vert 0 := by
        rw [show P'.vert 0 = (snocArc P z' hz'adj (fun _ => hz'ne)).vert 0 by simp [P']]
        rw [snocArc_vert_le P z' hz'adj (fun _ => hz'ne) (by omega)]
      have hP'1 : P'.vert 1 = P.vert 1 := by
        rw [show P'.vert 1 = (snocArc P z' hz'adj (fun _ => hz'ne)).vert 1 by simp [P']]
        rw [snocArc_vert_le P z' hz'adj (fun _ => hz'ne) (by omega)]
      have hP'last : P'.vert (s - 2) = P.vert (s - 2) := by
        rw [show P'.vert (s - 2) = (snocArc P z' hz'adj (fun _ => hz'ne)).vert (s - 2) by simp [P']]
        rw [snocArc_vert_le P z' hz'adj (fun _ => hz'ne) (by omega)]
      let Q : Arc Γ s := arcCast (by omega : (s - 1) + 1 = s)
        (consArc P' z (by rw [hP'0]; exact hzadj.symm)
          (fun _ => by rw [hP'1]; exact hzne))
      have hQ0 : Q.vert 0 = z := by simp [Q, consArc_vert_zero]
      have hQsucc : ∀ i, Q.vert (i + 1) =
          (consArc P' z (by rw [hP'0]; exact hzadj.symm)
            (fun _ => by rw [hP'1]; exact hzne)).vert (i + 1) := fun i => by simp [Q]
      refine finish Q ?_ ?_ ?_
      · intro i hi a ha
        by_cases hi0 : i = 0
        · subst hi0
          rw [hQ0]
          exact (mem_G1.mp (hXG1 0 (by omega) ha)).2 z hzadj
        · have hi1 : 1 ≤ i := by omega
          rw [show i = (i - 1) + 1 by omega, hQsucc]
          rw [consArc_vert_succ]
          by_cases hile : i - 1 ≤ s - 2
          · by_cases hlt : i - 1 < s - 2
            · have hv : P'.vert (i - 1) = P.vert (i - 1) := by
                simp only [P', arcCast_vert]
                rw [snocArc_vert_le P z' hz'adj (fun _ => hz'ne) (by omega)]
              rw [hv]
              exact hXfix (i - 1) hile a ha
            · have he : i - 1 = s - 2 := by omega
              rw [he, hP'last]
              exact hXfix (s - 2) le_rfl a ha
          · have hie : i - 1 = s - 1 := by omega
            rw [hie]
            have hP'last' : P'.vert (s - 1) = z' := by
              simp only [P', arcCast_vert]
              rw [show s - 1 = (s - 2) + 1 by omega, snocArc_vert_last]
            rw [hP'last']
            exact (mem_G1.mp (hXG1 (s - 2) le_rfl ha)).2 z' hz'adj
      · intro a ha
        have hv : Q.vert 1 = P.vert 0 := by
          simp only [Q, arcCast_vert]
          change (consArc P' z (by rw [hP'0]; exact hzadj.symm)
            (fun _ => by rw [hP'1]; exact hzne)).vert (0 + 1) = P.vert 0
          rw [consArc_vert_succ, hP'0]
        simpa [hv] using hXG1 0 (by omega) ha
      · intro a ha
        have hv : Q.vert 2 = P.vert 1 := by
          simp only [Q, arcCast_vert]
          change (consArc P' z (by rw [hP'0]; exact hzadj.symm)
            (fun _ => by rw [hP'1]; exact hzne)).vert (1 + 1) = P.vert 1
          rw [consArc_vert_succ, hP'1]
        simpa [hv] using hXG1 1 (by omega) ha
    ·
      obtain ⟨z, hzadj, hzne⟩ := h.exists_adj_ne (P.vert 0) (P.vert 1)
      let Q : Arc Γ s := arcCast (by omega : (s - 1) + 1 = s)
        (consArc P z hzadj.symm (fun _ => hzne))
      have hQ0 : Q.vert 0 = z := by simp [Q, consArc_vert_zero]
      refine finish Q ?_ ?_ ?_
      · intro i hi a ha
        by_cases hi0 : i = 0
        · subst hi0
          rw [hQ0]
          exact (mem_G1.mp (hXG1 0 (by omega) ha)).2 z hzadj
        · rw [show i = (i - 1) + 1 by omega]
          rw [show Q.vert ((i - 1) + 1) =
              (consArc P z hzadj.symm (fun _ => hzne)).vert ((i - 1) + 1) by simp [Q]]
          rw [consArc_vert_succ]
          exact hXfix (i - 1) (by omega) a ha
      · intro a ha
        have hv : Q.vert 1 = P.vert 0 := by
          simp only [Q, arcCast_vert]
          change (consArc P z hzadj.symm (fun _ => hzne)).vert (0 + 1) = P.vert 0
          rw [consArc_vert_succ]
        simpa [hv] using hXG1 0 (by omega) ha
      · intro a ha
        have hv : Q.vert 2 = P.vert 1 := by
          simp only [Q, arcCast_vert]
          change (consArc P z hzadj.symm (fun _ => hzne)).vert (1 + 1) = P.vert 1
          rw [consArc_vert_succ]
        simpa [hv] using hXG1 1 (by omega) ha
  ·
    let Q : Arc Γ s := initialArc P s hsm
    refine finish Q ?_ ?_ ?_
    · intro i hi a ha
      rw [initialArc_vert]
      exact hXfix i (by omega) a ha
    · intro a ha
      rw [initialArc_vert]
      exact hXG1 1 (by omega) ha
    · intro a ha
      rw [initialArc_vert]
      exact hXG1 2 (by omega) ha

theorem G1Set_arc_eq_bot (h : Hyp30 Γ G) (hn : ∀ v, nOf Γ v = 2)
    (hs : IsSingularity Γ G s) (hev : Even s) (hs6 : 6 ≤ s) (T : KTrack (Γ := Γ) (G := G))
    (hK : ∀ (i : ℤ) (a b : V), Γ.Adj (T.line.vert i) a → Γ.Adj (T.line.vert i) b →
      a ≠ T.line.vert (i - 1) → a ≠ T.line.vert (i + 1) →
      b ≠ T.line.vert (i - 1) → b ≠ T.line.vert (i + 1) → ∃ k ∈ T.K, k • a = b)
    {m : ℕ} (hm : s - 2 ≤ m) (P : Arc Γ m) :
    G1Set (Γ := Γ) (G := G) (P.vert '' Set.Icc 0 m) = ⊥ :=
  G1Set_arc_eq_bot_gen h hs hev hs6 T hK hm P

end CFSG.Quasithin.St84
