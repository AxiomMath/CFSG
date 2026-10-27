module

public import CFSG.Quasithin.Recognition.St84.Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Frattini

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

@[expose] def initialArc {m : ℕ} (P : Arc Γ m) (k : ℕ) (hk : k ≤ m) : Arc Γ k where
  vert := P.vert
  adj i hi := P.adj i (by omega)
  nb i hi := P.nb i (by omega)

@[simp] theorem initialArc_vert {m : ℕ} (P : Arc Γ m) (k : ℕ) (hk : k ≤ m) (i : ℕ) :
    (initialArc P k hk).vert i = P.vert i := rfl

@[expose] def suffixArc {m : ℕ} (P : Arc Γ m) (k : ℕ) (hk : k ≤ m) : Arc Γ k where
  vert i := P.vert (i + (m - k))
  adj i hi := by
    have h := P.adj (i + (m - k)) (by omega)
    rwa [show i + (m - k) + 1 = i + 1 + (m - k) by omega] at h
  nb i hi := by
    have h := P.nb (i + (m - k)) (by omega)
    rwa [show i + (m - k) + 2 = i + 2 + (m - k) by omega] at h

theorem suffixArc_vert_last {m : ℕ} (P : Arc Γ m) {k : ℕ} (hk : k ≤ m) :
    (suffixArc P k hk).vert k = P.vert m := by
  simp [suffixArc, show k + (m - k) = m by omega]

theorem suffixArc_vert_zero {m : ℕ} (P : Arc Γ m) {k : ℕ} (hk : k ≤ m) :
    (suffixArc P k hk).vert 0 = P.vert (m - k) := by
  simp [suffixArc]

theorem stabRange_suffixArc {m : ℕ} (P : Arc Γ m) {k : ℕ} (hk : k ≤ m) :
    stabRange G (suffixArc P k hk).vert 0 k = stabRange G P.vert (m - k) m := by
  ext g
  rw [mem_stabRange, mem_stabRange]
  constructor
  · intro h j hj1 hj2
    have h' := h (j - (m - k)) (Nat.zero_le _) (by omega)
    have e : j - (m - k) + (m - k) = j := by omega
    simpa [suffixArc, e] using h'
  · intro h i hi1 hi2
    have h' := h (i + (m - k)) (by omega) (by omega)
    simpa [suffixArc] using h'

theorem rightTransitive_mono_range {x : ℕ → V} {i j k : ℕ} (hij : i ≤ j)
    (h : RightTransitive Γ G x i k) : RightTransitive Γ G x j k := by
  intro a b ha hau hb hbu
  obtain ⟨g, hg, hga⟩ := h a b ha hau hb hbu
  exact ⟨g, stabRange_anti x hij le_rfl hg, hga⟩

theorem leftTransitive_mono_range {x : ℕ → V} {i k j : ℕ} (h : LeftTransitive Γ G x i k)
    (hjk : j ≤ k) : LeftTransitive Γ G x i j := by
  intro a b ha hau hb hbu
  obtain ⟨g, hg, hga⟩ := h a b ha hau hb hbu
  exact ⟨g, stabRange_anti x le_rfl hjk hg, hga⟩

theorem leftTransitive_initialArc {m : ℕ} (P : Arc Γ m) {k : ℕ} (hk : k ≤ m)
    (h : LeftTransitive Γ G P.vert 0 m) :
    LeftTransitive Γ G (initialArc P k hk).vert 0 k :=
  leftTransitive_mono_range h hk

theorem rightTransitive_suffixArc_iff {m k : ℕ} (P : Arc Γ m) (hk : k ≤ m) (hk1 : 1 ≤ k) :
    RightTransitive Γ G P.vert (m - k) m ↔
      RightTransitive Γ G (suffixArc P k hk).vert 0 k := by
  have hstab := stabRange_suffixArc (G := G) P hk
  have hlast : (suffixArc P k hk).vert k = P.vert m := suffixArc_vert_last P hk
  have hpen : (suffixArc P k hk).vert (k - 1) = P.vert (m - 1) := by
    simp [suffixArc, show (k - 1) + (m - k) = m - 1 by omega]
  simp only [RightTransitive]
  rw [hstab, hlast, hpen]

theorem rightTransitive_suffixArc {m k : ℕ} (P : Arc Γ m) (hk : k ≤ m) (hk1 : 1 ≤ k)
    (h : RightTransitive Γ G P.vert 0 m) :
    RightTransitive Γ G (suffixArc P k hk).vert 0 k := by
  have hmono : RightTransitive Γ G P.vert (m - k) m :=
    rightTransitive_mono_range (Nat.zero_le (m - k)) h
  exact (rightTransitive_suffixArc_iff P hk hk1).1 hmono

theorem rightTransitive_rev_iff {m : ℕ} (P : Arc Γ m) (hm : 1 ≤ m) :
    RightTransitive Γ G P.rev.vert 0 m ↔ LeftTransitive Γ G P.vert 0 m := by
  have hstab : stabRange G P.rev.vert 0 m = stabRange G P.vert 0 m := by
    have hfun : P.rev.vert = fun i => P.vert (m - i) := funext (fun i => Arc.rev_vert P i)
    rw [hfun, stabRange_rev P.vert (Nat.zero_le m) le_rfl]
    simp
  have hlast : P.rev.vert m = P.vert 0 := by
    rw [Arc.rev_vert]; simp
  have hpen : P.rev.vert (m - 1) = P.vert 1 := by
    rw [Arc.rev_vert, show m - (m - 1) = 1 by omega]
  simp only [RightTransitive, LeftTransitive]
  rw [hstab, hlast, hpen]

theorem leftTransitive_rev_iff {m : ℕ} (P : Arc Γ m) (hm : 1 ≤ m) :
    LeftTransitive Γ G P.rev.vert 0 m ↔ RightTransitive Γ G P.vert 0 m := by
  have hstab : stabRange G P.rev.vert 0 m = stabRange G P.vert 0 m := by
    have hfun : P.rev.vert = fun i => P.vert (m - i) := funext (fun i => Arc.rev_vert P i)
    rw [hfun, stabRange_rev P.vert (Nat.zero_le m) le_rfl]
    simp
  have hfirst : P.rev.vert 0 = P.vert m := by
    rw [Arc.rev_vert]; simp
  have hsecond : P.rev.vert 1 = P.vert (m - 1) := Arc.rev_vert P 1
  simp only [LeftTransitive, RightTransitive]
  rw [hstab, hfirst, hsecond]

@[expose] def smulArc (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) (g : G)
    {m : ℕ} (P : Arc Γ m) : Arc Γ m where
  vert i := g • P.vert i
  adj i hi := (hadj g _ _).2 (P.adj i hi)
  nb i hi h := P.nb i hi (MulAction.injective g h)

@[simp] theorem smulArc_vert (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (g : G) {m : ℕ} (P : Arc Γ m) (i : ℕ) : (smulArc hadj g P).vert i = g • P.vert i := rfl

theorem rightTransitive_of_smul
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {x y : ℕ → V} {m : ℕ} {g : G}
    (hg : ∀ i, i ≤ m → y i = g • x i) (h : RightTransitive Γ G x 0 m) :
    RightTransitive Γ G y 0 m := by
  intro a b ha hau hb hbu
  have key : ∀ c, Γ.Adj (y m) c → c ≠ y (m - 1) →
      Γ.Adj (x m) (g⁻¹ • c) ∧ g⁻¹ • c ≠ x (m - 1) := by
    intro c hc hcu
    refine ⟨?_, ?_⟩
    · have h1 : Γ.Adj (g • x m) (g • (g⁻¹ • c)) := by
        simpa [hg m le_rfl] using hc
      exact (hadj g (x m) (g⁻¹ • c)).1 h1
    · intro hh
      exact hcu (by rw [hg (m - 1) (by omega), ← hh, smul_inv_smul])
  obtain ⟨ha1, ha2⟩ := key a ha hau
  obtain ⟨hb1, hb2⟩ := key b hb hbu
  obtain ⟨t, ht, hta⟩ := h _ _ ha1 ha2 hb1 hb2
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · rw [mem_stabRange] at ht ⊢
    intro i hi1 hi2
    rw [mul_smul, mul_smul, hg i hi2, inv_smul_smul, ht i hi1 hi2]
  · rw [mul_smul, mul_smul, hta, smul_inv_smul]

theorem leftTransitive_of_smul
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {x y : ℕ → V} {m : ℕ} (hm : 1 ≤ m) {g : G}
    (hg : ∀ i, i ≤ m → y i = g • x i) (h : LeftTransitive Γ G x 0 m) :
    LeftTransitive Γ G y 0 m := by
  intro a b ha hau hb hbu
  have key : ∀ c, Γ.Adj (y 0) c → c ≠ y 1 →
      Γ.Adj (x 0) (g⁻¹ • c) ∧ g⁻¹ • c ≠ x 1 := by
    intro c hc hcu
    refine ⟨?_, ?_⟩
    · have h1 : Γ.Adj (g • x 0) (g • (g⁻¹ • c)) := by
        simpa [hg 0 (Nat.zero_le m)] using hc
      exact (hadj g (x 0) (g⁻¹ • c)).1 h1
    · intro hh
      exact hcu (by rw [hg 1 (by omega), ← hh, smul_inv_smul])
  obtain ⟨ha1, ha2⟩ := key a ha hau
  obtain ⟨hb1, hb2⟩ := key b hb hbu
  obtain ⟨t, ht, hta⟩ := h _ _ ha1 ha2 hb1 hb2
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · rw [mem_stabRange] at ht ⊢
    intro i hi1 hi2
    rw [mul_smul, mul_smul, hg i hi2, inv_smul_smul, ht i hi1 hi2]
  · rw [mul_smul, mul_smul, hta, smul_inv_smul]

theorem rightTransitive_smul_iff
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {m : ℕ} (g : G) (P : Arc Γ m) :
    RightTransitive Γ G (smulArc hadj g P).vert 0 m ↔
      RightTransitive Γ G P.vert 0 m := by
  constructor
  · intro h
    refine rightTransitive_of_smul hadj (x := (smulArc hadj g P).vert) (y := P.vert)
      (g := g⁻¹) ?_ h
    intro i hi
    simp
  · intro h
    refine rightTransitive_of_smul hadj (x := P.vert) (y := (smulArc hadj g P).vert)
      (g := g) ?_ h
    intro i hi
    simp

theorem leftTransitive_smul_iff
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {m : ℕ} (hm : 1 ≤ m) (g : G) (P : Arc Γ m) :
    LeftTransitive Γ G (smulArc hadj g P).vert 0 m ↔
      LeftTransitive Γ G P.vert 0 m := by
  constructor
  · intro h
    refine leftTransitive_of_smul hadj hm (x := (smulArc hadj g P).vert) (y := P.vert)
      (g := g⁻¹) ?_ h
    intro i hi
    simp
  · intro h
    refine leftTransitive_of_smul hadj hm (x := P.vert) (y := (smulArc hadj g P).vert)
      (g := g) ?_ h
    intro i hi
    simp

theorem arc_conj_of_le
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hs : IsSingularity Γ G s) :
    ∀ {m : ℕ}, m ≤ s → ∀ (P Q : Arc Γ m) (g : G),
      g • P.vert 0 = Q.vert 0 → ∃ h : G, ∀ i ≤ m, h • P.vert i = Q.vert i := by
  intro m
  induction m with
  | zero =>
    intro hm P Q g hg
    exact ⟨g, fun i hi => by rw [show i = 0 by omega]; exact hg⟩
  | succ m ih =>
    intro hm P Q g hg
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    ·
      have h1 : Γ.Adj (Q.vert 0) (g • P.vert 1) := by
        have h := (hadj g (P.vert 0) (P.vert 1)).2 (P.adj 0 (by omega))
        rwa [hg] at h
      have h2 : Γ.Adj (Q.vert 0) (Q.vert 1) := Q.adj 0 (by omega)
      obtain ⟨k, hk, hk1⟩ := hloc (Q.vert 0) (g • P.vert 1) (Q.vert 1) h1 h2
      refine ⟨k * g, fun i hi => ?_⟩
      rw [mul_smul]
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [hg, MulAction.mem_stabilizer_iff.mp hk]
      · exact hk1
    ·
      let P' : Arc Γ m := initialArc P m (by omega)
      let Q' : Arc Γ m := initialArc Q m (by omega)
      have hg' : g • P'.vert 0 = Q'.vert 0 := by simpa [P', Q'] using hg
      obtain ⟨h, hh⟩ := ih (by omega) P' Q' g hg'
      have hh' : ∀ i ≤ m, h • P.vert i = Q.vert i := by
        intro i hi
        simpa [P', Q'] using hh i hi
      have hms : m < s := by omega
      have hreg : Regular Γ G Q' := hs.2.1 m (by omega) hms Q'
      have hPm : Γ.Adj (Q'.vert m) (h • P.vert (m + 1)) := by
        have h := (hadj h (P.vert m) (P.vert (m + 1))).2 (P.adj m (by omega))
        rw [hh' m le_rfl] at h
        simpa [Q'] using h
      have hne : h • P.vert (m + 1) ≠ Q'.vert (m - 1) := by
        intro heq
        have h1 : P.vert (m + 1) = P.vert (m - 1) := by
          apply MulAction.injective h
          change h • P.vert (m + 1) = h • P.vert (m - 1)
          rw [heq, hh' (m - 1) (by omega)]
          simp [Q']
        exact (P.nb (m - 1) (by omega))
          (by simpa [show m - 1 + 2 = m + 1 by omega] using h1.symm)
      have hQnb : Q'.vert (m + 1) ≠ Q'.vert (m - 1) := by
        intro h
        have h1 : Q.vert (m + 1) = Q.vert (m - 1) := by simpa [Q'] using h
        exact (Q.nb (m - 1) (by omega))
          (by simpa [show m - 1 + 2 = m + 1 by omega] using h1.symm)
      obtain ⟨k, hk, hk1⟩ := hreg.2 (h • P.vert (m + 1)) (Q'.vert (m + 1)) hPm hne
        (by simpa [Q'] using Q.adj m (by omega)) hQnb
      refine ⟨k * h, fun i hi => ?_⟩
      rw [mul_smul]
      by_cases hlt : i ≤ m
      · have hki : k • Q'.vert i = Q'.vert i := (mem_stabRange.1 hk) i (Nat.zero_le _) hlt
        have hh_i : h • P.vert i = Q'.vert i := by simpa [Q'] using hh' i hlt
        rw [hh_i, hki]
        simp [Q']
      · rw [show i = m + 1 by omega]
        simpa [Q'] using hk1

theorem odd_succ_iff_even (n : ℕ) : Odd (n + 1) ↔ Even n := by
  rw [Nat.odd_add_one, Nat.not_odd_iff_even]

theorem even_succ_iff_odd (n : ℕ) : Even (n + 1) ↔ Odd n := by
  rw [← Nat.not_odd_iff_even, Nat.odd_add_one]
  tauto

theorem odd_dist_vert_iff (hT : Γ.IsTree) {m : ℕ} (P : Arc Γ m) (o : V) :
    Odd (Γ.dist o (P.vert m)) ↔ Odd (Γ.dist o (P.vert 0) + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hflip : Odd (Γ.dist o (P.vert (m + 1))) ↔ Even (Γ.dist o (P.vert m)) := by
      rcases IsTree.dist_adj_cases hT (r := o) (P.adj m (by omega)) with h | h
      · rw [h, odd_succ_iff_even]
      · rw [h, even_succ_iff_odd]
    have ih' : Odd (Γ.dist o (P.vert m)) ↔ Odd (Γ.dist o (P.vert 0) + m) :=
      ih (initialArc P m (by omega))
    rw [hflip, show Odd (Γ.dist o (P.vert 0) + (m + 1)) =
      Odd ((Γ.dist o (P.vert 0) + m) + 1) by rw [Nat.add_assoc], odd_succ_iff_even]
    rw [← Nat.not_odd_iff_even, ih', Nat.not_odd_iff_even]

theorem even_dist_ends_iff (hT : Γ.IsTree) {m : ℕ} (P : Arc Γ m) (o : V) (hm : Even m) :
    Even (Γ.dist o (P.vert 0)) ↔ Even (Γ.dist o (P.vert m)) := by
  have hodd : Odd (Γ.dist o (P.vert m)) ↔ Odd (Γ.dist o (P.vert 0)) := by
    rw [odd_dist_vert_iff hT P o]
    rw [Nat.odd_add]
    simp [hm]
  rw [← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even, hodd]

theorem odd_dist_ends_iff (hT : Γ.IsTree) {m : ℕ} (P : Arc Γ m) (o : V) (hm : Even m) :
    Odd (Γ.dist o (P.vert 0)) ↔ Odd (Γ.dist o (P.vert m)) := by
  rw [odd_dist_vert_iff hT P o, Nat.odd_add]
  simp [hm]

theorem orbit_eq_even_of_adj (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    {α₀ α₁ : V} (hα : Γ.Adj α₀ α₁) (hneigh : ∀ v, ∃ w, Γ.Adj v w) :
    (∀ v, v ∈ MulAction.orbit G α₀ ↔ Even (Γ.dist α₀ v)) ∧
      (∀ v, v ∈ MulAction.orbit G α₁ ↔ Odd (Γ.dist α₀ v)) := by
  constructor
  · intro v
    constructor
    · rintro ⟨g, rfl⟩
      exact hP g α₀
    · intro hv
      obtain ⟨w, hvw⟩ := hneigh v
      have hw_odd : Odd (Γ.dist α₀ w) := by
        rcases IsTree.dist_adj_cases hT (r := α₀) hvw with h | h
        · rw [h, odd_succ_iff_even]; exact hv
        · exact (even_succ_iff_odd (Γ.dist α₀ w)).mp (h ▸ hv)
      obtain ⟨g, -, hg⟩ := hET α₀ α₁ v w hα hvw
      rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨g, h1⟩
      · exfalso
        exact (Nat.not_even_iff_odd.mpr hw_odd) (h1 ▸ hP g α₀)
  · intro v
    constructor
    · rintro ⟨g, rfl⟩
      have h0 := hP g α₀
      have hadj' : Γ.Adj (g • α₀) (g • α₁) := (hadj g α₀ α₁).2 hα
      rcases IsTree.dist_adj_cases hT (r := α₀) hadj' with h | h
      · rw [h, odd_succ_iff_even]; exact h0
      · exact (even_succ_iff_odd (Γ.dist α₀ (g • α₁))).mp (h ▸ h0)
    · intro hv
      obtain ⟨w, hvw⟩ := hneigh v
      have hw_even : Even (Γ.dist α₀ w) := by
        rcases IsTree.dist_adj_cases hT (r := α₀) hvw with h | h
        · rw [h]; exact (even_succ_iff_odd (Γ.dist α₀ v)).mpr hv
        · exact (odd_succ_iff_even (Γ.dist α₀ w)).mp (h ▸ hv)
      obtain ⟨g, -, hg⟩ := hET α₀ α₁ v w hα hvw
      rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso
        exact (Nat.not_even_iff_odd.mpr hv) (h1 ▸ hP g α₀)
      · exact ⟨g, h2⟩

theorem exists_adj_of_isSingularity (hT : Γ.IsTree) (hs : IsSingularity Γ G s) :
    ∀ v, ∃ w, Γ.Adj v w := by
  have hs1 : 1 ≤ s := hs.1
  obtain ⟨P, -⟩ := hs.2.2
  haveI : Nontrivial V := ⟨P.vert 0, P.vert 1, (P.adj 0 (by omega)).ne⟩
  exact hT.connected.preconnected.exists_adj_of_nontrivial

theorem exists_not_leftTransitive_arc_of_rightSingular
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hs : IsSingularity Γ G s) {γ : Arc Γ s}
    (hγ : ¬ RightTransitive Γ G γ.vert 0 s) :
    ∃ δ : Arc Γ s, δ.vert 0 = γ.vert 1 ∧ ¬ LeftTransitive Γ G δ.vert 0 s := by
  have hs1 : 1 ≤ s := hs.1
  have hγ' : ∃ a b, Γ.Adj (γ.vert s) a ∧ a ≠ γ.vert (s - 1) ∧
      Γ.Adj (γ.vert s) b ∧ b ≠ γ.vert (s - 1) ∧
      ∀ g ∈ stabRange G γ.vert 0 s, g • a ≠ b := by
    unfold RightTransitive at hγ
    push Not at hγ
    exact hγ
  obtain ⟨a, b, ha, hau, hb, hbu, hno⟩ := hγ'
  have hg_exists : ∃ g ∈ stabRange G γ.vert 1 s, g • a = b := by
    rcases Nat.eq_or_lt_of_le hs1 with hs_eq | hs_gt
    · subst hs_eq
      have hloc' := hloc (γ.vert 1) a b ha hb
      simpa [stabRange_self] using hloc'
    · let γ₁ : Arc Γ (s - 1) := suffixArc γ (s - 1) (by omega)
      have hreg : Regular Γ G γ₁ := hs.2.1 (s - 1) (by omega) (by omega) γ₁
      have hlast : γ₁.vert (s - 1) = γ.vert s := suffixArc_vert_last γ (by omega)
      have hpen : γ₁.vert (s - 1 - 1) = γ.vert (s - 1) := by
        simp [γ₁, suffixArc, show (s - 1 - 1) + (s - (s - 1)) = s - 1 by omega]
      obtain ⟨g, hg, hga⟩ := hreg.2 a b (by rwa [hlast]) (by rwa [hpen])
        (by rwa [hlast]) (by rwa [hpen])
      refine ⟨g, ?_, hga⟩
      have hstab := stabRange_suffixArc (G := G) γ (k := s - 1) (by omega)
      rw [show s - (s - 1) = 1 by omega] at hstab
      rwa [← hstab]
  obtain ⟨g, hg_mem, hga⟩ := hg_exists
  let δ : Arc Γ s := Arc.fwd γ b hb (fun _ => hbu)
  have hδ0 : δ.vert 0 = γ.vert 1 := Arc.fwd_vert_zero γ hs1 b hb (fun _ => hbu)
  have hδlt : ∀ i, i < s → δ.vert i = γ.vert (i + 1) := fun i hi =>
    Arc.fwd_vert_lt γ b hb (fun _ => hbu) hi
  have hδlast : δ.vert s = b := Arc.fwd_vert_last γ b hb (fun _ => hbu)
  refine ⟨δ, hδ0, ?_⟩
  intro hL
  have hg1 : g • γ.vert 1 = γ.vert 1 := (mem_stabRange.1 hg_mem) 1 (by omega) (by omega)
  have hx_adj : Γ.Adj (δ.vert 0) (g • γ.vert 0) := by
    have h1 : Γ.Adj (g • γ.vert 0) (g • γ.vert 1) := (hadj g _ _).2 (γ.adj 0 (by omega))
    rw [hg1] at h1
    rw [hδ0]
    exact h1.symm
  have hy_adj : Γ.Adj (δ.vert 0) (γ.vert 0) := by
    rw [hδ0]
    exact (γ.adj 0 (by omega)).symm
  have hx_ne : g • γ.vert 0 ≠ δ.vert 1 := by
    rcases Nat.eq_or_lt_of_le hs1 with hs_eq | hs_gt
    · subst hs_eq
      rw [show δ.vert 1 = b from hδlast]
      intro hgb
      have ha0 : a = γ.vert 0 := by
        calc a = g⁻¹ • (g • a) := by rw [inv_smul_smul]
          _ = g⁻¹ • b := by rw [hga]
          _ = g⁻¹ • (g • γ.vert 0) := by rw [hgb]
          _ = γ.vert 0 := by rw [inv_smul_smul]
      exact hau (by simpa using ha0)
    · have hs2 : 2 ≤ s := by omega
      have hδ1 : δ.vert 1 = γ.vert 2 := hδlt 1 (by omega)
      rw [hδ1]
      intro hg2
      have hg2fix : g • γ.vert 2 = γ.vert 2 := (mem_stabRange.1 hg_mem) 2 (by omega) (by omega)
      have hg2fix' : g⁻¹ • γ.vert 2 = γ.vert 2 := by
        calc g⁻¹ • γ.vert 2 = g⁻¹ • (g • γ.vert 2) := by rw [hg2fix]
          _ = γ.vert 2 := by rw [inv_smul_smul]
      have : γ.vert 0 = γ.vert 2 := by
        calc γ.vert 0 = g⁻¹ • (g • γ.vert 0) := by rw [inv_smul_smul]
          _ = g⁻¹ • γ.vert 2 := by rw [hg2]
          _ = γ.vert 2 := hg2fix'
      exact (γ.nb 0 (by omega)) this
  have hy_ne : γ.vert 0 ≠ δ.vert 1 := by
    rcases Nat.eq_or_lt_of_le hs1 with hs_eq | hs_gt
    · subst hs_eq
      rw [show δ.vert 1 = b from hδlast]
      exact fun h => hbu h.symm
    · have hδ1 : δ.vert 1 = γ.vert 2 := hδlt 1 (by omega)
      rw [hδ1]
      exact γ.nb 0 (by omega)
  obtain ⟨h, hh_mem, hh_smul⟩ := hL (g • γ.vert 0) (γ.vert 0) hx_adj hx_ne hy_adj hy_ne
  have hh_fix : ∀ i, 1 ≤ i → i ≤ s → h • γ.vert i = γ.vert i := by
    intro i hi1 his
    have hj : i - 1 < s := by omega
    have h' := (mem_stabRange.1 hh_mem) (i - 1) (Nat.zero_le _) (by omega)
    rwa [hδlt (i - 1) hj, show i - 1 + 1 = i by omega] at h'
  have hh_b : h • b = b := by
    have h' := (mem_stabRange.1 hh_mem) s (Nat.zero_le _) le_rfl
    rwa [hδlast] at h'
  have hg'_mem : h * g ∈ stabRange G γ.vert 0 s := by
    rw [mem_stabRange]
    intro i hi0 his
    rw [mul_smul]
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [hh_smul]
    · rw [mem_stabRange.1 hg_mem i hi1 his]
      exact hh_fix i hi1 his
  have hg'_a : (h * g) • a = b := by
    rw [mul_smul, hga, hh_b]
  exact hno (h * g) hg'_mem hg'_a

theorem rightSingular_of_start_even (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    (hs : IsSingularity Γ G s) {γ : Arc Γ s}
    (hγ : ¬ RightTransitive Γ G γ.vert 0 s) {P : Arc Γ s}
    (h0 : Even (Γ.dist (γ.vert 0) (P.vert 0))) :
    ¬ RightTransitive Γ G P.vert 0 s := by
  have hs1 : 1 ≤ s := hs.1
  intro hPtrans
  have hneigh := exists_adj_of_isSingularity hT hs
  have hα : Γ.Adj (γ.vert 0) (γ.vert 1) := γ.adj 0 (by omega)
  have horbit : P.vert 0 ∈ MulAction.orbit G (γ.vert 0) :=
    ((orbit_eq_even_of_adj hT hadj hET hP hα hneigh).1 (P.vert 0)).2 h0
  obtain ⟨g, hg⟩ := horbit
  obtain ⟨h, hh⟩ := arc_conj_of_le hadj hloc hs (le_refl s) γ P g hg
  have htrans : RightTransitive Γ G γ.vert 0 s := by
    refine rightTransitive_of_smul hadj (x := P.vert) (y := γ.vert) (g := h⁻¹) ?_ hPtrans
    intro i hi
    rw [← hh i hi, inv_smul_smul]
  exact hγ htrans

theorem leftSingular_of_start_odd (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    (hs : IsSingularity Γ G s) {γ : Arc Γ s}
    (hγ : ¬ RightTransitive Γ G γ.vert 0 s) {P : Arc Γ s}
    (h0 : Odd (Γ.dist (γ.vert 0) (P.vert 0))) :
    ¬ LeftTransitive Γ G P.vert 0 s := by
  have hs1 : 1 ≤ s := hs.1
  obtain ⟨δ, hδ0, hδL⟩ := exists_not_leftTransitive_arc_of_rightSingular hadj hloc hs hγ
  intro hPtrans
  have hneigh := exists_adj_of_isSingularity hT hs
  have hα : Γ.Adj (γ.vert 0) (γ.vert 1) := γ.adj 0 (by omega)
  have horbit : P.vert 0 ∈ MulAction.orbit G (δ.vert 0) := by
    rw [hδ0]
    exact ((orbit_eq_even_of_adj hT hadj hET hP hα hneigh).2 (P.vert 0)).2 h0
  obtain ⟨g, hg⟩ := horbit
  obtain ⟨h, hh⟩ := arc_conj_of_le hadj hloc hs (le_refl s) δ P g hg
  have htrans : LeftTransitive Γ G δ.vert 0 s := by
    refine leftTransitive_of_smul hadj hs.1 (x := P.vert) (y := δ.vert) (g := h⁻¹) ?_ hPtrans
    intro i hi
    rw [← hh i hi, inv_smul_smul]
  exact hδL htrans

theorem leftSingular_of_end_even (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    (hs : IsSingularity Γ G s) {γ : Arc Γ s}
    (hγ : ¬ RightTransitive Γ G γ.vert 0 s) {P : Arc Γ s}
    (hs_end : Even (Γ.dist (γ.vert 0) (P.vert s))) :
    ¬ LeftTransitive Γ G P.vert 0 s := by
  have hs1 : 1 ≤ s := hs.1
  have hrev : ¬ RightTransitive Γ G P.rev.vert 0 s := by
    refine rightSingular_of_start_even hT hadj hloc hET hP hs hγ (P := P.rev) ?_
    simpa using hs_end
  rwa [rightTransitive_rev_iff P hs.1] at hrev

theorem rightSingular_of_end_odd (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    (hs : IsSingularity Γ G s) {γ : Arc Γ s}
    (hγ : ¬ RightTransitive Γ G γ.vert 0 s) {P : Arc Γ s}
    (hs_end : Odd (Γ.dist (γ.vert 0) (P.vert s))) :
    ¬ RightTransitive Γ G P.vert 0 s := by
  have hs1 : 1 ≤ s := hs.1
  have hrev : ¬ LeftTransitive Γ G P.rev.vert 0 s := by
    refine leftSingular_of_start_odd hT hadj hloc hET hP hs hγ (P := P.rev) ?_
    simpa using hs_end
  rwa [leftTransitive_rev_iff P hs.1] at hrev

theorem even_case_nontransitive (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    (hs : IsSingularity Γ G s) (heven : Even s) {γ : Arc Γ s}
    (hγ : ¬ RightTransitive Γ G γ.vert 0 s) :
    ∀ m, s ≤ m → ∀ P : Arc Γ m,
      ¬ LeftTransitive Γ G P.vert 0 m ∧ ¬ RightTransitive Γ G P.vert 0 m := by
  have hlen : ∀ P : Arc Γ s,
      ¬ LeftTransitive Γ G P.vert 0 s ∧ ¬ RightTransitive Γ G P.vert 0 s := by
    intro P
    rcases Nat.even_or_odd (Γ.dist (γ.vert 0) (P.vert 0)) with h0even | h0odd
    · have hse : Even (Γ.dist (γ.vert 0) (P.vert s)) :=
        (even_dist_ends_iff hT P (γ.vert 0) heven).1 h0even
      exact ⟨leftSingular_of_end_even hT hadj hloc hET hP hs hγ hse,
        rightSingular_of_start_even hT hadj hloc hET hP hs hγ h0even⟩
    · have hso : Odd (Γ.dist (γ.vert 0) (P.vert s)) :=
        (odd_dist_ends_iff hT P (γ.vert 0) heven).1 h0odd
      exact ⟨leftSingular_of_start_odd hT hadj hloc hET hP hs hγ h0odd,
        rightSingular_of_end_odd hT hadj hloc hET hP hs hγ hso⟩
  intro m hm P
  constructor
  · intro hL
    exact (hlen (initialArc P s hm)).1 (leftTransitive_initialArc P hm hL)
  · intro hR
    have hR' : RightTransitive Γ G P.vert (m - s) m :=
      rightTransitive_mono_range (Nat.zero_le (m - s)) hR
    have hR'' : RightTransitive Γ G (suffixArc P s hm).vert 0 s :=
      (rightTransitive_suffixArc_iff P hm hs.1).1 hR'
    exact (hlen (suffixArc P s hm)).2 hR''

theorem odd_orbit_of_rightSingular (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    (hs : IsSingularity Γ G s) {γ : Arc Γ s}
    (hγ : ¬ RightTransitive Γ G γ.vert 0 s) :
    (∀ m, s ≤ m → ∀ P : Arc Γ m,
        (Odd (Γ.dist (γ.vert 0) (P.vert m)) → ¬ RightTransitive Γ G P.vert 0 m) ∧
        (Odd (Γ.dist (γ.vert 0) (P.vert 0)) → ¬ LeftTransitive Γ G P.vert 0 m)) ∧
      (∀ m, s ≤ m → ∀ P : Arc Γ m, Regular Γ G P →
        Even (Γ.dist (γ.vert 0) (P.vert 0)) ∧ Even (Γ.dist (γ.vert 0) (P.vert m))) := by
  have hmain : ∀ m, s ≤ m → ∀ P : Arc Γ m,
      (Odd (Γ.dist (γ.vert 0) (P.vert m)) → ¬ RightTransitive Γ G P.vert 0 m) ∧
      (Odd (Γ.dist (γ.vert 0) (P.vert 0)) → ¬ LeftTransitive Γ G P.vert 0 m) := by
    intro m hm P
    constructor
    · intro hoddm hR
      have hR' : RightTransitive Γ G P.vert (m - s) m :=
        rightTransitive_mono_range (Nat.zero_le (m - s)) hR
      have hR'' : RightTransitive Γ G (suffixArc P s hm).vert 0 s :=
        (rightTransitive_suffixArc_iff P hm hs.1).1 hR'
      have hodd' : Odd (Γ.dist (γ.vert 0) ((suffixArc P s hm).vert s)) := by
        rw [suffixArc_vert_last]
        exact hoddm
      exact rightSingular_of_end_odd hT hadj hloc hET hP hs hγ hodd' hR''
    · intro hodd0 hL
      exact leftSingular_of_start_odd hT hadj hloc hET hP hs hγ hodd0
        (leftTransitive_initialArc P hm hL)
  refine ⟨hmain, ?_⟩
  intro m hm P hreg
  exact ⟨Nat.not_odd_iff_even.mp (fun ho => (hmain m hm P).2 ho hreg.1),
    Nat.not_odd_iff_even.mp (fun ho => (hmain m hm P).1 ho hreg.2)⟩

theorem exists_odd_orbit (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    (hs : IsSingularity Γ G s) (hodd : Odd s) :
    ∃ o : V, (∀ m, s ≤ m → ∀ P : Arc Γ m,
        (Odd (Γ.dist o (P.vert m)) → ¬ RightTransitive Γ G P.vert 0 m) ∧
        (Odd (Γ.dist o (P.vert 0)) → ¬ LeftTransitive Γ G P.vert 0 m)) ∧
      (∀ m, s ≤ m → ∀ P : Arc Γ m, Regular Γ G P →
        Even (Γ.dist o (P.vert 0)) ∧ Even (Γ.dist o (P.vert m))) := by
  have hs1 : 1 ≤ s := hs.1
  obtain ⟨P, hPnot⟩ := hs.2.2
  rcases not_and_or.mp hPnot with hL | hR
  · refine ⟨P.rev.vert 0, ?_⟩
    have hγ : ¬ RightTransitive Γ G P.rev.vert 0 s := by
      rwa [rightTransitive_rev_iff P hs1]
    have h := odd_orbit_of_rightSingular hT hadj hloc hET hP hs hγ
    simpa using h
  · exact ⟨P.vert 0, odd_orbit_of_rightSingular hT hadj hloc hET hP hs hR⟩

theorem singularity_dichotomy (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    (hs : IsSingularity Γ G s) :
    (Even s ∧ ∀ m, s ≤ m → ∀ P : Arc Γ m,
        ¬ LeftTransitive Γ G P.vert 0 m ∧ ¬ RightTransitive Γ G P.vert 0 m) ∨
      (Odd s ∧ ∃ o : V, ∀ m, s ≤ m → ∀ P : Arc Γ m,
        (Odd (Γ.dist o (P.vert m)) → ¬ RightTransitive Γ G P.vert 0 m) ∧
        (Odd (Γ.dist o (P.vert 0)) → ¬ LeftTransitive Γ G P.vert 0 m)) := by
  rcases Nat.even_or_odd s with heven | hodd
  · left
    refine ⟨heven, ?_⟩
    have hs1 : 1 ≤ s := hs.1
    obtain ⟨P, hPnot⟩ := hs.2.2
    rcases not_and_or.mp hPnot with hL | hR
    · exact even_case_nontransitive hT hadj hloc hET hP hs heven
        (γ := P.rev) (by rwa [rightTransitive_rev_iff P hs1])
    · exact even_case_nontransitive hT hadj hloc hET hP hs heven hR
  · right
    obtain ⟨o, ho, -⟩ := exists_odd_orbit hT hadj hloc hET hP hs hodd
    exact ⟨hodd, o, ho⟩

theorem regular_even_of_le (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hET : EdgeTransitive Γ (⊤ : Subgroup G)) (hP : PreservesParts Γ G)
    (hs : IsSingularity Γ G s) (hodd : Odd s) {o : V}
    (ho : ∀ m, s ≤ m → ∀ P : Arc Γ m,
      (Odd (Γ.dist o (P.vert m)) → ¬ RightTransitive Γ G P.vert 0 m) ∧
      (Odd (Γ.dist o (P.vert 0)) → ¬ LeftTransitive Γ G P.vert 0 m)) :
    ∀ m, s ≤ m → ∀ P : Arc Γ m, Regular Γ G P →
      Even (Γ.dist o (P.vert 0)) ∧ Even (Γ.dist o (P.vert m)) := by
  intro m hm P hreg
  exact ⟨Nat.not_odd_iff_even.mp (fun h0 => (ho m hm P).2 h0 hreg.1),
    Nat.not_odd_iff_even.mp (fun hm' => (ho m hm P).1 hm' hreg.2)⟩

theorem exists_adj_ne_ne {v a b : V} (hdeg : 3 ≤ Nat.card (Γ.neighborSet v)) :
    ∃ w, Γ.Adj v w ∧ w ≠ a ∧ w ≠ b := by
  by_contra h
  push Not at h
  have hsub : Γ.neighborSet v ⊆ ({a, b} : Set V) := by
    intro w hw
    by_cases hwa : w = a
    · simp [hwa]
    · have hwb : w = b := h w hw hwa
      simp [hwb]
  have h2 : ({a, b} : Set V).ncard ≤ 2 := by
    by_cases hab : a = b
    · subst hab; simp
    · rw [Set.ncard_insert_of_notMem (s := {b}) (by simpa [hab])]
      simp
  have hle : Nat.card (Γ.neighborSet v) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub).trans h2
  omega

theorem exists_isSingularity (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b)
    (hfin : ∀ v : V, Finite (MulAction.stabilizer G v))
    (hdeg : ∀ v : V, 3 ≤ Nat.card (Γ.neighborSet v)) :
    ∃ s, IsSingularity Γ G s := by
  classical
  by_cases hex : ∃ k, 1 ≤ k ∧ ∃ P : Arc Γ k, ¬ Regular Γ G P
  · let s := Nat.find hex
    have hspec := Nat.find_spec hex
    refine ⟨s, hspec.1, ?_, hspec.2⟩
    intro j hj1 hjs P
    by_contra hP
    have hpj : 1 ≤ j ∧ ∃ P : Arc Γ j, ¬ Regular Γ G P := ⟨hj1, P, hP⟩
    have := Nat.find_min' hex hpj
    omega
  · push Not at hex
    exfalso
    obtain ⟨v0⟩ := hT.connected.nonempty
    have hv0 : 0 < Nat.card (Γ.neighborSet v0) := by have := hdeg v0; omega
    haveI : Finite (Γ.neighborSet v0) := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨⟨v1, hv1⟩⟩ := Finite.card_pos_iff.mp hv0
    have exists_adj_ne : ∀ prev v : V, ∃ w, Γ.Adj v w ∧ w ≠ prev := by
      intro prev v
      by_contra h
      push Not at h
      haveI : Finite (Γ.neighborSet v) := Nat.finite_of_card_ne_zero (by have := hdeg v; omega)
      have hsub : Subsingleton (Γ.neighborSet v) :=
        ⟨fun a b => Subtype.ext ((h a.1 a.2).trans (h b.1 b.2).symm)⟩
      have hle : Nat.card (Γ.neighborSet v) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
      have := hdeg v
      omega
    let step (prev v : V) : V := Classical.choose (exists_adj_ne prev v)
    have step_adj : ∀ prev v, Γ.Adj v (step prev v) := fun prev v =>
      (Classical.choose_spec (exists_adj_ne prev v)).1
    have step_ne : ∀ prev v, step prev v ≠ prev := fun prev v =>
      (Classical.choose_spec (exists_adj_ne prev v)).2
    let Q : ℕ → V × V := fun n =>
      Nat.rec (v0, v1) (fun _ p => (p.2, step p.1 p.2)) n
    let x : ℕ → V := fun n => (Q n).1
    have x_zero : x 0 = v0 := rfl
    have x_one : x 1 = v1 := rfl
    have x_succ_succ : ∀ n, x (n + 2) = step (x n) (x (n + 1)) := by
      intro n
      rfl
    have x_adj : ∀ n, Γ.Adj (x n) (x (n + 1)) := by
      intro n
      cases n with
      | zero => simpa [x_zero, x_one] using hv1
      | succ n =>
        rw [x_succ_succ n]
        exact step_adj (x n) (x (n + 1))
    have x_nb : ∀ n, x n ≠ x (n + 2) := by
      intro n
      rw [x_succ_succ n]
      exact (step_ne (x n) (x (n + 1))).symm
    let A : ∀ k, Arc Γ k := fun k =>
      { vert := x
        adj := fun i _ => x_adj i
        nb := fun i _ => x_nb i }
    let H : ℕ → Subgroup G := fun k => stabRange G x 0 k
    have hfinH0 : Finite (H 0) := by
      simpa [H, stabRange_self] using hfin (x 0)
    have hfinH : ∀ k, Finite (H k) := by
      haveI : Finite (H 0) := hfinH0
      intro k
      exact Finite.of_injective
        (fun y : H k => (⟨y.1, stabRange_anti x (Nat.zero_le 0) (Nat.zero_le k) y.2⟩ : H 0))
        (fun y z h => Subtype.ext (congrArg (fun w : H 0 => w.1) h))
    have hstrict : ∀ k, 1 ≤ k → H (k + 1) < H k := by
      intro k hk1
      have hle : H (k + 1) ≤ H k := stabRange_anti x le_rfl (Nat.le_succ k)
      have hrt : RightTransitive Γ G x 0 k := (hex k hk1 (A k)).2
      obtain ⟨b, hb_adj, hb_ne1, hb_ne2⟩ :=
        exists_adj_ne_ne (Γ := Γ) (v := x k) (a := x (k - 1)) (b := x (k + 1)) (hdeg (x k))
      have hxk : x (k + 1) ≠ x (k - 1) := by
        have h := x_nb (k - 1)
        rw [show k - 1 + 2 = k + 1 by omega] at h
        exact h.symm
      obtain ⟨g, hg_mem, hg_smul⟩ := hrt (x (k + 1)) b (x_adj k) hxk hb_adj hb_ne1
      have hg_not : g ∉ H (k + 1) := by
        intro hgin
        have hfix := (mem_stabRange.1 hgin) (k + 1) (Nat.zero_le _) le_rfl
        exact hb_ne2 (hg_smul.symm.trans hfix)
      have hne : H (k + 1) ≠ H k := by
        intro heq
        exact hg_not (heq.symm ▸ hg_mem)
      exact lt_of_le_of_ne hle hne
    have hcard_lt : ∀ k, 1 ≤ k → Nat.card (H (k + 1)) < Nat.card (H k) := by
      intro k hk1
      have hlt := hstrict k hk1
      have hssub : (H (k + 1) : Set G) ⊂ (H k : Set G) := by
        rw [Set.ssubset_iff_subset_ne]
        refine ⟨fun g hg => hlt.1 hg, ?_⟩
        intro hset
        apply hlt.2
        intro g hg
        exact (Set.ext_iff.mp hset.symm g).mp hg
      exact Set.Finite.card_lt_card (hfinH k) hssub
    have hdec : ∀ n, Nat.card (H (1 + n)) + n ≤ Nat.card (H 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hstep : Nat.card (H (1 + (n + 1))) < Nat.card (H (1 + n)) := by
          simpa [show 1 + (n + 1) = (1 + n) + 1 by omega] using hcard_lt (1 + n) (by omega)
        omega
    have hzero : Nat.card (H (1 + Nat.card (H 1))) = 0 := by
      have := hdec (Nat.card (H 1))
      omega
    have hpos : 0 < Nat.card (H (1 + Nat.card (H 1))) := by
      haveI : Finite (H (1 + Nat.card (H 1))) := hfinH _
      haveI : Nonempty (H (1 + Nat.card (H 1))) := ⟨⟨1, (H _).one_mem⟩⟩
      exact Finite.card_pos
    omega

end CFSG.Quasithin.St84
