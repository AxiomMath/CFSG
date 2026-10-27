module

public import CFSG.Quasithin.Recognition.St84.Sec5Step89
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LineOfPair
import CFSG.Quasithin.Background.F6Amalgams

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

private theorem Z_zero_le_centralizer_Gi_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.Z 0 ≤ Subgroup.centralizer (Y.Gi 0 : Set G) := by
  obtain ⟨-, -, -, -, -, -, hcard, -⟩ := Y.s52_step8 H hZ
  exact Subgroup.le_centralizer_iff.mp fun g hg =>
    normalizer_le_centralizer_of_card_two hcard
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Y.Z_normal 0 g hg))

private theorem fixes_iff_dist_le_three_of_mem (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {z₀ : G} (hz₀Z : z₀ ∈ Y.Z 0) (hz₀ne : z₀ ≠ 1) (v : V) :
    z₀ • v = v ↔ Γ.dist (Y.vert 0) v ≤ 3 := by
  obtain ⟨-, -, -, -, -, -, hcard, -⟩ := Y.s52_step8 H hZ
  have h := Y.vertZ_le_stabilizer_iff H hZ 0 1 v
  rw [one_smul, ← Y.Z_eq_vertZ, if_pos (show Even (0 : ℤ) from ⟨0, by norm_num⟩)] at h
  rw [← h]
  refine ⟨fun hv z hz => ?_, fun hle => hle hz₀Z⟩
  rcases eq_or_ne z 1 with rfl | hz1
  · exact one_mem _
  · rw [CFSG.Quasithin.F6.eq_of_card_eq_two hcard hz hz₀Z hz1 hz₀ne]
    exact MulAction.mem_stabilizer_iff.mpr hv

private theorem smul_vert_eq_iff_natAbs_le_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {z₀ : G} (hz₀Z : z₀ ∈ Y.Z 0) (hz₀ne : z₀ ≠ 1) (j : ℤ) :
    z₀ • Y.vert j = Y.vert j ↔ j.natAbs ≤ 3 := by
  rw [fixes_iff_dist_le_three_of_mem Y H hZ hz₀Z hz₀ne, Y.dist_vert_natAbs]

private def vertsOnFixedLine (Y : Setup Γ G) (P : Subgroup G) : Set V :=
  {v | ∃ L : Line Γ, (∀ k ∈ Y.K, ∀ i, k • L.vert i = L.vert i) ∧
    (∀ p ∈ P, ∀ i, p • L.vert i = L.vert i) ∧ ∃ i : ℤ, L.vert i = v}

private theorem mem_vertsOnFixedLine (Y : Setup Γ G) {P : Subgroup G} {v : V} {M : Line Γ}
    (h1 : ∀ k ∈ Y.K, ∀ i, k • M.vert i = M.vert i)
    (h2 : ∀ p ∈ P, ∀ i, p • M.vert i = M.vert i) (h3 : ∃ i, M.vert i = v) :
    v ∈ Y.vertsOnFixedLine P := by
  rw [vertsOnFixedLine]
  exact ⟨M, h1, h2, h3⟩

private theorem conj_fixes_iff_dist_le_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {z₀ : G} (hz₀Z : z₀ ∈ Y.Z 0) (hz₀ne : z₀ ≠ 1) {g : G} {w : V}
    (hg : g • Y.vert 0 = w) (y : V) :
    (g * z₀ * g⁻¹) • y = y ↔ Γ.dist w y ≤ 3 := by
  have h1 : (g * z₀ * g⁻¹) • y = y ↔ z₀ • (g⁻¹ • y) = g⁻¹ • y := by
    constructor
    · intro h
      have h' := congrArg (fun t => g⁻¹ • t) h
      simpa [mul_smul] using h'
    · intro h
      have h' := congrArg (fun t => g • t) h
      simpa [mul_smul] using h'
  rw [h1, fixes_iff_dist_le_three_of_mem Y H hZ hz₀Z hz₀ne (g⁻¹ • y)]
  have hd : Γ.dist (Y.vert 0) (g⁻¹ • y) = Γ.dist w y := by
    have h := IsTree.dist_smul Y.hyp.isTree Y.hyp.adj_smul g (Y.vert 0) (g⁻¹ • y)
    rw [hg, smul_inv_smul] at h
    exact h.symm
  rw [hd]

private theorem conj_commute_of_smul_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {z₀ : G} (hz₀Z : z₀ ∈ Y.Z 0) {g : G} {w : V}
    (hg : g • Y.vert 0 = w) {y : G} (hy : y • w = w) :
    y * (g * z₀ * g⁻¹) = (g * z₀ * g⁻¹) * y := by
  have hcent : Y.Z 0 ≤ Subgroup.centralizer (Y.Gi 0 : Set G) :=
    Y.Z_zero_le_centralizer_Gi_zero H hZ
  have hy0 : (g⁻¹ * y * g) • Y.vert 0 = Y.vert 0 := by
    rw [mul_smul, mul_smul, hg, hy, ← hg, inv_smul_smul]
  have hcomm0 : (g⁻¹ * y * g) * z₀ = z₀ * (g⁻¹ * y * g) :=
    Subgroup.mem_centralizer_iff.mp (hcent hz₀Z) _ hy0
  calc y * (g * z₀ * g⁻¹) = g * ((g⁻¹ * y * g) * z₀) * g⁻¹ := by group
    _ = g * (z₀ * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm0]
    _ = (g * z₀ * g⁻¹) * y := by group

private theorem fixes_line_smul_of_commute (Y : Setup Γ G) {M : Subgroup G} {c : G}
    {lam : Line Γ} (hc : ∀ m ∈ M, m * c = c * m)
    (hM : ∀ m ∈ M, ∀ i, m • lam.vert i = lam.vert i) :
    ∀ m ∈ M, ∀ i,
      m • (Line.smul Y.hyp.adj_smul c lam).vert i = (Line.smul Y.hyp.adj_smul c lam).vert i := by
  intro m hm idx
  show m • (c • lam.vert idx) = c • lam.vert idx
  calc m • (c • lam.vert idx) = (m * c) • lam.vert idx := (mul_smul m c _).symm
    _ = (c * m) • lam.vert idx := by rw [hc m hm]
    _ = c • (m • lam.vert idx) := mul_smul c m _
    _ = c • lam.vert idx := by rw [hM m hm idx]

private theorem smul_eq_third_of_fixes (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {j : ℤ}
    (hj : Odd j) {a b x : V} {c : G} (ha : Γ.Adj (Y.vert j) a) (hb : Γ.Adj (Y.vert j) b)
    (hx : Γ.Adj (Y.vert j) x) (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x)
    (hcv : c • Y.vert j = Y.vert j) (hca : c • a = a) (hcb : c • b ≠ b) : c • b = x := by
  have hnbhd : Γ.neighborSet (Y.vert j) = ({a, b, x} : Set V) := by
    have hnj : nOf Γ (Y.vert j) = 1 := by
      obtain ⟨m, hm⟩ := hj
      have he : j = 1 + 2 * (m : ℤ) := by omega
      rw [he]
      exact Y.n_add m 1 |>.trans H.n_one
    have hval : Nat.card (Γ.neighborSet (Y.vert j)) = 3 := by
      have h := (Y.hyp.valency (Y.vert j)).2
      rw [hnj] at h
      simpa using h
    have h3B : (Γ.neighborSet (Y.vert j)).ncard = 3 := by
      rw [Nat.card_coe_set_eq] at hval
      exact hval
    have h3A : ({a, b, x} : Set V).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨a, b, x, hab, hax, hbx, rfl⟩
    have hsub : ({a, b, x} : Set V) ⊆ Γ.neighborSet (Y.vert j) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hx
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [h3B, h3A])
      (Y.hyp.finite_neighborSet (Y.vert j))).symm
  have hadj : Γ.Adj (Y.vert j) (c • b) := by
    rw [← hcv]
    exact (Y.hyp.adj_smul c (Y.vert j) b).mpr hb
  have hmem : c • b ∈ ({a, b, x} : Set V) := by
    rw [← hnbhd]
    exact hadj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exfalso
    have h1 : c • b = c • a := h.trans hca.symm
    exact hab (MulAction.injective c h1.symm)
  · exact absurd h hcb
  · exact h

private theorem vert_succ_pred_mem_vertsOnFixedLine (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {P : Subgroup G} {j : ℤ} (hj : Even j) (hX : Y.vert j ∈ Y.vertsOnFixedLine P) :
    Y.vert (j + 1) ∈ Y.vertsOnFixedLine P ∧ Y.vert (j - 1) ∈ Y.vertsOnFixedLine P := by
  obtain ⟨lam, hKl, hPl, i, hi⟩ := hX
  have hva : Γ.Adj (lam.vert (i - 1)) (Y.vert j) := by
    have h := lam.adj (i - 1)
    rw [show i - 1 + 1 = i by omega, hi] at h
    exact h
  have hvb : Γ.Adj (Y.vert j) (lam.vert (i + 1)) := by
    have h := lam.adj i
    rw [hi] at h
    exact h
  have hodd1 : Odd (Γ.dist (Y.vert 0) (Y.vert (j + 1))) := by
    rw [Y.dist_vert_natAbs (j + 1)]
    have hodd : Odd (j + 1) := by
      obtain ⟨m, hm⟩ := hj
      exact ⟨m, by rw [hm]; ring⟩
    exact hodd.natAbs
  have hcard2 : Nat.card {x : V // Γ.Adj (Y.vert j) x ∧ ∀ k ∈ Y.K, k • x = x} = 2 :=
    Y.card_fixed_nbrs_of_even H hodd1 (fun k hk => Y.K_fix k hk (j + 1))
      (Y.adj j).symm (fun k hk => Y.K_fix k hk j)
  let T := {x : V // Γ.Adj (Y.vert j) x ∧ ∀ k ∈ Y.K, k • x = x}
  let x₁ : T := ⟨lam.vert (i - 1), hva.symm, fun k hk => hKl k hk (i - 1)⟩
  let x₂ : T := ⟨lam.vert (i + 1), hvb, fun k hk => hKl k hk (i + 1)⟩
  have hx12 : x₁ ≠ x₂ := by
    intro h
    have h' := congrArg Subtype.val h
    exact absurd (Line.vert_injective Y.hyp.isTree lam h') (by omega)
  have htwo : ∀ y₁ y₂ : T, y₁ ≠ x₁ → y₂ ≠ x₁ → y₁ = y₂ := by
    intro y₁ y₂ h₁ h₂
    obtain ⟨u, -, huniq⟩ := (Nat.card_eq_two_iff' x₁).mp hcard2
    exact (huniq y₁ h₁).trans (huniq y₂ h₂).symm
  have hmem1 : Y.vert (j + 1) ∈ Y.vertsOnFixedLine P := by
    by_cases hy : Y.vert (j + 1) = lam.vert (i - 1)
    · exact mem_vertsOnFixedLine Y hKl hPl ⟨i - 1, hy.symm⟩
    · have hy' : (⟨Y.vert (j + 1), Y.adj j,
          fun k hk => Y.K_fix k hk (j + 1)⟩ : T) ≠ x₁ := by
        intro h
        exact hy (congrArg Subtype.val h)
      have heq : (⟨Y.vert (j + 1), Y.adj j,
          fun k hk => Y.K_fix k hk (j + 1)⟩ : T) = x₂ := htwo _ _ hy' hx12.symm
      exact mem_vertsOnFixedLine Y hKl hPl ⟨i + 1, (congrArg Subtype.val heq).symm⟩
  have hmem2 : Y.vert (j - 1) ∈ Y.vertsOnFixedLine P := by
    have hjm : Γ.Adj (Y.vert j) (Y.vert (j - 1)) := by
      have h := Y.adj (j - 1)
      rw [show j - 1 + 1 = j by omega] at h
      exact h.symm
    by_cases hy : Y.vert (j - 1) = lam.vert (i - 1)
    · exact mem_vertsOnFixedLine Y hKl hPl ⟨i - 1, hy.symm⟩
    · have hy' : (⟨Y.vert (j - 1), hjm,
          fun k hk => Y.K_fix k hk (j - 1)⟩ : T) ≠ x₁ := by
        intro h
        exact hy (congrArg Subtype.val h)
      have heq : (⟨Y.vert (j - 1), hjm,
          fun k hk => Y.K_fix k hk (j - 1)⟩ : T) = x₂ := htwo _ _ hy' hx12.symm
      exact mem_vertsOnFixedLine Y hKl hPl ⟨i + 1, (congrArg Subtype.val heq).symm⟩
  exact ⟨hmem1, hmem2⟩

private theorem mem_vertsOnFixedLine_of_adj_of_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {P : Subgroup G} {j : ℤ} (hj : Odd j)
    (hX : Y.vert j ∈ Y.vertsOnFixedLine P) {x : V} (hx : Γ.Adj (Y.vert j) x) :
    x ∈ Y.vertsOnFixedLine P := by
  obtain ⟨z₀, hz₀Z, hz₀ne⟩ :=
    (Y.Z 0).bot_or_exists_ne_one.resolve_left (Y.Z_ne_bot_of 0 (Y.Q_ne_bot H.char 0))
  obtain ⟨lam, hKl, hPl, i, hi⟩ := hX
  have hva : Γ.Adj (lam.vert (i - 1)) (Y.vert j) := by
    have h := lam.adj (i - 1)
    rw [show i - 1 + 1 = i by omega, hi] at h
    exact h
  have hvb : Γ.Adj (Y.vert j) (lam.vert (i + 1)) := by
    have h := lam.adj i
    rw [hi] at h
    exact h
  by_cases hxa : x = lam.vert (i - 1)
  · exact mem_vertsOnFixedLine Y hKl hPl ⟨i - 1, by rw [hxa]⟩
  by_cases hxb : x = lam.vert (i + 1)
  · exact mem_vertsOnFixedLine Y hKl hPl ⟨i + 1, by rw [hxb]⟩
  have hax : lam.vert (i - 1) ≠ x := fun h => hxa h.symm
  have hbx : lam.vert (i + 1) ≠ x := fun h => hxb h.symm
  have hwa2 : Γ.Adj (lam.vert (i - 3)) (lam.vert (i - 2)) := by
    have h := lam.adj (i - 3)
    rwa [show i - 3 + 1 = i - 2 by omega] at h
  have ha2a : Γ.Adj (lam.vert (i - 2)) (lam.vert (i - 1)) := by
    have h := lam.adj (i - 2)
    rwa [show i - 2 + 1 = i - 1 by omega] at h
  have hjodd : Odd (Γ.dist (Y.vert 0) (Y.vert j)) := by
    rw [Y.dist_vert_natAbs j]
    exact hj.natAbs
  have ha_even : Even (Γ.dist (Y.vert 0) (lam.vert (i - 1))) :=
    even_dist_of_adj_odd Y hjodd hva
  have ha2_odd : Odd (Γ.dist (Y.vert 0) (lam.vert (i - 2))) :=
    odd_dist_of_adj_even Y ha_even ha2a.symm
  obtain ⟨g, -, hg1, hg0⟩ := Y.exists_normalizer_K_edge H ha2_odd
    (fun k hk => hKl k hk (i - 2)) hwa2.symm (fun k hk => hKl k hk (i - 3))
  have hzwfix : ∀ y : V, (g * z₀ * g⁻¹) • y = y ↔
      Γ.dist (lam.vert (i - 3)) y ≤ 3 :=
    fun y => Y.conj_fixes_iff_dist_le_three H hZ hz₀Z hz₀ne hg0 y
  have hzwcomm : ∀ y : G, y • lam.vert (i - 3) = lam.vert (i - 3) →
      y * (g * z₀ * g⁻¹) = (g * z₀ * g⁻¹) * y :=
    fun y hy => Y.conj_commute_of_smul_eq H hZ hz₀Z hg0 hy
  have hGoodNew : (∀ k ∈ Y.K, ∀ i,
      k • (Line.smul Y.hyp.adj_smul (g * z₀ * g⁻¹) lam).vert i =
        (Line.smul Y.hyp.adj_smul (g * z₀ * g⁻¹) lam).vert i) ∧
      (∀ p ∈ P, ∀ i,
        p • (Line.smul Y.hyp.adj_smul (g * z₀ * g⁻¹) lam).vert i =
          (Line.smul Y.hyp.adj_smul (g * z₀ * g⁻¹) lam).vert i) :=
    ⟨fixes_line_smul_of_commute Y
        (fun k hk => hzwcomm k (hKl k hk (i - 3))) hKl,
      fixes_line_smul_of_commute Y
        (fun p hp => hzwcomm p (hPl p hp (i - 3))) hPl⟩
  have hd_wv : Γ.dist (lam.vert (i - 3)) (Y.vert j) = 3 := by
    rw [← hi]
    have h := Line.dist_eq Y.hyp.isTree lam (i := i - 3) (j := i) (by omega)
    rw [show i - (i - 3) = (3 : ℤ) by omega] at h
    simpa using h
  have hd_wa : Γ.dist (lam.vert (i - 3)) (lam.vert (i - 1)) = 2 := by
    have h := Line.dist_eq Y.hyp.isTree lam (i := i - 3) (j := i - 1) (by omega)
    rw [show i - 1 - (i - 3) = (2 : ℤ) by omega] at h
    simpa using h
  have hd_wb : Γ.dist (lam.vert (i - 3)) (lam.vert (i + 1)) = 4 := by
    have h := Line.dist_eq Y.hyp.isTree lam (i := i - 3) (j := i + 1) (by omega)
    rw [show i + 1 - (i - 3) = (4 : ℤ) by omega] at h
    simpa using h
  have hd_wx : Γ.dist (lam.vert (i - 3)) x = 4 := by
    rcases IsTree.dist_adj_cases Y.hyp.isTree (r := lam.vert (i - 3)) hx with h | h
    · rw [h, hd_wv]
    · have hx2 : Γ.dist (lam.vert (i - 3)) x = 2 := by
        have h' : Γ.dist (lam.vert (i - 3)) x + 1 = 2 + 1 := by rw [← h, hd_wv]
        exact Nat.succ.inj h'
      have ha2 : Γ.dist (lam.vert (i - 3)) (lam.vert (i - 1)) + 1 =
          Γ.dist (lam.vert (i - 3)) (Y.vert j) := by rw [hd_wa, hd_wv]
      have hx2' : Γ.dist (lam.vert (i - 3)) x + 1 =
          Γ.dist (lam.vert (i - 3)) (Y.vert j) := by rw [hx2, hd_wv]
      exact absurd (IsTree.eq_of_dist_succ Y.hyp.isTree hx.symm hva hx2' ha2) hax.symm
  have hfix_v : (g * z₀ * g⁻¹) • Y.vert j = Y.vert j :=
    (hzwfix _).mpr (by rw [hd_wv])
  have hfix_a : (g * z₀ * g⁻¹) • lam.vert (i - 1) = lam.vert (i - 1) :=
    (hzwfix _).mpr (by rw [hd_wa]; norm_num)
  have hmove_b : (g * z₀ * g⁻¹) • lam.vert (i + 1) ≠ lam.vert (i + 1) := by
    intro h
    have hle := (hzwfix _).mp h
    rw [hd_wb] at hle
    norm_num at hle
  have hab : lam.vert (i - 1) ≠ lam.vert (i + 1) := by
    intro h
    have h' := Line.vert_injective Y.hyp.isTree lam h
    omega
  have hb' : (g * z₀ * g⁻¹) • lam.vert (i + 1) = x :=
    smul_eq_third_of_fixes Y H hj hva.symm hvb hx hab hax hbx hfix_v hfix_a hmove_b
  exact mem_vertsOnFixedLine Y hGoodNew.1 hGoodNew.2
    ⟨i + 1, by show (g * z₀ * g⁻¹) • lam.vert (i + 1) = x; rw [hb']⟩

private theorem le_K_of_fixes_line (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {P : Subgroup G} (L : Line Γ)
    (hKL : ∀ k ∈ Y.K, ∀ i, k • L.vert i = L.vert i)
    (hPL : ∀ p ∈ P, ∀ i, p • L.vert i = L.vert i) {i₀ j₀ : ℤ}
    (hmeet : L.vert i₀ = Y.vert j₀) : P ≤ Y.K := by
  classical
  have hstep : ∀ j : ℤ, Y.vert j ∈ Y.vertsOnFixedLine P →
      Y.vert (j + 1) ∈ Y.vertsOnFixedLine P ∧ Y.vert (j - 1) ∈ Y.vertsOnFixedLine P := by
    intro j hXj
    by_cases hj : Even j
    · exact Y.vert_succ_pred_mem_vertsOnFixedLine H hj hXj
    · have hodd : Odd j := Int.not_even_iff_odd.mp hj
      have hfixm : Γ.Adj (Y.vert j) (Y.vert (j - 1)) := by
        have h := Y.adj (j - 1)
        rw [show j - 1 + 1 = j by omega] at h
        exact h.symm
      exact ⟨Y.mem_vertsOnFixedLine_of_adj_of_odd H hZ hodd hXj (Y.adj j),
        Y.mem_vertsOnFixedLine_of_adj_of_odd H hZ hodd hXj hfixm⟩
  have hbase : Y.vert j₀ ∈ Y.vertsOnFixedLine P :=
    Y.mem_vertsOnFixedLine hKL hPL ⟨i₀, hmeet⟩
  have hind : ∀ n : ℕ, Y.vert (j₀ + (n : ℤ)) ∈ Y.vertsOnFixedLine P ∧
      Y.vert (j₀ - (n : ℤ)) ∈ Y.vertsOnFixedLine P := by
    intro n
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      constructor
      · have h := (hstep (j₀ + (n : ℤ)) ih.1).1
        have he : j₀ + (n : ℤ) + 1 = j₀ + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
        rwa [he] at h
      · have h := (hstep (j₀ - (n : ℤ)) ih.2).2
        have he : j₀ - (n : ℤ) - 1 = j₀ - ((n + 1 : ℕ) : ℤ) := by push_cast; ring
        rwa [he] at h
  have hXall : ∀ j : ℤ, Y.vert j ∈ Y.vertsOnFixedLine P := by
    intro j
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (j - j₀)
    · have he : j = j₀ + (n : ℤ) := by omega
      rw [he]
      exact (hind n).1
    · have he : j = j₀ - (n : ℤ) := by omega
      rw [he]
      exact (hind n).2
  intro p hp
  rw [← Y.GT_eq_K_of_sec5Hyp H, Setup.GT, Fan86.mem_fixSet]
  rintro v ⟨j, rfl⟩
  obtain ⟨lam, hKl, hPl, i, hi⟩ := hXall j
  rw [← hi]
  exact hPl p hp i

private theorem arcStab_eight_eq_K_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.arcStab 0 8 = Y.K := by
  classical
  obtain ⟨z₀, hz₀Z, hz₀ne⟩ :=
    (Y.Z 0).bot_or_exists_ne_one.resolve_left (Y.Z_ne_bot_of 0 (Y.Q_ne_bot H.char 0))
  have hcent : Y.Z 0 ≤ Subgroup.centralizer (Y.Gi 0 : Set G) :=
    Y.Z_zero_le_centralizer_Gi_zero H hZ
  have hfix3 : z₀ • Y.vert 3 = Y.vert 3 :=
    (Y.smul_vert_eq_iff_natAbs_le_three H hZ hz₀Z hz₀ne 3).mpr (by norm_num)
  have hmove4 : z₀ • Y.vert 4 ≠ Y.vert 4 := by
    intro h
    have h4 := (Y.smul_vert_eq_iff_natAbs_le_three H hZ hz₀Z hz₀ne 4).mp h
    norm_num at h4
  let b : G := Y.τ ^ (4 : ℤ) * z₀ * (Y.τ ^ (4 : ℤ))⁻¹
  have hbZ : b ∈ Y.Z 8 := by
    have hZ8 : Y.Z 8 = conjSub (Y.τ ^ (4 : ℤ)) (Y.Z 0) := by
      exact Y.Z_smul Y (g := Y.τ ^ (4 : ℤ)) (i := 0) (j := 8) (by
        rw [Y.zpow_smul_vert]; norm_num)
    rw [hZ8]
    exact mul_mem_conjSub hz₀Z
  have hZ8t : Y.Zt 8 = ⊥ := Zt_eq_bot_of_even Y hZ (i := 8) ⟨4, by norm_num⟩
  have hZ8' : (Y.shift 8).Zt 0 = ⊥ := by
    simpa [Setup.Zt, zero_add] using hZ8t
  have hcent8 : Y.Z 8 ≤ Subgroup.centralizer (Y.Gi 8 : Set G) := by
    have h := Z_zero_le_centralizer_Gi_zero (Y.shift 8) (H.shift_two 4) hZ8'
    simpa [Setup.shift_Z, Setup.shift_Gi] using h
  have hb5 : b • Y.vert 5 = Y.vert 5 := by
    have h1 : (Y.τ ^ (4 : ℤ))⁻¹ • Y.vert 5 = Y.vert (-3) := by
      have e : (Y.τ ^ (4 : ℤ))⁻¹ = Y.τ ^ (-4 : ℤ) := (zpow_neg Y.τ 4).symm
      rw [e, Y.zpow_smul_vert]
      norm_num
    have h2 : z₀ • Y.vert (-3) = Y.vert (-3) :=
      (Y.smul_vert_eq_iff_natAbs_le_three H hZ hz₀Z hz₀ne (-3)).mpr (by norm_num)
    show (Y.τ ^ (4 : ℤ) * z₀ * (Y.τ ^ (4 : ℤ))⁻¹) • Y.vert 5 = Y.vert 5
    calc (Y.τ ^ (4 : ℤ) * z₀ * (Y.τ ^ (4 : ℤ))⁻¹) • Y.vert 5
        = (Y.τ ^ (4 : ℤ)) • (z₀ • ((Y.τ ^ (4 : ℤ))⁻¹ • Y.vert 5)) := by rw [mul_smul, mul_smul]
      _ = (Y.τ ^ (4 : ℤ)) • (z₀ • Y.vert (-3)) := by rw [h1]
      _ = (Y.τ ^ (4 : ℤ)) • Y.vert (-3) := by rw [h2]
      _ = Y.vert 5 := by rw [Y.zpow_smul_vert]; norm_num
  have hb4 : b • Y.vert 4 ≠ Y.vert 4 := by
    have h1 : (Y.τ ^ (4 : ℤ))⁻¹ • Y.vert 4 = Y.vert (-4) := by
      have e : (Y.τ ^ (4 : ℤ))⁻¹ = Y.τ ^ (-4 : ℤ) := (zpow_neg Y.τ 4).symm
      rw [e, Y.zpow_smul_vert]
      norm_num
    have h2 : z₀ • Y.vert (-4) ≠ Y.vert (-4) := by
      intro h
      have h4 := (Y.smul_vert_eq_iff_natAbs_le_three H hZ hz₀Z hz₀ne (-4)).mp h
      norm_num at h4
    intro h
    have hb' : (Y.τ ^ (4 : ℤ))⁻¹ * b = z₀ * (Y.τ ^ (4 : ℤ))⁻¹ := by
      show (Y.τ ^ (4 : ℤ))⁻¹ * (Y.τ ^ (4 : ℤ) * z₀ * (Y.τ ^ (4 : ℤ))⁻¹) = z₀ * (Y.τ ^ (4 : ℤ))⁻¹
      group
    have hcalc : (Y.τ ^ (4 : ℤ))⁻¹ • (b • Y.vert 4) = z₀ • ((Y.τ ^ (4 : ℤ))⁻¹ • Y.vert 4) := by
      calc (Y.τ ^ (4 : ℤ))⁻¹ • (b • Y.vert 4) = ((Y.τ ^ (4 : ℤ))⁻¹ * b) • Y.vert 4 :=
            (mul_smul _ _ _).symm
        _ = (z₀ * (Y.τ ^ (4 : ℤ))⁻¹) • Y.vert 4 := by rw [hb']
        _ = z₀ • ((Y.τ ^ (4 : ℤ))⁻¹ • Y.vert 4) := mul_smul _ _ _
    have hh : z₀ • ((Y.τ ^ (4 : ℤ))⁻¹ • Y.vert 4) = (Y.τ ^ (4 : ℤ))⁻¹ • Y.vert 4 := by
      rw [← hcalc]
      exact congrArg (fun t => (Y.τ ^ (4 : ℤ))⁻¹ • t) h
    rw [h1] at hh
    exact h2 hh
  let β : Arc Γ 2 := Y.line.arc 3 2
  have hβ0 : β.vert 0 = Y.vert 3 := by simp [β, Line.arc]
  have hβ1 : β.vert 1 = Y.vert 4 := by simp [β, Line.arc]
  have hβ2 : β.vert 2 = Y.vert 5 := by simp [β, Line.arc]
  obtain ⟨L, hLβ, hLfix⟩ := Line.exists_of_pair Y.hyp.adj_smul (ℓ := 2) (by norm_num) β
    (a := z₀) (b := b) (by rw [hβ0]; exact hfix3) (by rw [hβ1]; exact hmove4)
    (by rw [hβ2]; exact hb5) (by rw [hβ1]; exact hb4)
  have hKL : ∀ k ∈ Y.K, ∀ i, k • L.vert i = L.vert i := by
    intro k hk i
    refine hLfix k ?_ ?_ ?_ i
    · exact Subgroup.mem_centralizer_iff.mp (hcent hz₀Z) k (Y.K_le_Gi 0 hk)
    · exact Subgroup.mem_centralizer_iff.mp (hcent8 hbZ) k (Y.K_le_Gi 8 hk)
    · intro idx hidx
      have hi3 : β.vert idx = Y.vert (3 + (idx : ℤ)) := by simp [β, Line.arc]
      rw [hi3]
      exact Y.K_fix k hk (3 + idx)
  have hPL : ∀ p ∈ Y.arcStab 0 8, ∀ i, p • L.vert i = L.vert i := by
    intro p hp i
    refine hLfix p ?_ ?_ ?_ i
    · exact Subgroup.mem_centralizer_iff.mp (hcent hz₀Z) p
        (Y.arcStab_le_Gi_left (by norm_num) hp)
    · exact Subgroup.mem_centralizer_iff.mp (hcent8 hbZ) p
        (Y.arcStab_le_Gi_right (by norm_num) hp)
    · intro idx hidx
      have hi3 : β.vert idx = Y.vert (3 + (idx : ℤ)) := by simp [β, Line.arc]
      rw [hi3]
      exact (Fan86.mem_fixSet.mp hp) _ ⟨3 + (idx : ℤ), ⟨by omega, by omega⟩, rfl⟩
  have hmeet : L.vert 0 = Y.vert 3 := by
    simpa using (hLβ 0 (by norm_num)).trans hβ0
  have hle : Y.arcStab 0 8 ≤ Y.K :=
    Y.le_K_of_fixes_line H hZ L hKL hPL (i₀ := 0) (j₀ := 3) hmeet
  exact le_antisymm hle (Y.K_le_GT.trans (Y.GT_le_arcStab 0 8))

private theorem arcStab_eight_eq_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {a : ℤ} (ha : Even a) : Y.arcStab a (a + 8) = Y.K := by
  obtain ⟨m, hm⟩ := ha
  have h2m : a = 2 * m := by rw [hm]; ring
  rw [h2m]
  have hZt : Y.Zt (2 * m) = ⊥ := Zt_eq_bot_of_even Y hZ (i := 2 * m) ⟨m, by ring⟩
  have hZ' : (Y.shift (2 * m)).Zt 0 = ⊥ := by
    simpa [Setup.Zt, zero_add] using hZt
  have hcore := arcStab_eight_eq_K_zero (Y.shift (2 * m)) (H.shift_two m) hZ'
  rw [Setup.shift_arcStab, Setup.shift_K] at hcore
  simpa [add_comm] using hcore

theorem not_rightTransAt_of_eight_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {a : ℤ} {k : ℕ} (hk : 8 ≤ k) (hk' : Even a ∨ 9 ≤ k) :
    ¬ Y.RightTransAt a (a + (k : ℤ)) := by
  intro hR
  have hex : ∃ e : ℤ, Even e ∧ a ≤ e ∧ e + 8 ≤ a + (k : ℤ) := by
    by_cases ha : Even a
    · exact ⟨a, ha, le_rfl, by push_cast; omega⟩
    · have h9 : 9 ≤ k := by
        rcases hk' with h | h
        · exact absurd h ha
        · exact h
      have haodd : Odd a := Int.not_even_iff_odd.mp ha
      obtain ⟨m, hm⟩ := haodd
      exact ⟨a + 1, ⟨m + 1, by rw [hm]; ring⟩, by omega, by push_cast; omega⟩
  obtain ⟨e, he, hae, he8⟩ := hex
  have hK : Y.arcStab a (a + (k : ℤ)) ≤ Y.K :=
    (Y.arcStab_anti hae he8).trans (le_of_eq (Y.arcStab_eight_eq_K H hZ he))
  have hne : Y.vert (a + (k : ℤ) + 1) ≠ Y.vert (a + (k : ℤ) - 1) := by
    intro h
    have h' := Y.vert_injective h
    omega
  obtain ⟨x, hxadj, hx1, hx2⟩ := exists_adj_ne_ne (a := Y.vert (a + (k : ℤ) - 1))
    (b := Y.vert (a + (k : ℤ) + 1)) (Y.hyp.three_le_card (Y.vert (a + (k : ℤ))))
  obtain ⟨g, hgP, hgmap⟩ := hR (Y.vert (a + (k : ℤ) + 1)) x
    (Y.adj (a + (k : ℤ))) hne hxadj hx1
  have hgK : g ∈ Y.K := hK hgP
  have hfix := Y.K_fix g hgK (a + (k : ℤ) + 1)
  rw [hfix] at hgmap
  exact hx2 hgmap.symm

end Setup

end CFSG.Quasithin.St84
