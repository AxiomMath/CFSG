module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Set

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem move_end {ℓ : Line Γ} {N m : ℕ} (hs : ¬ LineSingLe Γ G ℓ N) (a : ℤ) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) {w : V} (hw : Γ.Adj (ℓ.vert (a + m)) w) (hwp : w ≠ ℓ.vert (a + m - 1)) :
    ∃ X : G, (∀ j : ℕ, j ≤ m → X • ℓ.vert (a + j) = ℓ.vert (a + j)) ∧ X • w ≠ w := by
  by_contra hcon
  push Not at hcon
  refine hs ⟨m, a, hm1, hmN, Or.inl ⟨w, ?_, ?_, ?_⟩⟩
  · simpa [Line.arc] using hw
  · have e : (ℓ.arc a m).vert (m - 1) = ℓ.vert (a + m - 1) := by
      simp only [Line.arc]
      congr 1
      push_cast [Nat.cast_sub hm1]
      ring
    rw [e]
    exact hwp
  · intro g hg
    refine hcon g fun j hj => ?_
    have := mem_stabRange.1 hg j (Nat.zero_le _) hj
    simpa [Line.arc] using this

namespace B2Set

theorem zA5_fix4 (S : B2Set F L T a) : zA L T a 5 • xv T a 4 = xv T a 4 :=
  (S.zA_fix_iff 5 4).2 ⟨by norm_num, by norm_num⟩

theorem adj_y3 (S : B2Set F L T a) : Γ.Adj (xv T a 4) (zA L T a 5 • xv T a 3) := by
  have := (F.adj_smul (zA L T a 5) (xv T a 3) (xv T a 4)).2 (xv_adj_of T a (by norm_num))
  rw [S.zA5_fix4] at this
  exact this.symm

theorem y3_ne (S : B2Set F L T a) : zA L T a 5 • xv T a 3 ≠ xv T a 3 := fun h => by
  have := ((S.zA_fix_iff 5 3).1 h).1
  norm_num at this

theorem orbit_elt (S : B2Set F L T a) (hn : nOrb T a = 4) {w : V}
    (hw : Γ.Adj (xv T a 4) w) (hw3 : w ≠ xv T a 3) :
    ∃ g ∈ T.subFixer (a + 2) (a + 5), w = g • xv T a 5 := by
  have hsub : {w : V | ∃ g ∈ T.subFixer (a + 2) (a + 5), w = g • xv T a 5} ⊆
      {w : V | Γ.Adj (xv T a 4) w ∧ w ≠ xv T a 3} := by
    rintro _ ⟨g, hg, rfl⟩
    have hgi : ∀ i : ℤ, 1 ≤ i → i ≤ 4 → g • xv T a i = xv T a i := fun i h1 h2 =>
      (T.mem_subFixer.1 hg) (a + 1 + i) (by omega) (by omega)
    refine ⟨?_, fun h => ?_⟩
    · have := (F.adj_smul g (xv T a 4) (xv T a 5)).2 (xv_adj_of T a (by norm_num))
      rwa [hgi 4 (by norm_num) (by norm_num)] at this
    · rw [← hgi 3 (by norm_num) (by norm_num)] at h
      exact xv_ne_of T a (by norm_num : (5 : ℤ) = 3 + 2) (MulAction.injective g h).symm
  have hv4 : valence Γ (xv T a 4) = 5 := by simpa using S.val_even 2
  have hfin : {w : V | Γ.Adj (xv T a 4) w ∧ w ≠ xv T a 3}.Finite :=
    (F.ncard_neighborSet_le (xv T a 4)).2.subset fun w hw => hw.1
  have hN : {w : V | Γ.Adj (xv T a 4) w ∧ w ≠ xv T a 3} =
      Γ.neighborSet (xv T a 4) \ {xv T a 3} := by
    ext w
    simp
  have hcard : {w : V | Γ.Adj (xv T a 4) w ∧ w ≠ xv T a 3}.ncard = 4 := by
    have hmem : xv T a 3 ∈ Γ.neighborSet (xv T a 4) :=
      (xv_adj_of T a (by norm_num : (4 : ℤ) = 3 + 1)).symm
    rw [hN, Set.ncard_sdiff_singleton_of_mem hmem]
    have : (Γ.neighborSet (xv T a 4)).ncard = 5 := by
      rw [← Nat.card_coe_set_eq]
      exact hv4
    omega
  have hEq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact hn.ge) hfin
  have hmem : w ∈ {w : V | Γ.Adj (xv T a 4) w ∧ w ≠ xv T a 3} := ⟨hw, hw3⟩
  rw [← hEq] at hmem
  exact hmem

theorem exists_arc_elt (S : B2Set F L T a) (hn : nOrb T a = 4) :
    ∃ g : G, g • xv T a 1 = xv T a 1 ∧ g • xv T a 2 = xv T a 2 ∧ g • xv T a 3 = xv T a 3 ∧
      g • xv T a 4 = xv T a 4 ∧ g • xv T a 5 = zA L T a 5 • xv T a 3 ∧
      g • xv T a 6 = zA L T a 5 • xv T a 2 := by
  obtain ⟨g₀, hg₀, hg₀5⟩ := S.orbit_elt hn S.adj_y3 S.y3_ne
  have hg₀i : ∀ i : ℤ, 1 ≤ i → i ≤ 4 → g₀ • xv T a i = xv T a i := fun i h1 h2 =>
    (T.mem_subFixer.1 hg₀) (a + 1 + i) (by omega) (by omega)
  have hw : Γ.Adj (T.line.vert (a + 2 + ((4 : ℕ) : ℤ))) (xv T a 6) := by
    have e : T.line.vert (a + 2 + ((4 : ℕ) : ℤ)) = xv T a 5 := by
      show _ = T.line.vert (a + 1 + 5)
      congr 1
      push_cast
      ring
    rw [e]
    exact xv_adj_of T a (by norm_num)
  have hwp : xv T a 6 ≠ T.line.vert (a + 2 + ((4 : ℕ) : ℤ) - 1) := by
    have e : T.line.vert (a + 2 + ((4 : ℕ) : ℤ) - 1) = xv T a 4 := by
      show _ = T.line.vert (a + 1 + 4)
      congr 1
      push_cast
      ring
    rw [e]
    exact (xv_ne_of T a (by norm_num)).symm
  obtain ⟨X, hX, hXmove⟩ := move_end (N := 4) (m := 4) S.hn4 (a + 2) (by norm_num) le_rfl hw hwp
  have hXi : ∀ i : ℤ, 1 ≤ i → i ≤ 5 → X • xv T a i = xv T a i := by
    intro i h1 h2
    have := hX (i - 1).toNat (by omega)
    have e : a + 2 + (((i - 1).toNat : ℕ) : ℤ) = a + 1 + i := by omega
    rw [e] at this
    exact this
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : G, k₀ = g₀ * X * g₀⁻¹ := ⟨_, rfl⟩
  have hk₀i : ∀ i : ℤ, 1 ≤ i → i ≤ 4 → k₀ • xv T a i = xv T a i := by
    intro i h1 h2
    rw [hk₀, mul_smul, mul_smul, inv_smul_eq_iff.2 (hg₀i i h1 h2).symm, hXi i h1 (by omega),
      hg₀i i h1 h2]
  have hk₀y3 : k₀ • (zA L T a 5 • xv T a 3) = zA L T a 5 • xv T a 3 := by
    rw [hg₀5, hk₀, mul_smul, mul_smul, inv_smul_smul, hXi 5 (by norm_num) le_rfl]
  have hk₀move : k₀ • (g₀ • xv T a 6) ≠ g₀ • xv T a 6 := by
    intro h
    apply hXmove
    rw [hk₀, mul_smul, mul_smul, inv_smul_smul] at h
    exact MulAction.injective g₀ h
  have hu_adj : Γ.Adj (zA L T a 5 • xv T a 3) (g₀ • xv T a 6) := by
    rw [hg₀5]
    exact (F.adj_smul g₀ _ _).2 (xv_adj_of T a (by norm_num))
  by_cases hu : g₀ • xv T a 6 = zA L T a 5 • xv T a 2
  · exact ⟨g₀, hg₀i 1 le_rfl (by norm_num), hg₀i 2 (by norm_num) (by norm_num),
      hg₀i 3 (by norm_num) (by norm_num), hg₀i 4 (by norm_num) le_rfl, hg₀5.symm, hu⟩
  · have hy2ne : zA L T a 5 • xv T a 2 ≠ xv T a 4 := fun h => by
      have h' : zA L T a 5 • xv T a 2 = zA L T a 5 • xv T a 4 := h.trans S.zA5_fix4.symm
      exact xv_ne_of T a (by norm_num : (4 : ℤ) = 2 + 2) (MulAction.injective _ h')
    have hy32 : Γ.Adj (zA L T a 5 • xv T a 3) (zA L T a 5 • xv T a 2) :=
      (F.adj_smul _ _ _).2 (xv_adj_of T a (by norm_num : (3 : ℤ) = 2 + 1)).symm
    have hv4 : valence Γ (xv T a 4) = 5 := by simpa using S.val_even 2
    obtain ⟨l', -, -, hset⟩ := P62.exists_sibling F hv4
      (show P62.Br Γ (xv T a 4) (zA L T a 5 • xv T a 3) (zA L T a 5 • xv T a 2) from
        ⟨S.adj_y3, hy32, hy2ne⟩)
    have hu4 : g₀ • xv T a 6 ≠ xv T a 4 := fun h => by
      rw [← hg₀i 4 (by norm_num) le_rfl] at h
      exact xv_ne_of T a (by norm_num : (6 : ℤ) = 4 + 2) (MulAction.injective g₀ h).symm
    have hul : g₀ • xv T a 6 = l' := by
      have hmem : g₀ • xv T a 6 ∈ Γ.neighborSet (zA L T a 5 • xv T a 3) := hu_adj
      rw [hset] at hmem
      rcases hmem with h | h | h
      · exact absurd h hu4
      · exact absurd h hu
      · exact h
    have hv_adj : Γ.Adj (zA L T a 5 • xv T a 3) (k₀ • g₀ • xv T a 6) := by
      have := (F.adj_smul k₀ _ _).2 hu_adj
      rwa [hk₀y3] at this
    have hv4' : k₀ • g₀ • xv T a 6 ≠ xv T a 4 := fun h => by
      rw [← hk₀i 4 (by norm_num) le_rfl] at h
      exact hu4 (MulAction.injective k₀ h)
    have hvy : k₀ • g₀ • xv T a 6 = zA L T a 5 • xv T a 2 := by
      have hmem : k₀ • g₀ • xv T a 6 ∈ Γ.neighborSet (zA L T a 5 • xv T a 3) := hv_adj
      rw [hset] at hmem
      rcases hmem with h | h | h
      · exact absurd h hv4'
      · exact h
      · exact absurd (h.trans hul.symm) hk₀move
    refine ⟨k₀ * g₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mul_smul, hg₀i 1 le_rfl (by norm_num), hk₀i 1 le_rfl (by norm_num)]
    · rw [mul_smul, hg₀i 2 (by norm_num) (by norm_num), hk₀i 2 (by norm_num) (by norm_num)]
    · rw [mul_smul, hg₀i 3 (by norm_num) (by norm_num), hk₀i 3 (by norm_num) (by norm_num)]
    · rw [mul_smul, hg₀i 4 (by norm_num) le_rfl, hk₀i 4 (by norm_num) le_rfl]
    · rw [mul_smul, ← hg₀5, hk₀y3]
    · rw [mul_smul]
      exact hvy

end B2Set

end P518

end CFSG.Quasithin.Fan86
