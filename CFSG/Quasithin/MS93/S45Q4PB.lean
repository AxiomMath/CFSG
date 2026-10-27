module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S45Path
public import CFSG.Quasithin.MS93.Sec2Basic

public section

namespace CFSG.Quasithin.MS93.S45Q4

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45 CFSG.Quasithin.Fan86.Univ
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Path

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem isNBPath_smul {p : ℕ → Vtx X} {N : ℕ} (hp : IsNBPath X p N) (g : X.Universal) :
    IsNBPath X (fun i => g • p i) N :=
  ⟨fun i hi => (adj_smul X g _ _).mpr (hp.adj i hi),
    fun i hi heq => hp.nb i hi (smul_left_cancel g heq)⟩

theorem isNBPath_shift {p : ℕ → Vtx X} {N : ℕ} (hp : IsNBPath X p N) (a : ℕ) :
    IsNBPath X (fun i => p (a + i)) (N - a) :=
  ⟨fun i hi => by simpa [Nat.add_assoc] using hp.adj (a + i) (by omega),
    fun i hi => by simpa [Nat.add_assoc] using hp.nb (a + i) (by omega)⟩

theorem isNBPath_bend {u w : ℕ → Vtx X} {m n : ℕ} (hu : IsNBPath X u m) (hw : IsNBPath X w n)
    (h0 : u 0 = w 0) (h1 : 0 < m → 0 < n → u 1 ≠ w 1) :
    IsNBPath X (fun j => if j ≤ m then u (m - j) else w (j - m)) (m + n) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · show X.treeGraph.Adj (if j ≤ m then u (m - j) else w (j - m))
      (if j + 1 ≤ m then u (m - (j + 1)) else w (j + 1 - m))
    rcases (show j + 1 ≤ m ∨ j = m ∨ m < j by omega) with hjm | hjm | hjm
    · have e1 : j ≤ m := by omega
      simp only [e1, hjm, ↓reduceIte]
      have := hu.adj (m - (j + 1)) (by omega)
      rw [show m - (j + 1) + 1 = m - j by omega] at this
      exact this.symm
    · have e1 : j ≤ m := by omega
      have e2 : ¬ j + 1 ≤ m := by omega
      simp only [e1, e2, ↓reduceIte]
      rw [show m - j = 0 by omega, h0, show j + 1 - m = 0 + 1 by omega]
      exact hw.adj 0 (by omega)
    · have e1 : ¬ j ≤ m := by omega
      have e2 : ¬ j + 1 ≤ m := by omega
      simp only [e1, e2, ↓reduceIte]
      have := hw.adj (j - m) (by omega)
      rwa [show j - m + 1 = j + 1 - m by omega] at this
  · show (if j + 2 ≤ m then u (m - (j + 2)) else w (j + 2 - m)) ≠
      (if j ≤ m then u (m - j) else w (j - m))
    rcases (show j + 2 ≤ m ∨ j + 1 = m ∨ j = m ∨ m < j by omega) with hj | hj | hj | hj
    · have e1 : j ≤ m := by omega
      simp only [e1, hj, ↓reduceIte]
      have := hu.nb (m - (j + 2)) (by omega)
      rw [show m - (j + 2) + 2 = m - j by omega] at this
      exact this.symm
    · have e1 : j ≤ m := by omega
      have e2 : ¬ j + 2 ≤ m := by omega
      simp only [e1, e2, ↓reduceIte]
      rw [show m - j = 1 by omega, show j + 2 - m = 1 by omega]
      exact (h1 (by omega) (by omega)).symm
    · have e1 : j ≤ m := by omega
      have e2 : ¬ j + 2 ≤ m := by omega
      simp only [e1, e2, ↓reduceIte]
      rw [show m - j = 0 by omega, h0, show j + 2 - m = 0 + 2 by omega]
      exact hw.nb 0 (by omega)
    · have e1 : ¬ j ≤ m := by omega
      have e2 : ¬ j + 2 ≤ m := by omega
      simp only [e1, e2, ↓reduceIte]
      have := hw.nb (j - m) (by omega)
      rwa [show j - m + 2 = j + 2 - m by omega] at this

structure Bend (q : ℕ → Vtx X) (g : X.Universal) : Prop where
  d8 : X.treeGraph.dist (g • q 4) (q 4) = 8
  d_g4_2 : X.treeGraph.dist (g • q 4) (q 2) = 6
  d_g2_4 : X.treeGraph.dist (g • q 2) (q 4) = 6
  d_g1_4 : X.treeGraph.dist (g • q 1) (q 4) = 5
  d_g2_2 : X.treeGraph.dist (g • q 2) (q 2) = 4
  d_1_g2 : X.treeGraph.dist (q 1) (g • q 2) = 3
  d_g1_2 : X.treeGraph.dist (g • q 1) (q 2) = 3
  d_2_g3 : X.treeGraph.dist (q 2) (g • q 3) = 5
  geo0 : geo X (g • q 4) (q 4) 0 = g • q 4
  geo2 : geo X (g • q 4) (q 4) 2 = g • q 2
  geo4 : geo X (g • q 4) (q 4) 4 = q 0
  geo6 : geo X (g • q 4) (q 4) 6 = q 2
  geo8 : geo X (g • q 4) (q 4) 8 = q 4
  geo'0 : geo X (q 4) (g • q 4) 0 = q 4
  geo'1 : geo X (q 4) (g • q 4) 1 = q 3
  geo'2 : geo X (q 4) (g • q 4) 2 = q 2
  geo'4 : geo X (q 4) (g • q 4) 4 = q 0
  geo'6 : geo X (q 4) (g • q 4) 6 = g • q 2
  geo'8 : geo X (q 4) (g • q 4) 8 = g • q 4

theorem bend_of {q : ℕ → Vtx X} (hq : IsNBPath X q 4) {g : X.Universal} (hgα : g • q 0 = q 0)
    (h11 : g • q 1 ≠ q 1) : Bend q g := by
  have hu : IsNBPath X (fun i => g • q i) 4 := isNBPath_smul hq g
  obtain ⟨w, hwdef⟩ : ∃ w : ℕ → Vtx X,
      w = fun j => if j ≤ 4 then g • q (4 - j) else q (j - 4) := ⟨_, rfl⟩
  have hw : IsNBPath X w 8 := by
    rw [hwdef]; exact isNBPath_bend hu hq hgα (fun _ _ => h11)
  have hw0 : w 0 = g • q 4 := by simp [hwdef]
  have hw1 : w 1 = g • q 3 := by simp [hwdef]
  have hw2 : w 2 = g • q 2 := by simp [hwdef]
  have hw3 : w 3 = g • q 1 := by simp [hwdef]
  have hw4 : w 4 = q 0 := by simp [hwdef, hgα]
  have hw5 : w 5 = q 1 := by simp [hwdef]
  have hw6 : w 6 = q 2 := by simp [hwdef]
  have hw7 : w 7 = q 3 := by simp [hwdef]
  have hw8 : w 8 = q 4 := by simp [hwdef]
  have hD : ∀ i j, i ≤ j → j ≤ 8 → X.treeGraph.dist (w i) (w j) = j - i :=
    fun i j hij hj => hw.dist_eq' hij hj
  have hgeo : ∀ k, k ≤ 8 → geo X (w 0) (w 8) k = w k := fun k hk => by
    have := hw.eq_geo (i := 0) (j := 8) (k := k) (Nat.zero_le k) hk le_rfl
    rw [Nat.sub_zero] at this
    exact this.symm
  have hgeo' : ∀ k, k ≤ 8 → geo X (w 8) (w 0) k = w (8 - k) := fun k hk => by
    have := hw.eq_geo_rev (i := 0) (j := 8) (k := 8 - k) (by omega) (by omega) le_rfl
    rw [show 8 - (8 - k) = k by omega] at this
    exact this.symm
  rw [hw0, hw8] at hgeo hgeo'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hw0, ← hw8]; exact hD 0 8 (by omega) le_rfl
  · rw [← hw0, ← hw6]; exact hD 0 6 (by omega) (by omega)
  · rw [← hw2, ← hw8]; exact hD 2 8 (by omega) le_rfl
  · rw [← hw3, ← hw8]; exact hD 3 8 (by omega) le_rfl
  · rw [← hw2, ← hw6]; exact hD 2 6 (by omega) (by omega)
  · rw [tdist_comm, ← hw2, ← hw5]; exact hD 2 5 (by omega) (by omega)
  · rw [← hw3, ← hw6]; exact hD 3 6 (by omega) (by omega)
  · rw [tdist_comm, ← hw1, ← hw6]; exact hD 1 6 (by omega) (by omega)
  · rw [hgeo 0 (by omega), hw0]
  · rw [hgeo 2 (by omega), hw2]
  · rw [hgeo 4 (by omega), hw4]
  · rw [hgeo 6 (by omega), hw6]
  · rw [hgeo 8 le_rfl, hw8]
  · rw [hgeo' 0 (by omega), hw8]
  · rw [hgeo' 1 (by omega), hw7]
  · rw [hgeo' 2 (by omega), hw6]
  · rw [hgeo' 4 (by omega), hw4]
  · rw [hgeo' 6 (by omega), hw2]
  · rw [hgeo' 8 le_rfl, hw0]

theorem isStraight_of_bend {q : ℕ → Vtx X} {g : X.Universal} (hB : Bend q g)
    (hg : g ∈ stab X (q 0)) {k : X.Universal} (hk : k ∈ stab X (q 2)) (hkq : k • q 4 = q 0) :
    IsStraight X (g • q 4) (q 4) ∧ IsStraight X (q 4) (g • q 4) := by
  have hgα : g • q 0 = q 0 := (mem_stab _).mp hg
  have hgα' : g⁻¹ • q 0 = q 0 := by rw [inv_smul_eq_iff, hgα]
  have hk2 : k • q 2 = q 2 := (mem_stab _).mp hk
  have hk2' : k⁻¹ • q 2 = q 2 := by rw [inv_smul_eq_iff, hk2]
  have hk0 : k⁻¹ • q 0 = q 4 := by rw [← hkq, inv_smul_smul]
  constructor
  · intro i hi hi8
    rw [hB.d8] at hi8
    rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
    · show ∃ x ∈ stab X (geo X (g • q 4) (q 4) 2), x • geo X (g • q 4) (q 4) 4 =
        geo X (g • q 4) (q 4) 0
      rw [hB.geo2, hB.geo4, hB.geo0]
      refine ⟨g * k⁻¹ * g⁻¹, ?_, ?_⟩
      · rw [mem_stab, mul_smul, mul_smul, inv_smul_smul, hk2']
      · rw [mul_smul, mul_smul, hgα', hk0]
    · show ∃ x ∈ stab X (geo X (g • q 4) (q 4) 4), x • geo X (g • q 4) (q 4) 6 =
        geo X (g • q 4) (q 4) 2
      rw [hB.geo4, hB.geo6, hB.geo2]
      exact ⟨g, hg, rfl⟩
    · show ∃ x ∈ stab X (geo X (g • q 4) (q 4) 6), x • geo X (g • q 4) (q 4) 8 =
        geo X (g • q 4) (q 4) 4
      rw [hB.geo6, hB.geo8, hB.geo4]
      exact ⟨k, hk, hkq⟩
  · intro i hi hi8
    rw [tdist_comm, hB.d8] at hi8
    rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
    · show ∃ x ∈ stab X (geo X (q 4) (g • q 4) 2), x • geo X (q 4) (g • q 4) 4 =
        geo X (q 4) (g • q 4) 0
      rw [hB.geo'2, hB.geo'4, hB.geo'0]
      exact ⟨k⁻¹, inv_mem hk, hk0⟩
    · show ∃ x ∈ stab X (geo X (q 4) (g • q 4) 4), x • geo X (q 4) (g • q 4) 6 =
        geo X (q 4) (g • q 4) 2
      rw [hB.geo'4, hB.geo'6, hB.geo'2]
      exact ⟨g⁻¹, inv_mem hg, inv_smul_smul g _⟩
    · show ∃ x ∈ stab X (geo X (q 4) (g • q 4) 6), x • geo X (q 4) (g • q 4) 8 =
        geo X (q 4) (g • q 4) 4
      rw [hB.geo'6, hB.geo'8, hB.geo'4]
      refine ⟨g * k * g⁻¹, ?_, ?_⟩
      · rw [mem_stab, mul_smul, mul_smul, inv_smul_smul, hk2]
      · rw [mul_smul, mul_smul, inv_smul_smul, hkq, hgα]

end Path

theorem mem_normalizer_of_map_conj_eq {Γ : Type*} [Group Γ] {K : Subgroup Γ} {g : Γ}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    rwa [← this]

end CFSG.Quasithin.MS93.S45Q4
