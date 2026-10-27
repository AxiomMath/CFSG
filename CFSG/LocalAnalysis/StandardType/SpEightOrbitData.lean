module

public import CFSG.LocalAnalysis.StandardType.SpEightCentralizers
public import CFSG.LocalAnalysis.StandardType.SpEightOrthogonalGeneration

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

@[expose] def vecOf (l : List ℕ) : Vec := fun i => ((l.getD (idx i) 0 : ℕ) : ZMod 2)

@[expose] def u0 : Vec := vecOf [0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def genCenters : List (List ℕ × List ℕ) :=
  [([0, 1, 0, 1, 0, 1, 1, 0], [1, 1, 0, 1, 1, 0, 0, 0]),
    ([0, 1, 0, 0, 1, 1, 1, 0], [1, 0, 0, 0, 1, 0, 0, 1]),
    ([0, 1, 0, 1, 1, 1, 1, 0], [1, 1, 1, 1, 0, 1, 1, 1]),
    ([0, 0, 0, 1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 0, 1, 0]),
    ([0, 0, 1, 1, 1, 1, 1, 0], [1, 1, 1, 0, 0, 0, 1, 1]),
    ([0, 0, 1, 0, 0, 1, 1, 1], [1, 0, 0, 1, 0, 0, 0, 1]),
    ([0, 0, 0, 1, 1, 1, 0, 1], [1, 1, 1, 1, 0, 0, 1, 0]),
    ([0, 1, 0, 1, 1, 1, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0]),
    ([0, 0, 1, 0, 0, 1, 1, 1], [1, 0, 1, 1, 0, 1, 1, 0])
  ]

@[expose] def genCommutes : List (ℕ × ℕ) :=
  [(0, 1), (1, 0), (1, 0), (1, 2), (1, 2), (1, 2), (1, 2), (1, 0), (1, 2)]

@[expose] def genGL (k : ℕ) : GL Idx (ZMod 2) :=
  tvGL (vecOf (genCenters.getD k ([], [])).1) * tvGL (vecOf (genCenters.getD k ([], [])).2)

@[expose] def applyGen (k : ℕ) (v : Vec) : Vec :=
  let c := vecOf (genCenters.getD k ([], [])).1
  let c' := vecOf (genCenters.getD k ([], [])).2
  let v' := v + omega v c' • c'
  v' + omega v' c • c

@[expose] def orbitWords : List (List ℕ × List ℕ) :=
  [([0, 0, 0, 1, 0, 0, 0, 1], []),
    ([0, 0, 0, 1, 0, 0, 1, 1], [2, 7]),
    ([0, 0, 0, 1, 0, 1, 0, 1], [8, 3]),
    ([0, 0, 0, 1, 0, 1, 1, 1], [3, 6, 1]),
    ([0, 0, 0, 1, 1, 0, 0, 1], [0, 0, 2]),
    ([0, 0, 0, 1, 1, 0, 1, 1], [0, 7, 0]),
    ([0, 0, 0, 1, 1, 1, 0, 1], [4, 6, 6]),
    ([0, 0, 0, 1, 1, 1, 1, 1], [2, 3, 2]),
    ([0, 0, 1, 0, 0, 0, 1, 0], [1, 7, 7]),
    ([0, 0, 1, 0, 0, 0, 1, 1], [5, 3]),
    ([0, 0, 1, 0, 0, 1, 1, 0], [6, 0]),
    ([0, 0, 1, 0, 0, 1, 1, 1], [3, 5]),
    ([0, 0, 1, 0, 1, 0, 1, 0], [0, 4]),
    ([0, 0, 1, 0, 1, 0, 1, 1], [5, 6, 6]),
    ([0, 0, 1, 0, 1, 1, 1, 0], [8, 1]),
    ([0, 0, 1, 0, 1, 1, 1, 1], [4, 4]),
    ([0, 0, 1, 1, 0, 0, 0, 1], [0, 8, 1]),
    ([0, 0, 1, 1, 0, 0, 1, 0], [0, 7, 3]),
    ([0, 0, 1, 1, 0, 1, 0, 1], [1, 4]),
    ([0, 0, 1, 1, 0, 1, 1, 0], [5]),
    ([0, 0, 1, 1, 1, 0, 0, 1], [6, 1]),
    ([0, 0, 1, 1, 1, 0, 1, 0], [3, 5, 6]),
    ([0, 0, 1, 1, 1, 1, 0, 1], [0, 7, 7]),
    ([0, 0, 1, 1, 1, 1, 1, 0], [0, 2]),
    ([0, 1, 0, 0, 0, 1, 0, 0], [4, 5]),
    ([0, 1, 0, 0, 0, 1, 0, 1], [0, 6, 8]),
    ([0, 1, 0, 0, 0, 1, 1, 0], [0, 5, 7]),
    ([0, 1, 0, 0, 0, 1, 1, 1], [0, 0]),
    ([0, 1, 0, 0, 1, 1, 0, 0], [3, 3, 6]),
    ([0, 1, 0, 0, 1, 1, 0, 1], [7]),
    ([0, 1, 0, 0, 1, 1, 1, 0], [3, 1, 8]),
    ([0, 1, 0, 0, 1, 1, 1, 1], [2]),
    ([0, 1, 0, 1, 0, 0, 0, 1], [4, 5, 3]),
    ([0, 1, 0, 1, 0, 0, 1, 1], [4, 1, 6]),
    ([0, 1, 0, 1, 0, 1, 0, 0], [3, 3, 2]),
    ([0, 1, 0, 1, 0, 1, 1, 0], [6, 7]),
    ([0, 1, 0, 1, 1, 0, 0, 1], [3, 6]),
    ([0, 1, 0, 1, 1, 0, 1, 1], [2, 4, 2]),
    ([0, 1, 0, 1, 1, 1, 0, 0], [0, 5, 3]),
    ([0, 1, 0, 1, 1, 1, 1, 0], [2, 3, 5]),
    ([0, 1, 1, 0, 0, 0, 1, 0], [0, 2, 7]),
    ([0, 1, 1, 0, 0, 0, 1, 1], [4, 8]),
    ([0, 1, 1, 0, 0, 1, 0, 0], [1, 3, 3]),
    ([0, 1, 1, 0, 0, 1, 0, 1], [2, 0, 6]),
    ([0, 1, 1, 0, 1, 0, 1, 0], [7, 5]),
    ([0, 1, 1, 0, 1, 0, 1, 1], [1, 2, 4]),
    ([0, 1, 1, 0, 1, 1, 0, 0], [1, 3, 6]),
    ([0, 1, 1, 0, 1, 1, 0, 1], [5, 3, 1]),
    ([0, 1, 1, 1, 0, 0, 0, 1], [1, 3]),
    ([0, 1, 1, 1, 0, 0, 1, 0], [5, 6, 8]),
    ([0, 1, 1, 1, 0, 1, 0, 0], [2, 0, 4]),
    ([0, 1, 1, 1, 0, 1, 1, 1], [1, 1, 6]),
    ([0, 1, 1, 1, 1, 0, 0, 1], [0, 0, 4]),
    ([0, 1, 1, 1, 1, 0, 1, 0], [8, 4]),
    ([0, 1, 1, 1, 1, 1, 0, 0], [4, 0]),
    ([0, 1, 1, 1, 1, 1, 1, 1], [0, 8]),
    ([1, 0, 0, 0, 1, 0, 0, 0], [1, 2]),
    ([1, 0, 0, 0, 1, 0, 0, 1], [7, 5, 4]),
    ([1, 0, 0, 0, 1, 0, 1, 0], [1, 7]),
    ([1, 0, 0, 0, 1, 0, 1, 1], [2, 4, 8]),
    ([1, 0, 0, 0, 1, 1, 0, 0], [0, 2, 3]),
    ([1, 0, 0, 0, 1, 1, 0, 1], [0, 4, 3]),
    ([1, 0, 0, 0, 1, 1, 1, 0], [6, 0, 7]),
    ([1, 0, 0, 0, 1, 1, 1, 1], [6, 0, 2]),
    ([1, 0, 0, 1, 0, 0, 0, 1], [3, 8]),
    ([1, 0, 0, 1, 0, 0, 1, 1], [4, 0, 6]),
    ([1, 0, 0, 1, 0, 1, 0, 1], [0, 7]),
    ([1, 0, 0, 1, 0, 1, 1, 1], [2, 0]),
    ([1, 0, 0, 1, 1, 0, 0, 0], [1, 1]),
    ([1, 0, 0, 1, 1, 0, 1, 0], [0, 6, 1]),
    ([1, 0, 0, 1, 1, 1, 0, 0], [0, 4, 5]),
    ([1, 0, 0, 1, 1, 1, 1, 0], [5, 7]),
    ([1, 0, 1, 0, 0, 0, 1, 0], [7, 6]),
    ([1, 0, 1, 0, 0, 0, 1, 1], [3, 3]),
    ([1, 0, 1, 0, 0, 1, 1, 0], [1, 1, 4]),
    ([1, 0, 1, 0, 0, 1, 1, 1], [8]),
    ([1, 0, 1, 0, 1, 0, 0, 0], [0, 0, 6]),
    ([1, 0, 1, 0, 1, 0, 0, 1], [1, 3, 0]),
    ([1, 0, 1, 0, 1, 1, 0, 0], [2, 4]),
    ([1, 0, 1, 0, 1, 1, 0, 1], [1, 7, 8]),
    ([1, 0, 1, 1, 0, 0, 0, 1], [4, 6, 2]),
    ([1, 0, 1, 1, 0, 0, 1, 0], [0, 7, 5]),
    ([1, 0, 1, 1, 0, 1, 0, 1], [6, 6, 0]),
    ([1, 0, 1, 1, 0, 1, 1, 0], [3]),
    ([1, 0, 1, 1, 1, 0, 0, 0], [2, 2]),
    ([1, 0, 1, 1, 1, 0, 1, 1], [0, 4, 8]),
    ([1, 0, 1, 1, 1, 1, 0, 0], [4, 1]),
    ([1, 0, 1, 1, 1, 1, 1, 1], [1, 1, 5]),
    ([1, 1, 0, 0, 0, 1, 0, 0], [5, 6]),
    ([1, 1, 0, 0, 0, 1, 0, 1], [0, 4, 6]),
    ([1, 1, 0, 0, 0, 1, 1, 0], [1, 1, 2]),
    ([1, 1, 0, 0, 0, 1, 1, 1], [1, 3, 8]),
    ([1, 1, 0, 0, 1, 0, 0, 0], [3, 6, 8]),
    ([1, 1, 0, 0, 1, 0, 0, 1], [0]),
    ([1, 1, 0, 0, 1, 0, 1, 0], [4, 0, 8]),
    ([1, 1, 0, 0, 1, 0, 1, 1], [1, 6]),
    ([1, 1, 0, 1, 0, 0, 0, 1], [4, 6, 4]),
    ([1, 1, 0, 1, 0, 0, 1, 1], [3, 5, 7]),
    ([1, 1, 0, 1, 0, 1, 0, 0], [0, 6]),
    ([1, 1, 0, 1, 0, 1, 1, 0], [1]),
    ([1, 1, 0, 1, 1, 0, 0, 0], [4, 4, 2]),
    ([1, 1, 0, 1, 1, 0, 1, 0], [1, 4, 6]),
    ([1, 1, 0, 1, 1, 1, 0, 1], [0, 4, 2]),
    ([1, 1, 0, 1, 1, 1, 1, 1], [3, 1, 5]),
    ([1, 1, 1, 0, 0, 0, 1, 0], [2, 4, 1]),
    ([1, 1, 1, 0, 0, 0, 1, 1], [6, 6]),
    ([1, 1, 1, 0, 0, 1, 0, 0], [1, 8, 3]),
    ([1, 1, 1, 0, 0, 1, 0, 1], [7, 7]),
    ([1, 1, 1, 0, 1, 0, 0, 0], [2, 3]),
    ([1, 1, 1, 0, 1, 0, 0, 1], [8, 1, 1]),
    ([1, 1, 1, 0, 1, 1, 1, 0], [0, 5]),
    ([1, 1, 1, 0, 1, 1, 1, 1], [4, 6]),
    ([1, 1, 1, 1, 0, 0, 0, 1], [1, 8]),
    ([1, 1, 1, 1, 0, 0, 1, 0], [4]),
    ([1, 1, 1, 1, 0, 1, 0, 0], [8, 4, 0]),
    ([1, 1, 1, 1, 0, 1, 1, 1], [0, 4, 4]),
    ([1, 1, 1, 1, 1, 0, 0, 0], [3, 1]),
    ([1, 1, 1, 1, 1, 0, 1, 1], [7, 8]),
    ([1, 1, 1, 1, 1, 1, 0, 1], [2, 3, 3]),
    ([1, 1, 1, 1, 1, 1, 1, 0], [6])
  ]

theorem genGL_mem_statedSp (k : ℕ) : genGL k ∈ StatedSp 4 (ZMod 2) := by
  unfold genGL
  exact (StatedSp 4 (ZMod 2)).mul_mem (tvGL_mem_statedSp _) (tvGL_mem_statedSp _)

theorem genGL_mulVec (k : ℕ) (v : Vec) :
    ((genGL k : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ v = applyGen k v := by
  unfold genGL applyGen
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, tvGL_mulVec, tvGL_mulVec]

theorem genCommutes_ne_one :
    ∀ k : Fin 9,
      a2 ^ (genCommutes.getD k.val (0, 0)).1 * b2 ^ (genCommutes.getD k.val (0, 0)).2 ≠ 1 := by
  decide +kernel

theorem genGL_commutes_genCommutes :
    ∀ k : Fin 9,
      genGL k *
          (a2 ^ (genCommutes.getD k.val (0, 0)).1 * b2 ^ (genCommutes.getD k.val (0, 0)).2) =
        (a2 ^ (genCommutes.getD k.val (0, 0)).1 * b2 ^ (genCommutes.getD k.val (0, 0)).2) *
          genGL k := by
  decide +kernel

theorem genGL_mem_D0 (k : Fin 9) : genGL k ∈ D0 E2 := by
  have ha2 : a2 ∈ E2 := Subgroup.subset_closure (by simp [E2])
  have hb2 : b2 ∈ E2 := Subgroup.subset_closure (by simp [E2])
  refine Subgroup.subset_closure ⟨genGL_mem_statedSp k, ?_⟩
  exact ⟨a2 ^ (genCommutes.getD k.val (0, 0)).1 * b2 ^ (genCommutes.getD k.val (0, 0)).2,
    Subgroup.mul_mem _ (Subgroup.pow_mem _ ha2 _) (Subgroup.pow_mem _ hb2 _),
    genCommutes_ne_one k, genGL_commutes_genCommutes k⟩

theorem tvGL_u0_commutes : tvGL u0 * (a2 * b2) = (a2 * b2) * tvGL u0 := by
  decide +kernel

theorem a2b2_ne_one : a2 * b2 ≠ 1 := by
  decide +kernel

theorem tvGL_u0_mem_D0 : tvGL u0 ∈ D0 E2 := by
  have ha2 : a2 ∈ E2 := Subgroup.subset_closure (by simp [E2])
  have hb2 : b2 ∈ E2 := Subgroup.subset_closure (by simp [E2])
  exact Subgroup.subset_closure
    ⟨tvGL_mem_statedSp u0, a2 * b2, Subgroup.mul_mem _ ha2 hb2, a2b2_ne_one, tvGL_u0_commutes⟩

theorem orbit_table_check :
    ∀ p ∈ orbitWords, p.2.foldl (fun v k => applyGen k v) u0 = vecOf p.1 := by
  decide +kernel

theorem orbit_table_cover : ∀ w : Vec, Q0 w = 1 → ∃ p ∈ orbitWords, vecOf p.1 = w := by
  decide +kernel

theorem orbitWords_word_index_lt_nine : ∀ p ∈ orbitWords, ∀ k ∈ p.2, k < 9 := by
  decide +kernel

theorem foldl_applyGen_mem_D0 (word : List ℕ) :
    (∀ k ∈ word, k < 9) → ∀ g ∈ D0 E2, ∃ h ∈ D0 E2,
      ((h : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ u0 =
        word.foldl (fun v k => applyGen k v)
          (((g : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ u0) := by
  induction word with
  | nil => intro _ g hg; exact ⟨g, hg, rfl⟩
  | cons k rest ih =>
      intro hword g hg
      have hk : k < 9 := hword k (by simp)
      have hrest : ∀ k' ∈ rest, k' < 9 := fun k' hk' => hword k' (by simp [hk'])
      have hgk : genGL k * g ∈ D0 E2 := (D0 E2).mul_mem (genGL_mem_D0 ⟨k, hk⟩) hg
      obtain ⟨h, hh, hhval⟩ := ih hrest (genGL k * g) hgk
      refine ⟨h, hh, ?_⟩
      rw [hhval, List.foldl_cons, Units.val_mul, ← Matrix.mulVec_mulVec, genGL_mulVec]

theorem exists_mem_D0_mulVec_eq {w : Vec} (hw : Q0 w = 1) :
    ∃ h ∈ D0 E2, ((h : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ u0 = w := by
  obtain ⟨p, hp, hpw⟩ := orbit_table_cover w hw
  obtain ⟨h, hh, hhval⟩ :=
    foldl_applyGen_mem_D0 p.2 (orbitWords_word_index_lt_nine p hp) 1 (D0 E2).one_mem
  refine ⟨h, hh, ?_⟩
  rw [hhval, show ((1 : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ u0 = u0 by simp]
  exact (orbit_table_check p hp).trans hpw

theorem tvGL_mem_D0 {w : Vec} (hw : Q0 w = 1) : tvGL w ∈ D0 E2 := by
  obtain ⟨h, hh, hhw⟩ := exists_mem_D0_mulVec_eq hw
  have hhSp : h ∈ StatedSp 4 (ZMod 2) :=
    matrixOrthogonal_le_statedSp (D0_E2_le_matrixOrthogonal hh)
  have hconj := mul_tvGL_mul_inv hhSp u0
  rw [hhw] at hconj
  rw [← hconj]
  exact (D0 E2).mul_mem ((D0 E2).mul_mem hh tvGL_u0_mem_D0) ((D0 E2).inv_mem hh)

theorem matrixOrthogonal_le_D0_E2 : matrixOrthogonal Q0 ≤ D0 E2 := by
  rw [matrixOrthogonal_eq_closure_tvGL]
  exact (Subgroup.closure_le _).2 (by
    rintro _ ⟨w, hw, rfl⟩
    exact tvGL_mem_D0 hw)

theorem D0_E2_eq_matrixOrthogonal : D0 E2 = matrixOrthogonal Q0 :=
  le_antisymm D0_E2_le_matrixOrthogonal matrixOrthogonal_le_D0_E2

end CFSG.StandardType.SpEight
